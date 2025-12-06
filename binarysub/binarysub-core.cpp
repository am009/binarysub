
#include "binarysub-core.h"

namespace binarysub {

// compute the max level contained in a type (lazy in paper; direct here)
int level_of(const SimpleType &st) {
  return std::visit(
      [](auto const &n) -> int {
        using T = std::decay_t<decltype(n)>;
        if constexpr (isTPrimitiveType<T>()) {
          return 0;
        } else if constexpr (isVariableStateType<T>()) {
          return n.level;
        } else if constexpr (isTFunctionType<T>()) {
          int m = level_of(n.result);
          for (auto const &arg : n.args)
            m = std::max(m, level_of(arg));
          return m;
        } else if constexpr (isTRecordType<T>()) {
          int m = 0;
          for (auto const &[_, t] : n.fields)
            m = std::max(m, level_of(t));
          return m;
        } else {
          static_assert(!sizeof(T), "Unhandled variant type in level_of");
        }
      },
      st->v);
}

// ======================= Extrusion implementation =====================
SimpleType extrude(const SimpleType &ty, bool pol, int lvl,
                   std::map<PolarVar, std::shared_ptr<VariableState>> &cache,
                   VarSupply &supply) {
  if (level_of(ty) <= lvl)
    return ty;

  if (auto p [[maybe_unused]] = ty->getAsTPrimitive())
    return ty;

  if (auto f = ty->getAsTFunction()) {
    std::vector<SimpleType> newArgs;
    newArgs.reserve(f->args.size());
    for (auto const &a : f->args)
      newArgs.push_back(extrude(a, !pol, lvl, cache, supply));
    auto r = extrude(f->result, pol, lvl, cache, supply);
    return make_function(std::move(newArgs), std::move(r));
  }

  if (auto r = ty->getAsTRecord()) {
    std::vector<std::pair<std::string, SimpleType>> fs;
    fs.reserve(r->fields.size());
    for (auto const &[n, t] : r->fields) {
      fs.emplace_back(n, extrude(t, pol, lvl, cache, supply));
    }
    return make_record(std::move(fs));
  }

  auto vs = ty->getAsVariableState();
  assert(vs);

  PolarVar key{ty, pol};
  if (auto it = cache.find(key); it != cache.end()) {
    return std::make_shared<TypeNode>(*(it->second));
  }

  // Make a copy at requested level
  auto nvs = std::make_shared<VariableState>(supply.fresh_id(), lvl);
  cache.emplace(key, nvs);

  if (pol) {
    // positive: copy lowers to the new var; old var upper-bounds include the
    // new var
    vs->upperBounds.push_back(std::make_shared<TypeNode>(*nvs));
    nvs->lowerBounds.reserve(vs->lowerBounds.size());
    for (auto const &lb : vs->lowerBounds)
      nvs->lowerBounds.push_back(extrude(lb, pol, lvl, cache, supply));
  } else {
    // negative: copy uppers to the new var; old var lower-bounds include the
    // new var
    vs->lowerBounds.push_back(std::make_shared<TypeNode>(*nvs));
    nvs->upperBounds.reserve(vs->upperBounds.size());
    for (auto const &ub : vs->upperBounds)
      nvs->upperBounds.push_back(extrude(ub, pol, lvl, cache, supply));
  }
  return std::make_shared<TypeNode>(*nvs);
}

// ======================= Subtype constraint solver implementation
expected<void, Error> constrain_impl(const SimpleType &lhs,
                                     const SimpleType &rhs, Cache &cache,
                                     VarSupply &supply);

expected<void, Error> constrain(const SimpleType &lhs, const SimpleType &rhs,
                                Cache &cache, VarSupply &supply) {
  auto key = std::make_pair(lhs.get(), rhs.get());
  if (cache.find(key) != cache.end())
    return expected<void, Error>{};
  cache.insert(key);
  return constrain_impl(lhs, rhs, cache, supply);
}

expected<void, Error> constrain_impl(const SimpleType &lhs,
                                     const SimpleType &rhs, Cache &cache,
                                     VarSupply &supply) {
  if (auto lp = lhs->getAsTPrimitive()) {
    if (auto rp = rhs->getAsTPrimitive()) {
      if (lp->name == rp->name)
        return expected<void, Error>{};
      else
        return unexpected<Error>(Error::make("primitive mismatch: " + lp->name +
                                             " </: " + rp->name));
    }
  }

  if (auto lf = lhs->getAsTFunction())
    if (auto rf = rhs->getAsTFunction()) {
      if (lf->args.size() < rf->args.size()) {
        return unexpected<Error>(
            Error::make("function arity mismatch: subtype has fewer params"));
      }
      for (size_t i = 0; i < rf->args.size(); ++i) {
        if (auto e = constrain(rf->args[i], lf->args[i], cache, supply); !e)
          return e;
      }
      if (auto e = constrain(lf->result, rf->result, cache, supply); !e)
        return e;
      return expected<void, Error>{};
    }

  if (auto lr = lhs->getAsTRecord())
    if (auto rr = rhs->getAsTRecord()) {
      std::map<std::string, SimpleType> fmap;
      for (auto const &[n, t] : lr->fields)
        fmap[n] = t;
      for (auto const &[n_req, t_req] : rr->fields) {
        auto it = fmap.find(n_req);
        if (it == fmap.end())
          return unexpected<Error>(Error::make("missing field: " + n_req));
        if (auto e = constrain(it->second, t_req, cache, supply); !e)
          return e;
      }
      return expected<void, Error>{};
    }

  if (auto lv = lhs->getAsVariableState()) {
    // guard: only allow rhs to flow into α if rhs.level <= α.level
    if (level_of(rhs) <= lv->level) {
      lv->upperBounds.push_back(rhs);
      for (auto const &lb : lv->lowerBounds)
        if (auto e = constrain(lb, rhs, cache, supply); !e)
          return e;
      return expected<void, Error>{};
    }
    // else extrude rhs down to lhs.level (negative polarity) and retry
    // make a copy of the problematic type such that the copy has the requested level and soundly approximates the original type.
    std::map<PolarVar, std::shared_ptr<VariableState>> ex;
    auto rhs_ex = extrude(rhs, /*pol=*/false, lv->level, ex, supply);
    return constrain(lhs, rhs_ex, cache, supply);
  }

  if (auto rv = rhs->getAsVariableState()) {
    if (level_of(lhs) <= rv->level) {
      rv->lowerBounds.push_back(lhs);
      for (auto const &ub : rv->upperBounds)
        if (auto e = constrain(lhs, ub, cache, supply); !e)
          return e;
      return expected<void, Error>{};
    }
    // else extrude lhs down to rhs.level (positive polarity) and retry
    std::map<PolarVar, std::shared_ptr<VariableState>> ex;
    auto lhs_ex = extrude(lhs, /*pol=*/true, rv->level, ex, supply);
    return constrain(lhs_ex, rhs, cache, supply);
  }

  return unexpected<Error>(Error::make("cannot constrain given pair"));
}

} // namespace binarysub
