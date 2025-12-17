
#include "binarysub-core.h"
#include <functional>

namespace binarysub {

// Define the global variable supply
VarSupply globalVarSupply;

// compute the max level contained in a type (lazy in paper; direct here)
int level_of(const SimpleType &st) {
  if (st->isTPrimitive()) {
    return 0;
  } else if (auto n = st->getAsVariableState()) {
    return n->level;
  } else if (auto n = st->getAsTFunction()) {
    int m = level_of(n->result);
    for (auto const &arg : n->args)
      m = std::max(m, level_of(arg));
    return m;
  } else if (auto n = st->getAsTRecord()) {
    int m = 0;
    for (auto const &[_, t] : n->fields)
      m = std::max(m, level_of(t));
    return m;
  } else {
    assert(false && "Unhandled variant type in level_of");
  }
}

// ======================= Extrusion implementation =====================
SimpleType extrude(const SimpleType &ty, bool pol, int lvl,
                   std::map<PolarVar, SimpleType> &cache) {
  if (level_of(ty) <= lvl)
    return ty;

  if (auto p [[maybe_unused]] = ty->getAsTPrimitive())
    return ty;

  if (auto f = ty->getAsTFunction()) {
    std::vector<SimpleType> newArgs;
    newArgs.reserve(f->args.size());
    for (auto const &a : f->args)
      newArgs.push_back(extrude(a, !pol, lvl, cache));
    auto r = extrude(f->result, pol, lvl, cache);
    return make_function(std::move(newArgs), std::move(r));
  }

  if (auto r = ty->getAsTRecord()) {
    std::vector<std::pair<std::string, SimpleType>> fs;
    fs.reserve(r->fields.size());
    for (auto const &[n, t] : r->fields) {
      fs.emplace_back(n, extrude(t, pol, lvl, cache));
    }
    return make_record(std::move(fs));
  }

  auto vs = ty->getAsVariableState();
  assert(vs);

  PolarVar key{ty, pol};
  if (auto it = cache.find(key); it != cache.end()) {
    return it->second;
  }

  // Make a copy at requested level
  auto nvs = make_variable(lvl);
  cache.emplace(key, nvs);
  auto nvs_vs = nvs->getAsVariableState();

  if (pol) {
    // positive: copy lowers to the new var; old var upper-bounds include the
    // new var
    vs->upperBounds.push_back(nvs);
    nvs_vs->lowerBounds.reserve(vs->lowerBounds.size());
    for (auto const &lb : vs->lowerBounds)
      nvs_vs->lowerBounds.push_back(extrude(lb, pol, lvl, cache));
  } else {
    // negative: copy uppers to the new var; old var lower-bounds include the
    // new var
    vs->lowerBounds.push_back(nvs);
    nvs_vs->upperBounds.reserve(vs->upperBounds.size());
    for (auto const &ub : vs->upperBounds)
      nvs_vs->upperBounds.push_back(extrude(ub, pol, lvl, cache));
  }
  return nvs;
}

// ======================= Subtype constraint solver implementation
expected<void, Error> constrain_impl(
    const SimpleType &lhs, const SimpleType &rhs, Cache &cache,
    std::function<void(const SimpleType &, const SimpleType &)> AddToWorklist);

expected<void, Error> constrain(const SimpleType &lhs, const SimpleType &rhs,
                                Cache &cache) {
  // Worklist用于存储待处理的约束对
  std::vector<std::pair<SimpleType, SimpleType>> worklist;

  auto AddToWorklist = [&](const SimpleType &l, const SimpleType &r) {
    // 检查缓存，避免重复添加
    auto key = std::make_pair(l.get(), r.get());
    if (cache.find(key) == cache.end()) {
      worklist.emplace_back(l, r);
    }
  };

  // 初始约束加入worklist
  AddToWorklist(lhs, rhs);

  while (!worklist.empty()) {
    auto [current_lhs, current_rhs] = worklist.back();
    worklist.pop_back();

    // 检查缓存，避免重复处理
    auto key = std::make_pair(current_lhs.get(), current_rhs.get());
    if (cache.find(key) != cache.end()) {
      continue;
    }
    cache.insert(key);

    // 处理当前约束，将新产生的约束加入worklist
    if (auto result = constrain_impl(current_lhs, current_rhs, cache,
                                     AddToWorklist);
        !result) {
      return result;
    }
  }

  return expected<void, Error>{};
}

expected<void, Error> constrain_impl(
    const SimpleType &lhs, const SimpleType &rhs, Cache &cache,
    std::function<void(const SimpleType &, const SimpleType &)> AddToWorklist) {
  // 处理基本类型
  if (auto lp = lhs->getAsTPrimitive()) {
    if (auto rp = rhs->getAsTPrimitive()) {
      if (lp->name == rp->name)
        return expected<void, Error>{};
      else
        return unexpected<Error>(Error::make("primitive mismatch: " + lp->name +
                                             " </: " + rp->name));
    }
  }

  // 处理函数类型
  if (auto lf = lhs->getAsTFunction())
    if (auto rf = rhs->getAsTFunction()) {
      if (lf->args.size() < rf->args.size()) {
        return unexpected<Error>(
            Error::make("function arity mismatch: subtype has fewer params"));
      }
      // 将参数约束加入worklist
      for (size_t i = 0; i < rf->args.size(); ++i) {
        AddToWorklist(rf->args[i], lf->args[i]);
      }
      // 将返回类型约束加入worklist
      AddToWorklist(lf->result, rf->result);
      return expected<void, Error>{};
    }

  // 处理记录类型
  if (auto lr = lhs->getAsTRecord())
    if (auto rr = rhs->getAsTRecord()) {
      std::map<std::string, SimpleType> fmap;
      for (auto const &[n, t] : lr->fields)
        fmap[n] = t;
      for (auto const &[n_req, t_req] : rr->fields) {
        auto it = fmap.find(n_req);
        if (it == fmap.end())
          return unexpected<Error>(Error::make("missing field: " + n_req));
        // 将字段约束加入worklist
        AddToWorklist(it->second, t_req);
      }
      return expected<void, Error>{};
    }

  // 处理左侧是变量的情况
  if (auto lv = lhs->getAsVariableState()) {
    // guard: only allow rhs to flow into α if rhs.level <= α.level
    if (level_of(rhs) <= lv->level) {
      lv->upperBounds.push_back(rhs);
      // 将新产生的约束加入worklist
      for (auto const &lb : lv->lowerBounds) {
        AddToWorklist(lb, rhs);
      }
      return expected<void, Error>{};
    }
    // else extrude rhs down to lhs.level (negative polarity) and retry
    // make a copy of the problematic type such that the copy has the requested
    // level and soundly approximates the original type.
    std::map<PolarVar, SimpleType> ex;
    auto rhs_ex = extrude(rhs, /*pol=*/false, lv->level, ex);
    // 将extrude后的约束加入worklist
    AddToWorklist(lhs, rhs_ex);
    return expected<void, Error>{};
  }

  // 处理右侧是变量的情况
  if (auto rv = rhs->getAsVariableState()) {
    if (level_of(lhs) <= rv->level) {
      rv->lowerBounds.push_back(lhs);
      // 将新产生的约束加入worklist
      for (auto const &ub : rv->upperBounds) {
        AddToWorklist(lhs, ub);
      }
      return expected<void, Error>{};
    }
    // else extrude lhs down to rhs.level (positive polarity) and retry
    std::map<PolarVar, SimpleType> ex;
    auto lhs_ex = extrude(lhs, /*pol=*/true, rv->level, ex);
    // 将extrude后的约束加入worklist
    AddToWorklist(lhs_ex, rhs);
    return expected<void, Error>{};
  }

  return unexpected<Error>(Error::make("cannot constrain given pair"));
}

} // namespace binarysub
