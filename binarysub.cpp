#include "binarysub.h"
#include <sstream>

namespace simplesub {

// ======================= Implementation =======================

// VarSupply implementation
std::uint32_t VarSupply::fresh_id() { return next++; }

// Scope implementation
void Scope::enter() { ++level; }
void Scope::leave() { --level; }

// VariableState implementation
VariableState::VariableState(std::uint32_t i, int lvl) : id(i), level(lvl) {}

// TypeNode implementation
TypeNode::TypeNode(TPrimitive p) : v(std::move(p)) {}
TypeNode::TypeNode(TVariable v_) : v(std::move(v_)) {}
TypeNode::TypeNode(TFunction f) : v(std::move(f)) {}
TypeNode::TypeNode(TRecord r) : v(std::move(r)) {}

TPrimitive *TypeNode::getAsTPrimitive() { return std::get_if<TPrimitive>(&v); }
const TPrimitive *TypeNode::getAsTPrimitive() const {
  return std::get_if<TPrimitive>(&v);
}

TVariable *TypeNode::getAsTVariable() { return std::get_if<TVariable>(&v); }
const TVariable *TypeNode::getAsTVariable() const {
  return std::get_if<TVariable>(&v);
}

TFunction *TypeNode::getAsTFunction() { return std::get_if<TFunction>(&v); }
const TFunction *TypeNode::getAsTFunction() const {
  return std::get_if<TFunction>(&v);
}

TRecord *TypeNode::getAsTRecord() { return std::get_if<TRecord>(&v); }
const TRecord *TypeNode::getAsTRecord() const {
  return std::get_if<TRecord>(&v);
}

TFunction &TypeNode::getAsTFunctionRef() { return std::get<TFunction>(v); }
const TFunction &TypeNode::getAsTFunctionRef() const {
  return std::get<TFunction>(v);
}

bool TypeNode::isTPrimitive() const {
  return std::holds_alternative<TPrimitive>(v);
}
bool TypeNode::isTVariable() const {
  return std::holds_alternative<TVariable>(v);
}
bool TypeNode::isTFunction() const {
  return std::holds_alternative<TFunction>(v);
}
bool TypeNode::isTRecord() const { return std::holds_alternative<TRecord>(v); }

// Helper template function implementations
template <typename T> constexpr bool isTPrimitiveType() {
  return std::is_same_v<std::decay_t<T>, TPrimitive>;
}

template <typename T> constexpr bool isTVariableType() {
  return std::is_same_v<std::decay_t<T>, TVariable>;
}

template <typename T> constexpr bool isTFunctionType() {
  return std::is_same_v<std::decay_t<T>, TFunction>;
}

template <typename T> constexpr bool isTRecordType() {
  return std::is_same_v<std::decay_t<T>, TRecord>;
}

// Type creation functions
SimpleType make_primitive(std::string name) {
  return std::make_shared<TypeNode>(TPrimitive{std::move(name)});
}

SimpleType make_variable(std::uint32_t id, int lvl) {
  return std::make_shared<TypeNode>(
      TVariable{std::make_shared<VariableState>(id, lvl)});
}

SimpleType fresh_variable(VarSupply &vs, int lvl) {
  return make_variable(vs.fresh_id(), lvl);
}

SimpleType make_function(SimpleType a, SimpleType b) {
  return std::make_shared<TypeNode>(TFunction{std::move(a), std::move(b)});
}

SimpleType make_record(std::vector<std::pair<std::string, SimpleType>> fields) {
  std::sort(fields.begin(), fields.end(),
            [](auto &x, auto &y) { return x.first < y.first; });
  return std::make_shared<TypeNode>(TRecord{std::move(fields)});
}

// compute the max level contained in a type (lazy in paper; direct here)
// :contentReference[oaicite:3]{index=3}
int level_of(const SimpleType &st) {
  return std::visit(
      [](auto const &n) -> int {
        using T = std::decay_t<decltype(n)>;
        if constexpr (isTPrimitiveType<T>()) {
          return 0;
        } else if constexpr (isTVariableType<T>()) {
          return n.state->level;
        } else if constexpr (isTFunctionType<T>()) {
          return std::max(level_of(n.lhs), level_of(n.rhs));
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
    auto l = extrude(f->lhs, !pol, lvl, cache, supply);
    auto r = extrude(f->rhs, pol, lvl, cache, supply);
    return make_function(std::move(l), std::move(r));
  }

  if (auto r = ty->getAsTRecord()) {
    std::vector<std::pair<std::string, SimpleType>> fs;
    fs.reserve(r->fields.size());
    for (auto const &[n, t] : r->fields) {
      fs.emplace_back(n, extrude(t, pol, lvl, cache, supply));
    }
    return make_record(std::move(fs));
  }

  auto v = ty->getAsTVariable();
  assert(v);

  PolarVar key{v->state.get(), pol};
  if (auto it = cache.find(key); it != cache.end()) {
    return std::make_shared<TypeNode>(TVariable{it->second});
  }

  // Make a copy at requested level
  auto nvs = std::make_shared<VariableState>(supply.fresh_id(), lvl);
  cache.emplace(key, nvs);

  if (pol) {
    // positive: copy lowers to the new var; old var upper-bounds include the
    // new var
    v->state->upperBounds.push_back(std::make_shared<TypeNode>(TVariable{nvs}));
    nvs->lowerBounds.reserve(v->state->lowerBounds.size());
    for (auto const &lb : v->state->lowerBounds)
      nvs->lowerBounds.push_back(extrude(lb, pol, lvl, cache, supply));
  } else {
    // negative: copy uppers to the new var; old var lower-bounds include the
    // new var
    v->state->lowerBounds.push_back(std::make_shared<TypeNode>(TVariable{nvs}));
    nvs->upperBounds.reserve(v->state->upperBounds.size());
    for (auto const &ub : v->state->upperBounds)
      nvs->upperBounds.push_back(extrude(ub, pol, lvl, cache, supply));
  }
  return std::make_shared<TypeNode>(TVariable{nvs});
}

// ======================= Subtype constraint solver implementation
// =============
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
      if (auto e = constrain(rf->lhs, lf->lhs, cache, supply); !e)
        return e;
      if (auto e = constrain(lf->rhs, rf->rhs, cache, supply); !e)
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

  if (auto lv = lhs->getAsTVariable()) {
    // guard: only allow rhs to flow into α if rhs.level <= α.level
    if (level_of(rhs) <= lv->state->level) {
      lv->state->upperBounds.push_back(rhs);
      for (auto const &lb : lv->state->lowerBounds)
        if (auto e = constrain(lb, rhs, cache, supply); !e)
          return e;
      return expected<void, Error>{};
    }
    // else extrude rhs down to lhs.level (negative polarity) and retry
    // :contentReference[oaicite:6]{index=6}
    std::map<PolarVar, std::shared_ptr<VariableState>> ex;
    auto rhs_ex = extrude(rhs, /*pol=*/false, lv->state->level, ex, supply);
    return constrain(lhs, rhs_ex, cache, supply);
  }

  if (auto rv = rhs->getAsTVariable()) {
    if (level_of(lhs) <= rv->state->level) {
      rv->state->lowerBounds.push_back(lhs);
      for (auto const &ub : rv->state->upperBounds)
        if (auto e = constrain(lhs, ub, cache, supply); !e)
          return e;
      return expected<void, Error>{};
    }
    // else extrude lhs down to rhs.level (positive polarity) and retry
    // :contentReference[oaicite:7]{index=7}
    std::map<PolarVar, std::shared_ptr<VariableState>> ex;
    auto lhs_ex = extrude(lhs, /*pol=*/true, rv->state->level, ex, supply);
    return constrain(lhs_ex, rhs, cache, supply);
  }

  return unexpected<Error>(Error::make("cannot constrain given pair"));
}

// ======================= User-facing algebraic types & coalescing =========

// Generate unique variable names
static std::uint32_t var_name_counter = 0;
std::string fresh_var_name() {
  return "α" + std::to_string(var_name_counter++);
}

// Pretty printing implementation
std::string printType(const UTypePtr &ty) {
  std::ostringstream oss;
  printTypeImpl(ty, oss, 0);
  return oss.str();
}

void printTypeImpl(const UTypePtr &ty, std::ostream &os, int precedence) {
  std::visit(
      [&](auto const &n) {
        using T = std::decay_t<decltype(n)>;
        if constexpr (std::is_same_v<T, UTop>) {
          os << "⊤";
        } else if constexpr (std::is_same_v<T, UBot>) {
          os << "⊥";
        } else if constexpr (std::is_same_v<T, UPrimitiveType>) {
          os << n.name;
        } else if constexpr (std::is_same_v<T, UTypeVariable>) {
          os << n.name;
        } else if constexpr (std::is_same_v<T, UFunctionType>) {
          bool needParens = precedence > 1;
          if (needParens)
            os << "(";
          printTypeImpl(n.lhs, os, 2);
          os << " → ";
          printTypeImpl(n.rhs, os, 1);
          if (needParens)
            os << ")";
        } else if constexpr (std::is_same_v<T, UUnion>) {
          bool needParens = precedence > 3;
          if (needParens)
            os << "(";
          printTypeImpl(n.lhs, os, 4);
          os << " ∪ ";
          printTypeImpl(n.rhs, os, 3);
          if (needParens)
            os << ")";
        } else if constexpr (std::is_same_v<T, UInter>) {
          bool needParens = precedence > 4;
          if (needParens)
            os << "(";
          printTypeImpl(n.lhs, os, 5);
          os << " ∩ ";
          printTypeImpl(n.rhs, os, 4);
          if (needParens)
            os << ")";
        } else if constexpr (std::is_same_v<T, URecordType>) {
          os << "{";
          for (size_t i = 0; i < n.fields.size(); ++i) {
            if (i > 0)
              os << "; ";
            os << n.fields[i].first << ": ";
            printTypeImpl(n.fields[i].second, os, 0);
          }
          os << "}";
        } else if constexpr (std::is_same_v<T, URecursiveType>) {
          os << "μ" << n.name << ".";
          printTypeImpl(n.body, os, 0);
        } else {
          static_assert(!sizeof(T), "Unhandled UType variant in printTypeImpl");
        }
      },
      ty->v);
}

// ============= Type schemes implementation =================
SimpleType freshen_above_rec(const SimpleType &t, int cutoff, int at_level,
                             std::map<VariableState *, SimpleType> &memo,
                             VarSupply &supply) {
  return std::visit(
      [&](auto const &n) -> SimpleType {
        using T = std::decay_t<decltype(n)>;
        if constexpr (isTPrimitiveType<T>()) {
          return t;
        } else if constexpr (isTFunctionType<T>()) {
          return make_function(
              freshen_above_rec(n.lhs, cutoff, at_level, memo, supply),
              freshen_above_rec(n.rhs, cutoff, at_level, memo, supply));
        } else if constexpr (isTRecordType<T>()) {
          std::vector<std::pair<std::string, SimpleType>> fs;
          fs.reserve(n.fields.size());
          for (auto const &[name, sub] : n.fields)
            fs.emplace_back(
                name, freshen_above_rec(sub, cutoff, at_level, memo, supply));
          return make_record(std::move(fs));
        } else if constexpr (isTVariableType<T>()) {
          // TVariable
          auto *vs = n.state.get();
          if (vs->level > cutoff) {
            if (auto it = memo.find(vs); it != memo.end())
              return it->second;
            auto fresh =
                fresh_variable(supply, at_level); // empty bounds, new id/level
            memo.emplace(vs, fresh);
            return fresh;
          }
          return t;
        } else {
          static_assert(!sizeof(T),
                        "Unhandled variant type in freshen_above_rec");
        }
      },
      t->v);
}

SimpleType instantiate(const TypeScheme &sch, int at_level, VarSupply &supply) {
  if (auto m = std::get_if<MonoScheme>(&sch))
    return m->body;
  auto const &p = std::get<PolyScheme>(sch);
  std::map<VariableState *, SimpleType> memo;
  return freshen_above_rec(p.body, p.generalized_above, at_level, memo, supply);
}

// Helper to wrap a rhs type at let generalization point
TypeScheme generalize(const SimpleType &rhs, int env_level) {
  return PolyScheme{env_level, rhs};
}



} // namespace simplesub

// =================== Type Simplification Implementation
// ===========================

namespace simplesub {

// Helper function to get variable ID from type variable names (assumes format
// "α123")
std::uint32_t extractVariableId(const std::string &varName) {
  if (varName.empty() || varName.substr(0, 1) != "α")
    return 0;
  try {
    return std::stoul(varName.substr(1));
  } catch (...) {
    return 0;
  }
}

// ======================= CompactType Implementation =======================

// Helper function to merge two CompactTypes based on polarity
std::shared_ptr<CompactType>
merge_compact_types(bool pol, const std::shared_ptr<CompactType> &lhs,
                    const std::shared_ptr<CompactType> &rhs) {

  auto result = std::make_shared<CompactType>();

  // Merge variables (always union)
  result->vars = lhs->vars;
  result->vars.insert(rhs->vars.begin(), rhs->vars.end());

  // Merge primitives (always union)
  result->prims = lhs->prims;
  result->prims.insert(rhs->prims.begin(), rhs->prims.end());

  // Merge record types
  if (lhs->record && rhs->record) {
    auto merged_rec =
        std::make_shared<std::map<std::string, std::shared_ptr<CompactType>>>();
    if (pol) {
      // Positive: intersection of common fields
      for (const auto &[k, v] : *lhs->record) {
        auto it = rhs->record->find(k);
        if (it != rhs->record->end()) {
          (*merged_rec)[k] = merge_compact_types(pol, v, it->second);
        }
      }
    } else {
      // Negative: union of all fields
      *merged_rec = *lhs->record;
      for (const auto &[k, v] : *rhs->record) {
        auto it = merged_rec->find(k);
        if (it != merged_rec->end()) {
          it->second = merge_compact_types(pol, it->second, v);
        } else {
          (*merged_rec)[k] = v;
        }
      }
    }
    if (!merged_rec->empty()) {
      result->record = *merged_rec;
    }
  } else if (lhs->record) {
    result->record = lhs->record;
  } else if (rhs->record) {
    result->record = rhs->record;
  }

  // Merge function types
  if (lhs->function && rhs->function) {
    result->function = std::make_pair(
        merge_compact_types(!pol, lhs->function->first, rhs->function->first),
        merge_compact_types(pol, lhs->function->second, rhs->function->second));
  } else if (lhs->function) {
    result->function = lhs->function;
  } else if (rhs->function) {
    result->function = rhs->function;
  }

  return result;
}

std::string toString(const CompactType &ct) {
  // TODO
}

} // namespace simplesub
