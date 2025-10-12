#include "binarysub.h"

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

TPrimitive* TypeNode::getAsTPrimitive() { return std::get_if<TPrimitive>(&v); }
const TPrimitive* TypeNode::getAsTPrimitive() const { return std::get_if<TPrimitive>(&v); }

TVariable* TypeNode::getAsTVariable() { return std::get_if<TVariable>(&v); }
const TVariable* TypeNode::getAsTVariable() const { return std::get_if<TVariable>(&v); }

TFunction* TypeNode::getAsTFunction() { return std::get_if<TFunction>(&v); }
const TFunction* TypeNode::getAsTFunction() const { return std::get_if<TFunction>(&v); }

TRecord* TypeNode::getAsTRecord() { return std::get_if<TRecord>(&v); }
const TRecord* TypeNode::getAsTRecord() const { return std::get_if<TRecord>(&v); }

TFunction& TypeNode::getAsTFunctionRef() { return std::get<TFunction>(v); }
const TFunction& TypeNode::getAsTFunctionRef() const { return std::get<TFunction>(v); }

bool TypeNode::isTPrimitive() const { return std::holds_alternative<TPrimitive>(v); }
bool TypeNode::isTVariable() const { return std::holds_alternative<TVariable>(v); }
bool TypeNode::isTFunction() const { return std::holds_alternative<TFunction>(v); }
bool TypeNode::isTRecord() const { return std::holds_alternative<TRecord>(v); }

// Helper template function implementations
template<typename T>
constexpr bool isTPrimitiveType() {
  return std::is_same_v<std::decay_t<T>, TPrimitive>;
}

template<typename T>
constexpr bool isTVariableType() {
  return std::is_same_v<std::decay_t<T>, TVariable>;
}

template<typename T>
constexpr bool isTFunctionType() {
  return std::is_same_v<std::decay_t<T>, TFunction>;
}

template<typename T>
constexpr bool isTRecordType() {
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

// ======================= Error implementation ==============================
Error Error::make(std::string m) { return {std::move(m)}; }

// ======================= PolarVS implementation =============================
bool PolarVS::operator<(const PolarVS &other) const {
  if (vs != other.vs)
    return vs < other.vs;
  return pos < other.pos;
}
// ======================= Extrusion implementation =====================
SimpleType extrude(const SimpleType &ty, bool pol, int lvl,
                   std::map<PolarVS, std::shared_ptr<VariableState>> &cache,
                   VarSupply &supply) {
  if (level_of(ty) <= lvl)
    return ty;

  if (auto p = ty->getAsTPrimitive())
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

  PolarVS key{v->state.get(), pol};
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

// ======================= Subtype constraint solver implementation =============
expected<void, Error> constrain_impl(const SimpleType &lhs,
                                     const SimpleType &rhs,
                                     Cache &cache,
                                     VarSupply &supply);

expected<void, Error> constrain(const SimpleType &lhs,
                               const SimpleType &rhs, Cache &cache,
                               VarSupply &supply) {
  auto key = std::make_pair(lhs.get(), rhs.get());
  if (cache.contains(key))
    return expected<void, Error>{};
  cache.insert(key);
  return constrain_impl(lhs, rhs, cache, supply);
}

expected<void, Error> constrain_impl(const SimpleType &lhs,
                                    const SimpleType &rhs,
                                    Cache &cache,
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
    std::map<PolarVS, std::shared_ptr<VariableState>> ex;
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
    std::map<PolarVS, std::shared_ptr<VariableState>> ex;
    auto lhs_ex = extrude(lhs, /*pol=*/true, rv->state->level, ex, supply);
    return constrain(lhs_ex, rhs, cache, supply);
  }

  return unexpected<Error>(Error::make("cannot constrain given pair"));
}

// ======================= User-facing algebraic types & coalescing =========
// (unchanged from previous version, omitted here for brevity in this excerpt)
// -- keep your existing UType, coalesceType, printU implementation --

// ============= Type schemes implementation =================
SimpleType freshen_above_rec(const SimpleType &t, int cutoff,
                             int at_level,
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
          static_assert(!sizeof(T), "Unhandled variant type in freshen_above_rec");
        }
      },
      t->v);
}

SimpleType instantiate(const TypeScheme &sch, int at_level,
                      VarSupply &supply) {
  if (auto m = std::get_if<MonoScheme>(&sch))
    return m->body;
  auto const &p = std::get<PolyScheme>(sch);
  std::map<VariableState *, SimpleType> memo;
  return freshen_above_rec(p.body, p.generalized_above, at_level, memo,
                           supply);
}

// Helper to wrap a rhs type at let generalization point
TypeScheme generalize(const SimpleType &rhs, int env_level) {
  return PolyScheme{env_level, rhs};
}

// ======================= Demo implementation ==============
#ifdef SIMPLESUB_DEMO
int demo_levels() {
  VarSupply supply;
  Scope env; // level=0

  // Build the rhs of "id": α -> α  at level (env.level+1)
  env.enter();                                // enter let-rhs
  auto a = fresh_variable(supply, env.level); // level=1
  auto id_ty = make_function(a, a);
  env.leave();

  // Generalize id at env.level (0)
  TypeScheme id_scheme = generalize(id_ty, /*env_level*/ 0);

  // Two uses at current level=0: instantiate twice (freshenAbove)
  auto id1 = instantiate(id_scheme, env.level, supply);
  auto id2 = instantiate(id_scheme, env.level, supply);

  // Build primitives
  auto TInt = make_primitive("int");
  auto TBool = make_primitive("bool");

  // For application: (int) <: dom(id1)  && cod(id1) <: int   (simulates id 1)
  // and similarly for bool on id2.
  Cache cache;
  // id1 is α1→α1
  auto d1 = id1->getAsTFunctionRef().lhs;
  auto r1 = id1->getAsTFunctionRef().rhs;
  auto d2 = id2->getAsTFunctionRef().lhs;
  auto r2 = id2->getAsTFunctionRef().rhs;

  if (auto e = constrain(TInt, d1, cache, supply); !e) {
    std::cerr << e.error().msg << "\n";
    return 1;
  }
  if (auto e = constrain(r1, TInt, cache, supply); !e) {
    std::cerr << e.error().msg << "\n";
    return 1;
  }
  if (auto e = constrain(TBool, d2, cache, supply); !e) {
    std::cerr << e.error().msg << "\n";
    return 1;
  }
  if (auto e = constrain(r2, TBool, cache, supply); !e) {
    std::cerr << e.error().msg << "\n";
    return 1;
  }

  return 0;
}

// Test function based on the "twice" example from simplesub paper Section 3.4.2
// twice = λf. λx. f(f x)
// Expected type: (α → β) → α → β  (after constraint propagation)
int demo_twice() {
  VarSupply supply;
  Cache cache;
  
  // Create type variables for the twice function: λf. λx. f(f x)
  auto alpha = fresh_variable(supply, 0);     // f's type
  auto beta = fresh_variable(supply, 0);      // x's type  
  auto gamma = fresh_variable(supply, 0);     // result of f x
  auto delta = fresh_variable(supply, 0);     // final result
  
  std::cout << "=== Testing twice function type inference ===\n";
  std::cout << "twice = λf. λx. f(f x)\n";
  
  // Step 1: Analyze inner application f x
  // For f x to be valid: f must be a function (β → γ)
  // So we constrain: α <: (β → γ)  
  auto f_inner_type = make_function(beta, gamma);
  if (auto e = constrain(alpha, f_inner_type, cache, supply); !e) {
    std::cerr << "Failed to constrain f for inner application: " << e.error().msg << "\n";
    return 1;
  }
  std::cout << "✓ Constrained f type for inner application f x\n";
  
  // Step 2: Analyze outer application f (f x)  
  // For f (f x) to be valid: f must be a function (γ → δ)
  // So we constrain: α <: (γ → δ)
  auto f_outer_type = make_function(gamma, delta);
  if (auto e = constrain(alpha, f_outer_type, cache, supply); !e) {
    std::cerr << "Failed to constrain f for outer application: " << e.error().msg << "\n";
    return 1;
  }
  std::cout << "✓ Constrained f type for outer application f(f x)\n";
  
  // At this point, α has two upper bounds: (β → γ) and (γ → δ)
  // Check that the variables are properly constrained
  auto alpha_var = alpha->getAsTVariable();
  if (!alpha_var || alpha_var->state->upperBounds.size() != 2) {
    std::cerr << "Error: α should have exactly 2 upper bounds\n";
    return 1;
  }
  
  std::cout << "✓ Alpha has " << alpha_var->state->upperBounds.size() << " upper bounds as expected\n";
  
  // Test type soundness with concrete types
  // If we apply twice to a function int → int, everything should work
  auto int_type = make_primitive("int");
  auto int_to_int = make_function(int_type, int_type);
  
  Cache test_cache = cache; // copy cache for this test
  
  // Constrain α to be int → int (simulating applying twice to an int → int function)
  if (auto e = constrain(int_to_int, alpha, test_cache, supply); !e) {
    std::cerr << "Failed to apply twice to int → int function: " << e.error().msg << "\n";
    return 1;
  }
  
  // Now constrain β to int (simulating applying the result to an int)
  if (auto e = constrain(int_type, beta, test_cache, supply); !e) {
    std::cerr << "Failed to apply result to int: " << e.error().msg << "\n";
    return 1;
  }
  
  // The result δ should be compatible with int
  if (auto e = constrain(delta, int_type, test_cache, supply); !e) {
    std::cerr << "Result type incompatible with int: " << e.error().msg << "\n";
    return 1;
  }
  
  std::cout << "✓ Successfully applied twice to int → int function\n";
  std::cout << "✓ Result type is correctly int\n";
  
  std::cout << "=== All twice function tests passed! ===\n";
  return 0;
}
#endif

} // namespace simplesub

#ifdef SIMPLESUB_DEMO
int main() { 
  int result1 = simplesub::demo_levels();
  if (result1 != 0) {
    std::cerr << "demo_levels failed\n";
    return result1;
  }
  
  int result2 = simplesub::demo_twice();
  if (result2 != 0) {
    std::cerr << "demo_twice failed\n";
    return result2;
  }
  
  std::cout << "All demos passed!\n";
  return 0;
}
#endif
