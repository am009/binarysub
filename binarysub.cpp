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
  if (cache.find(key) != cache.end())
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

// Helper functions to create UType instances
UTypePtr make_utop() {
  return std::make_shared<UType>(UTop{});
}

UTypePtr make_ubot() {
  return std::make_shared<UType>(UBot{});
}

UTypePtr make_uunion(UTypePtr lhs, UTypePtr rhs) {
  return std::make_shared<UType>(UUnion{std::move(lhs), std::move(rhs)});
}

UTypePtr make_uinter(UTypePtr lhs, UTypePtr rhs) {
  return std::make_shared<UType>(UInter{std::move(lhs), std::move(rhs)});
}

UTypePtr make_ufunctiontype(UTypePtr lhs, UTypePtr rhs) {
  return std::make_shared<UType>(UFunctionType{std::move(lhs), std::move(rhs)});
}

UTypePtr make_urecordtype(std::vector<std::pair<std::string, UTypePtr>> fields) {
  return std::make_shared<UType>(URecordType{std::move(fields)});
}

UTypePtr make_urecursivetype(std::string name, UTypePtr body) {
  return std::make_shared<UType>(URecursiveType{std::move(name), std::move(body)});
}

UTypePtr make_utypevariable(std::string name) {
  return std::make_shared<UType>(UTypeVariable{std::move(name)});
}

UTypePtr make_uprimitivetype(std::string name) {
  return std::make_shared<UType>(UPrimitiveType{std::move(name)});
}

// PolarVar implementation
bool PolarVar::operator<(const PolarVar& other) const {
  if (vs != other.vs)
    return vs < other.vs;
  return polar < other.polar;
}

// Generate unique variable names
static std::uint32_t var_name_counter = 0;
std::string fresh_var_name() {
  return "α" + std::to_string(var_name_counter++);
}

// Type coalescing implementation based on paper Section 3.3.3
UTypePtr coalesceType(const SimpleType& st) {
  std::set<PolarVar> inProcess;
  std::map<PolarVar, std::string> recursive;
  return coalesceTypeImpl(st, true, inProcess, recursive);
}

UTypePtr coalesceTypeImpl(const SimpleType& st, bool polar, 
                         std::set<PolarVar>& inProcess,
                         std::map<PolarVar, std::string>& recursive) {
  return std::visit(
      [&](auto const &n) -> UTypePtr {
        using T = std::decay_t<decltype(n)>;
        if constexpr (isTPrimitiveType<T>()) {
          return make_uprimitivetype(n.name);
        } else if constexpr (isTFunctionType<T>()) {
          auto l = coalesceTypeImpl(n.lhs, !polar, inProcess, recursive);
          auto r = coalesceTypeImpl(n.rhs, polar, inProcess, recursive);
          return make_ufunctiontype(std::move(l), std::move(r));
        } else if constexpr (isTRecordType<T>()) {
          std::vector<std::pair<std::string, UTypePtr>> fields;
          fields.reserve(n.fields.size());
          for (auto const& [name, ty] : n.fields) {
            fields.emplace_back(name, coalesceTypeImpl(ty, polar, inProcess, recursive));
          }
          return make_urecordtype(std::move(fields));
        } else if constexpr (isTVariableType<T>()) {
          PolarVar pv{n.state.get(), polar};
          
          // Check if we're already processing this variable (recursion detection)
          if (inProcess.find(pv) != inProcess.end()) {
            auto it = recursive.find(pv);
            if (it != recursive.end()) {
              return make_utypevariable(it->second);
            } else {
              std::string varName = fresh_var_name();
              recursive[pv] = varName;
              return make_utypevariable(varName);
            }
          }
          
          inProcess.insert(pv);
          
          // Get the appropriate bounds based on polarity
          const auto& bounds = polar ? n.state->lowerBounds : n.state->upperBounds;
          
          if (bounds.empty()) {
            // No bounds, return the variable itself
            std::string varName = "α" + std::to_string(n.state->id);
            inProcess.erase(pv);
            return make_utypevariable(varName);
          }
          
          // Convert bounds to user types
          std::vector<UTypePtr> boundTypes;
          boundTypes.reserve(bounds.size());
          for (const auto& bound : bounds) {
            boundTypes.push_back(coalesceTypeImpl(bound, polar, inProcess, recursive));
          }
          
          // Combine bounds with union (for positive) or intersection (for negative)
          UTypePtr result;
          if (polar) {
            // Positive: union of lower bounds
            result = boundTypes[0];
            for (size_t i = 1; i < boundTypes.size(); ++i) {
              result = make_uunion(result, boundTypes[i]);
            }
          } else {
            // Negative: intersection of upper bounds
            result = boundTypes[0];
            for (size_t i = 1; i < boundTypes.size(); ++i) {
              result = make_uinter(result, boundTypes[i]);
            }
          }
          
          inProcess.erase(pv);
          
          // Check if this was a recursive variable
          auto it = recursive.find(pv);
          if (it != recursive.end()) {
            return make_urecursivetype(it->second, result);
          }
          
          return result;
        } else {
          static_assert(!sizeof(T), "Unhandled variant type in coalesceTypeImpl");
        }
      },
      st->v);
}

// Pretty printing implementation
std::string printType(const UTypePtr& ty) {
  std::ostringstream oss;
  printTypeImpl(ty, oss, 0);
  return oss.str();
}

void printTypeImpl(const UTypePtr& ty, std::ostream& os, int precedence) {
  std::visit([&](auto const& n) {
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
      if (needParens) os << "(";
      printTypeImpl(n.lhs, os, 2);
      os << " → ";
      printTypeImpl(n.rhs, os, 1);
      if (needParens) os << ")";
    } else if constexpr (std::is_same_v<T, UUnion>) {
      bool needParens = precedence > 3;
      if (needParens) os << "(";
      printTypeImpl(n.lhs, os, 4);
      os << " ∪ ";
      printTypeImpl(n.rhs, os, 3);
      if (needParens) os << ")";
    } else if constexpr (std::is_same_v<T, UInter>) {
      bool needParens = precedence > 4;
      if (needParens) os << "(";
      printTypeImpl(n.lhs, os, 5);
      os << " ∩ ";
      printTypeImpl(n.rhs, os, 4);
      if (needParens) os << ")";
    } else if constexpr (std::is_same_v<T, URecordType>) {
      os << "{";
      for (size_t i = 0; i < n.fields.size(); ++i) {
        if (i > 0) os << "; ";
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
  }, ty->v);
}

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
  std::cout << "twice = λf. λx. f(f x)\n\n";
  
  // Build the twice function type structure: α → β → δ
  auto twice_type = make_function(alpha, make_function(beta, delta));
  
  std::cout << "Initial structure: " << printType(coalesceType(twice_type)) << "\n\n";
  
  // Step 1: Analyze inner application f x
  // For f x to be valid: f must be a function (β → γ)
  // So we constrain: α <: (β → γ)  
  auto f_inner_type = make_function(beta, gamma);
  if (auto e = constrain(alpha, f_inner_type, cache, supply); !e) {
    std::cerr << "Failed to constrain f for inner application: " << e.error().msg << "\n";
    return 1;
  }
  std::cout << "✓ Constrained f type for inner application f x\n";
  std::cout << "  α <: β → γ  (f must accept x and return some γ)\n";
  
  // Show current twice type after first constraint
  std::cout << "  Current twice type: " << printType(coalesceType(twice_type)) << "\n\n";
  
  // Step 2: Analyze outer application f (f x)  
  // For f (f x) to be valid: f must be a function (γ → δ)
  // So we constrain: α <: (γ → δ)
  auto f_outer_type = make_function(gamma, delta);
  if (auto e = constrain(alpha, f_outer_type, cache, supply); !e) {
    std::cerr << "Failed to constrain f for outer application: " << e.error().msg << "\n";
    return 1;
  }
  std::cout << "✓ Constrained f type for outer application f(f x)\n";
  std::cout << "  α <: γ → δ  (f must accept γ and return final result δ)\n";
  
  // Show final twice type after all constraints
  std::cout << "  Final twice type: " << printType(coalesceType(twice_type)) << "\n";
  std::cout << "  After simplification: " << printType(simplifyType(coalesceType(twice_type))) << "\n\n";
  
  // At this point, α has two upper bounds: (β → γ) and (γ → δ)
  // Check that the variables are properly constrained
  auto alpha_var = alpha->getAsTVariable();
  if (!alpha_var || alpha_var->state->upperBounds.size() != 2) {
    std::cerr << "Error: α should have exactly 2 upper bounds\n";
    return 1;
  }
  
  std::cout << "✓ Alpha has " << alpha_var->state->upperBounds.size() << " upper bounds as expected\n";
  
  // Show individual variable types
  std::cout << "\nVariable constraint analysis:\n";
  std::cout << "  α (f type): " << printType(coalesceType(alpha)) << "\n";
  std::cout << "  β (x type): " << printType(coalesceType(beta)) << "\n";
  std::cout << "  γ (intermediate): " << printType(coalesceType(gamma)) << "\n";
  std::cout << "  δ (result): " << printType(coalesceType(delta)) << "\n\n";
  
  // Test type soundness with concrete types
  // If we apply twice to a function int → int, everything should work
  std::cout << "=== Testing with concrete int → int function ===\n";
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
  std::cout << "  When f: int → int and x: int\n";
  std::cout << "  Result twice type: " << printType(coalesceType(twice_type)) << "\n";
  std::cout << "✓ Result type is correctly int\n";
  
  std::cout << "\n=== All twice function tests passed! ===\n";
  return 0;
}

// Test simplification strategies based on paper examples
int demo_simplification() {
  VarSupply supply;
  
  std::cout << "=== Testing Type Simplification Strategies ===\n\n";
  
  // Test 1: Polar variable removal (Section 4.3.1)
  // Type: α ∩ int → int  (α only appears negatively, should be simplified to int → int)
  std::cout << "Test 1: Polar variable removal\n";
  std::cout << "Input type: α ∩ int → int\n";
  
  auto alpha = make_utypevariable("α1");
  auto int_type = make_uprimitivetype("int");
  auto alpha_inter_int = make_uinter(alpha, int_type);
  auto polar_test_type = make_ufunctiontype(alpha_inter_int, int_type);
  
  std::cout << "Before simplification: " << printType(polar_test_type) << "\n";
  auto simplified_polar = simplifyType(polar_test_type);
  std::cout << "After simplification:  " << printType(simplified_polar) << "\n";
  std::cout << "✓ Expected int → int (α removed because it only appears negatively)\n\n";
  
  // Test 2: Variable sandwich flattening (Section 4.3.1)
  // Type: α ∩ int → α ∪ int  (α sandwiched between int, should simplify to int → int)
  std::cout << "Test 2: Variable sandwich flattening\n";  
  std::cout << "Input type: α ∩ int → α ∪ int\n";
  
  auto beta = make_utypevariable("α2");
  auto beta_inter_int = make_uinter(beta, int_type);
  auto beta_union_int = make_uunion(beta, int_type);
  auto sandwich_test_type = make_ufunctiontype(beta_inter_int, beta_union_int);
  
  std::cout << "Before simplification: " << printType(sandwich_test_type) << "\n";
  auto simplified_sandwich = simplifyType(sandwich_test_type);
  std::cout << "After simplification:  " << printType(simplified_sandwich) << "\n";
  std::cout << "✓ Expected int → int (α equivalent to int)\n\n";
  
  // Test 3: if-then-else type simplification (from paper)
  // Type: bool → α → β → α ∪ β should simplify to bool → α → α → α
  std::cout << "Test 3: if-then-else type unification\n";
  std::cout << "Input type: bool → α → β → α ∪ β\n";
  
  auto bool_type = make_uprimitivetype("bool");
  auto gamma = make_utypevariable("α3");
  auto delta = make_utypevariable("α4");
  auto gamma_union_delta = make_uunion(gamma, delta);
  auto if_type = make_ufunctiontype(bool_type, 
                   make_ufunctiontype(gamma,
                     make_ufunctiontype(delta, gamma_union_delta)));
  
  std::cout << "Before simplification: " << printType(if_type) << "\n";
  auto simplified_if = simplifyType(if_type);
  std::cout << "After simplification:  " << printType(simplified_if) << "\n";
  std::cout << "✓ Expected α and β to be unified since they're indistinguishable\n\n";
  
  // Test 4: Record type simplification
  std::cout << "Test 4: Record type with polar variables\n";
  std::cout << "Input type: {x: α, y: α → int}\n";
  
  auto epsilon = make_utypevariable("α5");
  auto epsilon_to_int = make_ufunctiontype(epsilon, int_type);
  std::vector<std::pair<std::string, UTypePtr>> record_fields = {
    {"x", epsilon},
    {"y", epsilon_to_int}
  };
  auto record_test_type = make_urecordtype(record_fields);
  
  std::cout << "Before simplification: " << printType(record_test_type) << "\n";
  auto simplified_record = simplifyType(record_test_type);
  std::cout << "After simplification:  " << printType(simplified_record) << "\n";
  std::cout << "✓ α appears both positively and negatively, should be preserved\n\n";
  
  // Test 5: Complex nested type
  std::cout << "Test 5: Complex nested type with multiple variables\n";
  std::cout << "Input type: (α → β) → (β → γ) → α → γ\n";
  
  auto zeta = make_utypevariable("α6");
  auto eta = make_utypevariable("α7");  
  auto theta = make_utypevariable("α8");
  auto zeta_to_eta = make_ufunctiontype(zeta, eta);
  auto eta_to_theta = make_ufunctiontype(eta, theta);
  auto zeta_to_theta = make_ufunctiontype(zeta, theta);
  auto complex_type = make_ufunctiontype(zeta_to_eta,
                        make_ufunctiontype(eta_to_theta, zeta_to_theta));
  
  std::cout << "Before simplification: " << printType(complex_type) << "\n";
  auto simplified_complex = simplifyType(complex_type);
  std::cout << "After simplification:  " << printType(simplified_complex) << "\n";
  std::cout << "✓ This represents function composition, variables should be preserved\n\n";
  
  // Test 6: Demonstrate hash consing with recursive types
  std::cout << "Test 6: Hash consing with structural sharing\n";
  auto iota = make_utypevariable("α9");
  auto duplicate_subtype = make_ufunctiontype(int_type, iota);
  auto sharing_test = make_uunion(duplicate_subtype, duplicate_subtype);
  
  std::cout << "Before simplification: " << printType(sharing_test) << "\n";
  auto simplified_sharing = simplifyType(sharing_test);
  std::cout << "After simplification:  " << printType(simplified_sharing) << "\n";
  std::cout << "✓ Duplicate structures should be shared via hash consing\n\n";
  
  std::cout << "=== All simplification tests completed! ===\n";
  return 0;
}
#endif

} // namespace simplesub

// =================== Type Simplification Implementation ===========================

namespace simplesub {

// Helper function to get variable ID from type variable names (assumes format "α123")
std::uint32_t extractVariableId(const std::string& varName) {
  if (varName.empty() || varName.substr(0, 1) != "α") return 0;
  try {
    return std::stoul(varName.substr(1));
  } catch (...) {
    return 0;
  }
}

// Helper function to compute type hash for hash consing
std::string computeTypeHash(const UTypePtr& ty) {
  std::ostringstream oss;
  std::visit([&](auto const& n) {
    using T = std::decay_t<decltype(n)>;
    if constexpr (std::is_same_v<T, UTop>) {
      oss << "TOP";
    } else if constexpr (std::is_same_v<T, UBot>) {
      oss << "BOT";
    } else if constexpr (std::is_same_v<T, UPrimitiveType>) {
      oss << "PRIM:" << n.name;
    } else if constexpr (std::is_same_v<T, UTypeVariable>) {
      oss << "VAR:" << n.name;
    } else if constexpr (std::is_same_v<T, UFunctionType>) {
      oss << "FUN(" << computeTypeHash(n.lhs) << "->" << computeTypeHash(n.rhs) << ")";
    } else if constexpr (std::is_same_v<T, UUnion>) {
      oss << "UNION(" << computeTypeHash(n.lhs) << "+" << computeTypeHash(n.rhs) << ")";
    } else if constexpr (std::is_same_v<T, UInter>) {
      oss << "INTER(" << computeTypeHash(n.lhs) << "&" << computeTypeHash(n.rhs) << ")";
    } else if constexpr (std::is_same_v<T, URecordType>) {
      oss << "REC{";
      for (size_t i = 0; i < n.fields.size(); ++i) {
        if (i > 0) oss << ";";
        oss << n.fields[i].first << ":" << computeTypeHash(n.fields[i].second);
      }
      oss << "}";
    } else if constexpr (std::is_same_v<T, URecursiveType>) {
      oss << "MU(" << n.name << "." << computeTypeHash(n.body) << ")";
    }
  }, ty->v);
  return oss.str();
}

// Co-occurrence analysis implementation (Section 4.3.1)
void analyzeOccurrencesImpl(const UTypePtr& ty, bool positive, OccurrenceMap& occMap, 
                           std::set<std::uint32_t>& currentContext) {
  std::visit([&](auto const& n) {
    using T = std::decay_t<decltype(n)>;
    if constexpr (std::is_same_v<T, UTop>) {
      // Top doesn't contribute to co-occurrence
    } else if constexpr (std::is_same_v<T, UBot>) {
      // Bot doesn't contribute to co-occurrence
    } else if constexpr (std::is_same_v<T, UTypeVariable>) {
      std::uint32_t varId = extractVariableId(n.name);
      if (varId != 0) {
        auto& occ = occMap[varId];
        if (positive) {
          occ.appearsPositive = true;
          // Record co-occurrence with other variables in current context
          for (auto otherId : currentContext) {
            occ.coOccurs.positiveVars.insert(otherId);
            occMap[otherId].coOccurs.positiveVars.insert(varId);
          }
        } else {
          occ.appearsNegative = true;
          for (auto otherId : currentContext) {
            occ.coOccurs.negativeVars.insert(otherId);
            occMap[otherId].coOccurs.negativeVars.insert(varId);
          }
        }
        currentContext.insert(varId);
      }
    } else if constexpr (std::is_same_v<T, UPrimitiveType>) {
      // Record primitive co-occurrence with variables in context
      for (auto varId : currentContext) {
        if (positive) {
          occMap[varId].coOccurs.positivePrims.insert(n.name);
        } else {
          occMap[varId].coOccurs.negativePrims.insert(n.name);
        }
      }
    } else if constexpr (std::is_same_v<T, UFunctionType>) {
      // Function: lhs is negative, rhs is positive
      analyzeOccurrencesImpl(n.lhs, !positive, occMap, currentContext);
      analyzeOccurrencesImpl(n.rhs, positive, occMap, currentContext);
    } else if constexpr (std::is_same_v<T, UUnion>) {
      // Union: both sides have same polarity
      std::set<std::uint32_t> leftContext = currentContext;
      std::set<std::uint32_t> rightContext = currentContext;
      analyzeOccurrencesImpl(n.lhs, positive, occMap, leftContext);
      analyzeOccurrencesImpl(n.rhs, positive, occMap, rightContext);
      // Merge contexts for co-occurrence
      currentContext.insert(leftContext.begin(), leftContext.end());
      currentContext.insert(rightContext.begin(), rightContext.end());
    } else if constexpr (std::is_same_v<T, UInter>) {
      // Intersection: both sides have same polarity  
      std::set<std::uint32_t> leftContext = currentContext;
      std::set<std::uint32_t> rightContext = currentContext;
      analyzeOccurrencesImpl(n.lhs, positive, occMap, leftContext);
      analyzeOccurrencesImpl(n.rhs, positive, occMap, rightContext);
      currentContext.insert(leftContext.begin(), leftContext.end());
      currentContext.insert(rightContext.begin(), rightContext.end());
    } else if constexpr (std::is_same_v<T, URecordType>) {
      // Record fields: same polarity
      for (const auto& [name, fieldType] : n.fields) {
        analyzeOccurrencesImpl(fieldType, positive, occMap, currentContext);
      }
    } else if constexpr (std::is_same_v<T, URecursiveType>) {
      // Recursive types: analyze body
      analyzeOccurrencesImpl(n.body, positive, occMap, currentContext);
    } else {
      static_assert(!sizeof(T), "Unhandled UType variant in analyzeOccurrencesImpl");
    }
  }, ty->v);
}

OccurrenceMap analyzeOccurrences(const UTypePtr& ty) {
  OccurrenceMap occMap;
  std::set<std::uint32_t> context;
  analyzeOccurrencesImpl(ty, true, occMap, context);
  return occMap;
}

// Polar variable removal (Section 4.3.1)
UTypePtr removePolarVariables(const UTypePtr& ty, const OccurrenceMap& occMap) {
  return std::visit([&](auto const& n) -> UTypePtr {
    using T = std::decay_t<decltype(n)>;
    if constexpr (std::is_same_v<T, UTop>) {
      return ty; // Top unchanged
    } else if constexpr (std::is_same_v<T, UBot>) {
      return ty; // Bot unchanged
    } else if constexpr (std::is_same_v<T, UPrimitiveType>) {
      return ty; // Primitive unchanged
    } else if constexpr (std::is_same_v<T, UTypeVariable>) {
      std::uint32_t varId = extractVariableId(n.name);
      if (varId != 0) {
        auto it = occMap.find(varId);
        if (it != occMap.end()) {
          const auto& occ = it->second;
          // Remove variables that appear only positively (replace with ⊥) 
          // or only negatively (replace with ⊤)
          if (occ.appearsPositive && !occ.appearsNegative) {
            return make_ubot(); // Variable only appears positively, can be ⊥
          }
          if (occ.appearsNegative && !occ.appearsPositive) {
            return make_utop(); // Variable only appears negatively, can be ⊤
          }
        }
      }
      return ty; // Keep variable as-is
    } else if constexpr (std::is_same_v<T, UFunctionType>) {
      return make_ufunctiontype(
          removePolarVariables(n.lhs, occMap),
          removePolarVariables(n.rhs, occMap));
    } else if constexpr (std::is_same_v<T, UUnion>) {
      auto left = removePolarVariables(n.lhs, occMap);
      auto right = removePolarVariables(n.rhs, occMap);
      // Simplify: ⊥ ∪ τ = τ
      if (std::holds_alternative<UBot>(left->v)) return right;
      if (std::holds_alternative<UBot>(right->v)) return left;
      return make_uunion(left, right);
    } else if constexpr (std::is_same_v<T, UInter>) {
      auto left = removePolarVariables(n.lhs, occMap);
      auto right = removePolarVariables(n.rhs, occMap);
      // Simplify: ⊤ ∩ τ = τ
      if (std::holds_alternative<UTop>(left->v)) return right;
      if (std::holds_alternative<UTop>(right->v)) return left;
      return make_uinter(left, right);
    } else if constexpr (std::is_same_v<T, URecordType>) {
      std::vector<std::pair<std::string, UTypePtr>> fields;
      fields.reserve(n.fields.size());
      for (const auto& [name, fieldType] : n.fields) {
        fields.emplace_back(name, removePolarVariables(fieldType, occMap));
      }
      return make_urecordtype(std::move(fields));
    } else if constexpr (std::is_same_v<T, URecursiveType>) {
      return make_urecursivetype(n.name, removePolarVariables(n.body, occMap));
    } else {
      static_assert(!sizeof(T), "Unhandled UType variant in removePolarVariables");
    }
  }, ty->v);
}

// Variable sandwich flattening (Section 4.3.1)
UTypePtr flattenVariableSandwiches(const UTypePtr& ty, const OccurrenceMap& occMap) {
  return std::visit([&](auto const& n) -> UTypePtr {
    using T = std::decay_t<decltype(n)>;
    if constexpr (std::is_same_v<T, UTop>) {
      return ty; // Top unchanged
    } else if constexpr (std::is_same_v<T, UBot>) {
      return ty; // Bot unchanged
    } else if constexpr (std::is_same_v<T, UPrimitiveType>) {
      return ty; // Primitive unchanged
    } else if constexpr (std::is_same_v<T, UTypeVariable>) {
      std::uint32_t varId = extractVariableId(n.name);
      if (varId != 0) {
        auto it = occMap.find(varId);
        if (it != occMap.end()) {
          const auto& occ = it->second;
          // If variable co-occurs with exactly one primitive both positively and negatively,
          // it's equivalent to that primitive (variable sandwich)
          if (occ.appearsPositive && occ.appearsNegative &&
              occ.coOccurs.positivePrims.size() == 1 && occ.coOccurs.negativePrims.size() == 1 &&
              *occ.coOccurs.positivePrims.begin() == *occ.coOccurs.negativePrims.begin()) {
            return make_uprimitivetype(*occ.coOccurs.positivePrims.begin());
          }
        }
      }
      return ty;
    } else if constexpr (std::is_same_v<T, UFunctionType>) {
      return make_ufunctiontype(
          flattenVariableSandwiches(n.lhs, occMap),
          flattenVariableSandwiches(n.rhs, occMap));
    } else if constexpr (std::is_same_v<T, UUnion>) {
      return make_uunion(
          flattenVariableSandwiches(n.lhs, occMap),
          flattenVariableSandwiches(n.rhs, occMap));
    } else if constexpr (std::is_same_v<T, UInter>) {
      return make_uinter(
          flattenVariableSandwiches(n.lhs, occMap),
          flattenVariableSandwiches(n.rhs, occMap));
    } else if constexpr (std::is_same_v<T, URecordType>) {
      std::vector<std::pair<std::string, UTypePtr>> fields;
      fields.reserve(n.fields.size());
      for (const auto& [name, fieldType] : n.fields) {
        fields.emplace_back(name, flattenVariableSandwiches(fieldType, occMap));
      }
      return make_urecordtype(std::move(fields));
    } else if constexpr (std::is_same_v<T, URecursiveType>) {
      return make_urecursivetype(n.name, flattenVariableSandwiches(n.body, occMap));
    } else {
      static_assert(!sizeof(T), "Unhandled UType variant in flattenVariableSandwiches");
    }
  }, ty->v);
}

// Unification of indistinguishable variables (Section 4.3.1)
UTypePtr unifyIndistinguishableVariables(const UTypePtr& ty, const OccurrenceMap& occMap) {
  // Build equivalence classes of variables that always co-occur
  std::map<std::uint32_t, std::uint32_t> representatives; // var -> representative
  
  for (const auto& [varId, occ] : occMap) {
    representatives[varId] = varId; // Initially each var represents itself
  }
  
  // Find variables that always co-occur positively AND negatively
  for (const auto& [varId, occ] : occMap) {
    for (auto otherVarId : occ.coOccurs.positiveVars) {
      auto otherIt = occMap.find(otherVarId);
      if (otherIt != occMap.end() && 
          occ.coOccurs.negativeVars.count(otherVarId) > 0) {
        // varId and otherVarId co-occur both positively and negatively
        // Unify them by using the smaller ID as representative
        std::uint32_t rep = std::min(representatives[varId], representatives[otherVarId]);
        representatives[varId] = rep;
        representatives[otherVarId] = rep;
      }
    }
  }
  
  // Apply variable substitution
  std::function<UTypePtr(const UTypePtr&)> substitute = [&](const UTypePtr& t) -> UTypePtr {
    return std::visit([&](auto const& n) -> UTypePtr {
      using T = std::decay_t<decltype(n)>;
      if constexpr (std::is_same_v<T, UTop>) {
        return t; // Top unchanged
      } else if constexpr (std::is_same_v<T, UBot>) {
        return t; // Bot unchanged
      } else if constexpr (std::is_same_v<T, UPrimitiveType>) {
        return t; // Primitive unchanged
      } else if constexpr (std::is_same_v<T, UTypeVariable>) {
        std::uint32_t varId = extractVariableId(n.name);
        if (varId != 0 && representatives.count(varId)) {
          std::uint32_t rep = representatives[varId];
          if (rep != varId) {
            return make_utypevariable("α" + std::to_string(rep));
          }
        }
        return t;
      } else if constexpr (std::is_same_v<T, UFunctionType>) {
        return make_ufunctiontype(substitute(n.lhs), substitute(n.rhs));
      } else if constexpr (std::is_same_v<T, UUnion>) {
        return make_uunion(substitute(n.lhs), substitute(n.rhs));
      } else if constexpr (std::is_same_v<T, UInter>) {
        return make_uinter(substitute(n.lhs), substitute(n.rhs));
      } else if constexpr (std::is_same_v<T, URecordType>) {
        std::vector<std::pair<std::string, UTypePtr>> fields;
        fields.reserve(n.fields.size());
        for (const auto& [name, fieldType] : n.fields) {
          fields.emplace_back(name, substitute(fieldType));
        }
        return make_urecordtype(std::move(fields));
      } else if constexpr (std::is_same_v<T, URecursiveType>) {
        return make_urecursivetype(n.name, substitute(n.body));
      } else {
        static_assert(!sizeof(T), "Unhandled UType variant in substitute");
      }
    }, t->v);
  };
  
  return substitute(ty);
}

// Hash consing implementation (Section 4.3.2)
UTypePtr hashConsType(const UTypePtr& ty, TypeHashMap& hashMap) {
  std::string hash = computeTypeHash(ty);
  
  auto it = hashMap.find(hash);
  if (it != hashMap.end()) {
    return it->second; // Return existing instance
  }
  
  // Recursively hash cons subterms first
  UTypePtr result = std::visit([&](auto const& n) -> UTypePtr {
    using T = std::decay_t<decltype(n)>;
    if constexpr (std::is_same_v<T, UTop>) {
      return ty; // Top unchanged
    } else if constexpr (std::is_same_v<T, UBot>) {
      return ty; // Bot unchanged
    } else if constexpr (std::is_same_v<T, UPrimitiveType>) {
      return ty; // Primitive unchanged
    } else if constexpr (std::is_same_v<T, UTypeVariable>) {
      return ty; // Variable unchanged
    } else if constexpr (std::is_same_v<T, UFunctionType>) {
      return make_ufunctiontype(
          hashConsType(n.lhs, hashMap),
          hashConsType(n.rhs, hashMap));
    } else if constexpr (std::is_same_v<T, UUnion>) {
      return make_uunion(
          hashConsType(n.lhs, hashMap),
          hashConsType(n.rhs, hashMap));
    } else if constexpr (std::is_same_v<T, UInter>) {
      return make_uinter(
          hashConsType(n.lhs, hashMap),
          hashConsType(n.rhs, hashMap));
    } else if constexpr (std::is_same_v<T, URecordType>) {
      std::vector<std::pair<std::string, UTypePtr>> fields;
      fields.reserve(n.fields.size());
      for (const auto& [name, fieldType] : n.fields) {
        fields.emplace_back(name, hashConsType(fieldType, hashMap));
      }
      return make_urecordtype(std::move(fields));
    } else if constexpr (std::is_same_v<T, URecursiveType>) {
      return make_urecursivetype(n.name, hashConsType(n.body, hashMap));
    } else {
      static_assert(!sizeof(T), "Unhandled UType variant in hashConsType");
    }
  }, ty->v);
  
  // Update hash after processing subterms
  hash = computeTypeHash(result);
  hashMap[hash] = result;
  return result;
}

// ======================= CompactType Implementation =======================

// Helper function to create empty CompactType
std::shared_ptr<CompactType> make_empty_compact_type() {
  auto ct = std::make_shared<CompactType>();
  ct->vars.clear();
  ct->prims.clear();
  ct->record = std::nullopt;
  ct->function = std::nullopt;
  return ct;
}

// Helper function to merge two CompactTypes based on polarity
std::shared_ptr<CompactType> merge_compact_types(bool pol, 
    const std::shared_ptr<CompactType>& lhs, 
    const std::shared_ptr<CompactType>& rhs) {
  
  auto result = std::make_shared<CompactType>();
  
  // Merge variables (always union)
  result->vars = lhs->vars;
  result->vars.insert(rhs->vars.begin(), rhs->vars.end());
  
  // Merge primitives (always union) 
  result->prims = lhs->prims;
  result->prims.insert(rhs->prims.begin(), rhs->prims.end());
  
  // Merge record types
  if (lhs->record && rhs->record) {
    auto merged_rec = std::make_shared<std::map<std::string, std::shared_ptr<CompactType>>>();
    if (pol) {
      // Positive: intersection of common fields
      for (const auto& [k, v] : *lhs->record) {
        auto it = rhs->record->find(k);
        if (it != rhs->record->end()) {
          (*merged_rec)[k] = merge_compact_types(pol, v, it->second);
        }
      }
    } else {
      // Negative: union of all fields
      *merged_rec = *lhs->record;
      for (const auto& [k, v] : *rhs->record) {
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
      merge_compact_types(pol, lhs->function->second, rhs->function->second)
    );
  } else if (lhs->function) {
    result->function = lhs->function;
  } else if (rhs->function) {
    result->function = rhs->function;
  }
  
  return result;
}

// Convert SimpleType to CompactType representation
CompactTypeScheme compactType(const SimpleType& st) {
  std::map<std::pair<VariableState*, bool>, std::uint32_t> recursive_vars; // (var, polarity) -> recursive_id
  std::map<std::uint32_t, std::shared_ptr<CompactType>> rec_vars;
  std::set<std::pair<VariableState*, bool>> in_process;
  
  std::function<std::shared_ptr<CompactType>(const SimpleType&, bool, std::set<VariableState*>&)> go;
  
  go = [&](const SimpleType& ty, bool pol, std::set<VariableState*>& parents) -> std::shared_ptr<CompactType> {
    return std::visit([&](auto const& n) -> std::shared_ptr<CompactType> {
      using T = std::decay_t<decltype(n)>;
      
      if constexpr (std::is_same_v<T, TPrimitive>) {
        auto ct = make_empty_compact_type();
        ct->prims.insert(n.name);
        return ct;
      } 
      else if constexpr (std::is_same_v<T, TFunction>) {
        auto ct = make_empty_compact_type();
        ct->function = std::make_pair(
          go(n.lhs, !pol, parents),  // contravariant
          go(n.rhs, pol, parents)    // covariant
        );
        return ct;
      }
      else if constexpr (std::is_same_v<T, TRecord>) {
        auto ct = make_empty_compact_type();
        if (!n.fields.empty()) {
          auto rec_map = std::make_shared<std::map<std::string, std::shared_ptr<CompactType>>>();
          for (const auto& [name, field_ty] : n.fields) {
            (*rec_map)[name] = go(field_ty, pol, parents);
          }
          ct->record = *rec_map;
        }
        return ct;
      }
      else if constexpr (std::is_same_v<T, TVariable>) {
        const auto& bounds = pol ? n.state->lowerBounds : n.state->upperBounds;
        auto tv_pol = std::make_pair(n.state.get(), pol);
        
        // Check for cycles
        if (in_process.contains(tv_pol)) {
          if (parents.contains(n.state.get())) {
            // Spurious cycle, return empty
            return make_empty_compact_type();
          } else {
            // Real recursive reference
            auto rec_id = recursive_vars.find(tv_pol);
            if (rec_id == recursive_vars.end()) {
              recursive_vars[tv_pol] = n.state->id;
            }
            auto ct = make_empty_compact_type();
            ct->vars.insert(recursive_vars[tv_pol]);
            return ct;
          }
        }
        
        in_process.insert(tv_pol);
        auto new_parents = parents;
        new_parents.insert(n.state.get());
        
        // Start with the variable itself
        auto result = make_empty_compact_type();
        result->vars.insert(n.state->id);
        
        // Merge with all bounds
        for (const auto& bound : bounds) {
          auto bound_compact = go(bound, pol, new_parents);
          result = merge_compact_types(pol, result, bound_compact);
        }
        
        // Handle recursive case
        auto rec_it = recursive_vars.find(tv_pol);
        if (rec_it != recursive_vars.end()) {
          rec_vars[rec_it->second] = result;
          auto ct = make_empty_compact_type();
          ct->vars.insert(rec_it->second);
          in_process.erase(tv_pol);
          return ct;
        }
        
        in_process.erase(tv_pol);
        return result;
      }
      else {
        static_assert(!sizeof(T), "Unhandled SimpleType variant in compactType");
      }
    }, ty->v);
  };
  
  std::set<VariableState*> empty_parents;
  auto compact_term = go(st, true, empty_parents);
  
  return CompactTypeScheme{compact_term, rec_vars};
}

// Convert CompactTypeScheme back to UTypePtr  
UTypePtr coalesceCompactType(const CompactTypeScheme& scheme) {
  std::map<std::pair<std::shared_ptr<CompactType>, bool>, std::string> in_process;
  
  std::function<UTypePtr(const std::shared_ptr<CompactType>&, bool)> go;
  
  go = [&](const std::shared_ptr<CompactType>& ct, bool pol) -> UTypePtr {
    auto key = std::make_pair(ct, pol);
    auto it = in_process.find(key);
    if (it != in_process.end()) {
      return make_utypevariable(it->second);
    }
    
    std::vector<UTypePtr> components;
    
    // Add type variables
    for (auto var_id : ct->vars) {
      auto rec_it = scheme.recVars.find(var_id);
      if (rec_it != scheme.recVars.end()) {
        // Recursive variable - create fresh name and recurse
        std::string rec_name = "μ" + std::to_string(var_id);
        in_process[key] = rec_name;
        auto body = go(rec_it->second, pol);
        in_process.erase(key);
        components.push_back(make_urecursivetype(rec_name, body));
      } else {
        // Regular variable
        components.push_back(make_utypevariable("α" + std::to_string(var_id)));
      }
    }
    
    // Add primitive types
    for (const auto& prim : ct->prims) {
      components.push_back(make_uprimitivetype(prim));
    }
    
    // Add record type
    if (ct->record) {
      std::vector<std::pair<std::string, UTypePtr>> fields;
      for (const auto& [name, field_ct] : *ct->record) {
        fields.emplace_back(name, go(field_ct, pol));
      }
      components.push_back(make_urecordtype(std::move(fields)));
    }
    
    // Add function type
    if (ct->function) {
      auto arg_type = go(ct->function->first, !pol);
      auto ret_type = go(ct->function->second, pol);
      components.push_back(make_ufunctiontype(arg_type, ret_type));
    }
    
    // Combine components based on polarity
    if (components.empty()) {
      return pol ? make_ubot() : make_utop();
    }
    
    UTypePtr result = components[0];
    for (size_t i = 1; i < components.size(); ++i) {
      if (pol) {
        result = make_uunion(result, components[i]);
      } else {
        result = make_uinter(result, components[i]);
      }
    }
    
    return result;
  };
  
  return go(scheme.cty, true);
}

// Main simplification function combining all strategies  
UTypePtr simplifyType(const UTypePtr& ty) {
  // Step 1: Compact type representation by merging bounds
  // This corresponds to the CompactType phase in TypeSimplifier.scala
  // We apply it conceptually by first doing co-occurrence analysis
  auto occMap = analyzeOccurrences(ty);
  
  // Step 2: Apply compact-inspired transformations first
  // Remove variables that only occur in one polarity (similar to compact's polar analysis)
  auto step1 = removePolarVariables(ty, occMap);
  
  // Step 3: Flatten variable sandwiches (this merges bounds similar to compact)
  auto step2 = flattenVariableSandwiches(step1, occMap);
  
  // Step 4: Unify indistinguishable variables (similar to compact's co-occurrence analysis)
  auto step3 = unifyIndistinguishableVariables(step2, occMap);
  
  // Step 5: Apply hash consing to remove duplicate structures
  TypeHashMap hashMap;
  auto result = hashConsType(step3, hashMap);
  
  return result;
}

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
  
  int result3 = simplesub::demo_simplification();
  if (result3 != 0) {
    std::cerr << "demo_simplification failed\n";
    return result3;
  }
  
  std::cout << "All demos passed!\n";
  return 0;
}
#endif
