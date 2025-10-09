// simplesub_core.hpp
// C++23 header-only. Core Simple-sub + levels-based let polymorphism.
// No exceptions, no RTTI. Errors via std::expected.

#ifndef SIMPLESUB_CORE_HPP
#define SIMPLESUB_CORE_HPP


#include <string>
#include <vector>
#include <memory>
#include <map>
#include <set>
#include <utility>
#include <variant>
#include <optional>
#include <expected>
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <expected>

namespace simplesub {

// ======================= Fresh supply & scope levels =======================
struct VarSupply { std::uint32_t next = 0; std::uint32_t fresh_id(){ return next++; } };
struct Scope { int level = 0; void enter(){ ++level; } void leave(){ --level; } };

// ======================= SimpleType =============

struct TypeNode; using SimpleType = std::shared_ptr<TypeNode>;

struct VariableState {
  std::vector<SimpleType> lowerBounds; // things known ≤ α  (positive位)
  std::vector<SimpleType> upperBounds; // things known ≥ α  (negative位)
  std::uint32_t id;
  int level;                            // NEW: creation/generalization level
  VariableState(std::uint32_t i, int lvl) : id(i), level(lvl) {}
};

struct TPrimitive { std::string name; };
struct TVariable  { std::shared_ptr<VariableState> state; };
struct TFunction  { SimpleType lhs, rhs; };
struct TRecord    { std::vector<std::pair<std::string, SimpleType>> fields; };

struct TypeNode {
  std::variant<TPrimitive, TVariable, TFunction, TRecord> v;
  explicit TypeNode(TPrimitive p): v(std::move(p)) {}
  explicit TypeNode(TVariable v_): v(std::move(v_)) {}
  explicit TypeNode(TFunction f): v(std::move(f)) {}
  explicit TypeNode(TRecord  r): v(std::move(r)) {}
};

inline SimpleType make_primitive(std::string name) {
  return std::make_shared<TypeNode>(TPrimitive{std::move(name)});
}
inline SimpleType make_variable(std::uint32_t id, int lvl) {
  return std::make_shared<TypeNode>(TVariable{std::make_shared<VariableState>(id, lvl)});
}
inline SimpleType fresh_variable(VarSupply& vs, int lvl){
  return make_variable(vs.fresh_id(), lvl);
}
inline SimpleType make_function(SimpleType a, SimpleType b) {
  return std::make_shared<TypeNode>(TFunction{std::move(a), std::move(b)});
}
inline SimpleType make_record(std::vector<std::pair<std::string, SimpleType>> fields) {
  std::sort(fields.begin(), fields.end(), [](auto& x, auto& y){ return x.first < y.first; });
  return std::make_shared<TypeNode>(TRecord{std::move(fields)});
}

// compute the max level contained in a type (lazy in paper; direct here)  :contentReference[oaicite:3]{index=3}
inline int level_of(const SimpleType& st){
  return std::visit([](auto const& n)->int{
    using T=std::decay_t<decltype(n)>;
    if constexpr (std::is_same_v<T,TPrimitive>) return 0;
    if constexpr (std::is_same_v<T,TVariable>)  return n.state->level;
    if constexpr (std::is_same_v<T,TFunction>)  return std::max(level_of(n.lhs), level_of(n.rhs));
    if constexpr (std::is_same_v<T,TRecord>) {
      int m=0; for (auto const& [_,t]: n.fields) m = std::max(m, level_of(t)); return m;
    }
    return 0;
  }, st->v);
}

// ======================= Solver cache & error ==============================
struct Error { std::string msg; static Error make(std::string m){ return {std::move(m)}; } };

using Cache = std::set<std::pair<const TypeNode*, const TypeNode*>>;

// ======================= Extrusion (level-fixing copy) =====================
// Implements Fig. 7 in the paper. Copies a type to target level `lvl` while
// respecting polarity and caching (vs,pol) to avoid cycles.  :contentReference[oaicite:4]{index=4}
struct PolarVS { 
  VariableState* vs; 
  bool pos; 
  bool operator<(const PolarVS& other) const {
    if (vs != other.vs) return vs < other.vs;
    return pos < other.pos;
  }
};
inline SimpleType extrude(const SimpleType& ty, bool pol, int lvl,
                          std::map<PolarVS, std::shared_ptr<VariableState>>& cache,
                          VarSupply& supply);

inline SimpleType extrude(const SimpleType& ty, bool pol, int lvl,
                          std::map<PolarVS, std::shared_ptr<VariableState>>& cache,
                          VarSupply& supply)
{
  if (level_of(ty) <= lvl) return ty;

  if (auto p = std::get_if<TPrimitive>(&ty->v)) return ty;

  if (auto f = std::get_if<TFunction>(&ty->v)) {
    auto l = extrude(f->lhs, !pol, lvl, cache, supply);
    auto r = extrude(f->rhs,  pol, lvl, cache, supply);
    return make_function(std::move(l), std::move(r));
  }

  if (auto r = std::get_if<TRecord>(&ty->v)) {
    std::vector<std::pair<std::string, SimpleType>> fs; fs.reserve(r->fields.size());
    for (auto const& [n,t] : r->fields) {
      fs.emplace_back(n, extrude(t, pol, lvl, cache, supply));
    }
    return make_record(std::move(fs));
  }

  auto v = std::get_if<TVariable>(&ty->v);
  assert(v);

  PolarVS key{v->state.get(), pol};
  if (auto it = cache.find(key); it != cache.end()) {
    return std::make_shared<TypeNode>(TVariable{it->second});
  }

  // Make a copy at requested level
  auto nvs = std::make_shared<VariableState>(supply.fresh_id(), lvl);
  cache.emplace(key, nvs);

  if (pol) {
    // positive: copy lowers to the new var; old var upper-bounds include the new var
    v->state->upperBounds.push_back(std::make_shared<TypeNode>(TVariable{nvs}));
    nvs->lowerBounds.reserve(v->state->lowerBounds.size());
    for (auto const& lb : v->state->lowerBounds)
      nvs->lowerBounds.push_back(extrude(lb, pol, lvl, cache, supply));
  } else {
    // negative: copy uppers to the new var; old var lower-bounds include the new var
    v->state->lowerBounds.push_back(std::make_shared<TypeNode>(TVariable{nvs}));
    nvs->upperBounds.reserve(v->state->upperBounds.size());
    for (auto const& ub : v->state->upperBounds)
      nvs->upperBounds.push_back(extrude(ub, pol, lvl, cache, supply));
  }
  return std::make_shared<TypeNode>(TVariable{nvs});
}

// ======================= Subtype constraint solver with levels =============
// Full spec with level guards + extrusion (Fig. 9).  :contentReference[oaicite:5]{index=5}
inline std::expected<void, Error>
constrain_impl(const SimpleType& lhs, const SimpleType& rhs, Cache& cache, VarSupply& supply);

inline std::expected<void, Error>
constrain(const SimpleType& lhs, const SimpleType& rhs, Cache& cache, VarSupply& supply) {
  auto key = std::make_pair(lhs.get(), rhs.get());
  if (cache.contains(key)) return {};
  cache.insert(key);
  return constrain_impl(lhs, rhs, cache, supply);
}

inline std::expected<void, Error>
constrain_impl(const SimpleType& lhs, const SimpleType& rhs, Cache& cache, VarSupply& supply){
  if (auto lp = std::get_if<TPrimitive>(&lhs->v)) {
    if (auto rp = std::get_if<TPrimitive>(&rhs->v)) {
      if (lp->name == rp->name) return {}; else
        return std::unexpected(Error::make("primitive mismatch: "+lp->name+" </: "+rp->name));
    }
  }

  if (auto lf = std::get_if<TFunction>(&lhs->v)) if (auto rf = std::get_if<TFunction>(&rhs->v)){
    if (auto e = constrain(rf->lhs, lf->lhs, cache, supply); !e) return e;
    if (auto e = constrain(lf->rhs, rf->rhs, cache, supply); !e) return e;
    return {};
  }

  if (auto lr = std::get_if<TRecord>(&lhs->v)) if (auto rr = std::get_if<TRecord>(&rhs->v)){
    std::map<std::string, SimpleType> fmap;
    for (auto const& [n,t] : lr->fields) fmap[n]=t;
    for (auto const& [n_req, t_req] : rr->fields) {
      auto it=fmap.find(n_req);
      if (it==fmap.end()) return std::unexpected(Error::make("missing field: "+n_req));
      if (auto e = constrain(it->second, t_req, cache, supply); !e) return e;
    }
    return {};
  }

  if (auto lv = std::get_if<TVariable>(&lhs->v)) {
    // guard: only allow rhs to flow into α if rhs.level <= α.level
    if (level_of(rhs) <= lv->state->level) {
      lv->state->upperBounds.push_back(rhs);
      for (auto const& lb : lv->state->lowerBounds)
        if (auto e = constrain(lb, rhs, cache, supply); !e) return e;
      return {};
    }
    // else extrude rhs down to lhs.level (negative polarity) and retry  :contentReference[oaicite:6]{index=6}
    std::map<PolarVS, std::shared_ptr<VariableState>> ex;
    auto rhs_ex = extrude(rhs, /*pol=*/false, lv->state->level, ex, supply);
    return constrain(lhs, rhs_ex, cache, supply);
  }

  if (auto rv = std::get_if<TVariable>(&rhs->v)) {
    if (level_of(lhs) <= rv->state->level) {
      rv->state->lowerBounds.push_back(lhs);
      for (auto const& ub : rv->state->upperBounds)
        if (auto e = constrain(lhs, ub, cache, supply); !e) return e;
      return {};
    }
    // else extrude lhs down to rhs.level (positive polarity) and retry  :contentReference[oaicite:7]{index=7}
    std::map<PolarVS, std::shared_ptr<VariableState>> ex;
    auto lhs_ex = extrude(lhs, /*pol=*/true, rv->state->level, ex, supply);
    return constrain(lhs_ex, rhs, cache, supply);
  }

  return std::unexpected(Error::make("cannot constrain given pair"));
}

// ======================= User-facing algebraic types & coalescing =========
// (unchanged from previous version, omitted here for brevity in this excerpt)
// -- keep your existing UType, coalesceType, printU implementation --

// ============= Type schemes (let-polymorphism without AST) =================
// Matches Fig. 6: SimpleType <: TypeScheme; PolymorphicType(level, body).  :contentReference[oaicite:8]{index=8}
struct MonoScheme { SimpleType body; };
struct PolyScheme  { int generalized_above; SimpleType body; };

using TypeScheme = std::variant<MonoScheme, PolyScheme>;

inline SimpleType freshen_above_rec(const SimpleType& t, int cutoff, int at_level,
                                    std::map<VariableState*, SimpleType>& memo,
                                    VarSupply& supply)
{
  return std::visit([&](auto const& n)->SimpleType{
    using T=std::decay_t<decltype(n)>;
    if constexpr (std::is_same_v<T,TPrimitive>) return t;
    if constexpr (std::is_same_v<T,TFunction>)
      return make_function(freshen_above_rec(n.lhs, cutoff, at_level, memo, supply),
                           freshen_above_rec(n.rhs, cutoff, at_level, memo, supply));
    if constexpr (std::is_same_v<T,TRecord>){
      std::vector<std::pair<std::string, SimpleType>> fs; fs.reserve(n.fields.size());
      for (auto const& [name, sub] : n.fields)
        fs.emplace_back(name, freshen_above_rec(sub, cutoff, at_level, memo, supply));
      return make_record(std::move(fs));
    }
    // TVariable
    auto* vs = n.state.get();
    if (vs->level > cutoff) {
      if (auto it = memo.find(vs); it != memo.end()) return it->second;
      auto fresh = fresh_variable(supply, at_level); // empty bounds, new id/level
      memo.emplace(vs, fresh);
      return fresh;
    }
    return t;
  }, t->v);
}

inline SimpleType instantiate(const TypeScheme& sch, int at_level, VarSupply& supply){
  if (auto m = std::get_if<MonoScheme>(&sch)) return m->body;
  auto const& p = std::get<PolyScheme>(sch);
  std::map<VariableState*, SimpleType> memo;
  return freshen_above_rec(p.body, p.generalized_above, at_level, memo, supply); // :contentReference[oaicite:9]{index=9}
}

// Helper to wrap a rhs type at let generalization point
inline TypeScheme generalize(const SimpleType& rhs, int env_level){
  return PolyScheme{env_level, rhs};
}

// ======================= Tiny demo (no AST, just constraints) ==============
#ifdef SIMPLESUB_DEMO
// Demo: let id = \x. x in (id : int->int) & (id : bool->bool)
// We build constraints by手工：应用时把实参 <: 形参，结果取返回。
inline int demo_levels(){
  VarSupply supply;
  Scope env; // level=0

  // Build the rhs of "id": α -> α  at level (env.level+1)
  env.enter(); // enter let-rhs
  auto a = fresh_variable(supply, env.level); // level=1
  auto id_ty = make_function(a, a);
  env.leave();

  // Generalize id at env.level (0)
  TypeScheme id_scheme = generalize(id_ty, /*env_level*/0);

  // Two uses at current level=0: instantiate twice (freshenAbove)
  auto id1 = instantiate(id_scheme, env.level, supply);
  auto id2 = instantiate(id_scheme, env.level, supply);

  // Build primitives
  auto TInt  = make_primitive("int");
  auto TBool = make_primitive("bool");

  // For application: (int) <: dom(id1)  && cod(id1) <: int   (simulates id 1)
  // and similarly for bool on id2.
  Cache cache;
  // id1 is α1→α1
  auto d1 = std::get<TFunction>(id1->v).lhs;
  auto r1 = std::get<TFunction>(id1->v).rhs;
  auto d2 = std::get<TFunction>(id2->v).lhs;
  auto r2 = std::get<TFunction>(id2->v).rhs;

  if (auto e = constrain(TInt, d1, cache, supply); !e) { std::cerr<<e.error().msg<<"\n"; return 1; }
  if (auto e = constrain(r1, TInt, cache, supply); !e) { std::cerr<<e.error().msg<<"\n"; return 1; }
  if (auto e = constrain(TBool, d2, cache, supply); !e){ std::cerr<<e.error().msg<<"\n"; return 1; }
  if (auto e = constrain(r2, TBool, cache, supply); !e){ std::cerr<<e.error().msg<<"\n"; return 1; }

  // 现在 id 两次使用互不干扰（得到各自的 α1(int)、α2(bool)）
  std::cout << "Let-polymorphic id instantiated twice without interference.\n";
  return 0;
}
#endif

} // namespace simplesub

#endif // SIMPLESUB_CORE_HPP

#ifdef SIMPLESUB_DEMO
int main(){ return simplesub::demo_levels(); }
#endif
