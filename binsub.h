#ifndef BINSUB_H
#define BINSUB_H

#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <utility>
#include <variant>
#include <vector>

namespace simplesub {

// ======================= Fresh supply & scope levels =======================
struct VarSupply {
  std::uint32_t next = 0;
  std::uint32_t fresh_id();
};

struct Scope {
  int level = 0;
  void enter();
  void leave();
};

// ======================= SimpleType =============
struct TypeNode;
using SimpleType = std::shared_ptr<TypeNode>;

struct VariableState {
  std::vector<SimpleType> lowerBounds;
  std::vector<SimpleType> upperBounds;
  std::uint32_t id;
  int level;
  VariableState(std::uint32_t i, int lvl);
};

struct TPrimitive {
  std::string name;
};

struct TVariable {
  std::shared_ptr<VariableState> state;
};

struct TFunction {
  SimpleType lhs, rhs;
};

struct TRecord {
  std::vector<std::pair<std::string, SimpleType>> fields;
};

struct TypeNode {
  std::variant<TPrimitive, TVariable, TFunction, TRecord> v;
  
  explicit TypeNode(TPrimitive p);
  explicit TypeNode(TVariable v_);
  explicit TypeNode(TFunction f);
  explicit TypeNode(TRecord r);
  
  TPrimitive* getAsTPrimitive();
  const TPrimitive* getAsTPrimitive() const;
  
  TVariable* getAsTVariable();
  const TVariable* getAsTVariable() const;
  
  TFunction* getAsTFunction();
  const TFunction* getAsTFunction() const;
  
  TRecord* getAsTRecord();
  const TRecord* getAsTRecord() const;
  
  TFunction& getAsTFunctionRef();
  const TFunction& getAsTFunctionRef() const;
  
  bool isTPrimitive() const;
  bool isTVariable() const;
  bool isTFunction() const;
  bool isTRecord() const;
};

// Helper functions for type checking variant types directly
template<typename T>
constexpr bool isTPrimitiveType();

template<typename T>
constexpr bool isTVariableType();

template<typename T>
constexpr bool isTFunctionType();

template<typename T>
constexpr bool isTRecordType();

// Type creation functions
SimpleType make_primitive(std::string name);
SimpleType make_variable(std::uint32_t id, int lvl);
SimpleType fresh_variable(VarSupply &vs, int lvl);
SimpleType make_function(SimpleType a, SimpleType b);
SimpleType make_record(std::vector<std::pair<std::string, SimpleType>> fields);

// Utility functions
int level_of(const SimpleType &st);

// Forward declaration for error handling
template<typename E>
class unexpected {
public:
    unexpected(E&& error) : error_(std::move(error)) {}
    unexpected(const E& error) : error_(error) {}
    const E& error() const { return error_; }
private:
    E error_;
};

template<typename E>
unexpected<E> make_unexpected(E&& error) {
    return unexpected<E>(std::forward<E>(error));
}

template<typename T, typename E>
class expected {
public:
    expected() : has_value_(true) {}
    expected(const T& value) : has_value_(true), value_(value) {}
    
    template<typename U>
    expected(const unexpected<U>& error) : has_value_(false), error_(error.error()) {}
    
    bool has_value() const { return has_value_; }
    operator bool() const { return has_value_; }
    bool operator!() const { return !has_value_; }
    
    const T& value() const { return value_; }
    T& value() { return value_; }
    
    const E& error() const { return error_; }
    
private:
    bool has_value_;
    union {
        T value_;
        E error_;
    };
};

// Specialization for void
template<typename E>
class expected<void, E> {
public:
    expected() : has_value_(true) {}
    
    template<typename U>
    expected(const unexpected<U>& error) : has_value_(false), error_(error.error()) {}
    
    bool has_value() const { return has_value_; }
    operator bool() const { return has_value_; }
    bool operator!() const { return !has_value_; }
    
    const E& error() const { return error_; }
    
private:
    bool has_value_;
    E error_;
};

// ======================= Solver cache & error ==============================
struct Error {
  std::string msg;
  static Error make(std::string m);
};

using Cache = std::set<std::pair<const TypeNode *, const TypeNode *>>;

// ======================= Extrusion (level-fixing copy) =====================
struct PolarVS {
  VariableState *vs;
  bool pos;
  bool operator<(const PolarVS &other) const;
};

SimpleType extrude(const SimpleType &ty, bool pol, int lvl,
                   std::map<PolarVS, std::shared_ptr<VariableState>> &cache,
                   VarSupply &supply);

// ======================= Subtype constraint solver with levels =============
expected<void, Error> constrain(const SimpleType &lhs,
                                const SimpleType &rhs, 
                                Cache &cache,
                                VarSupply &supply);

expected<void, Error> constrain_impl(const SimpleType &lhs,
                                    const SimpleType &rhs,
                                    Cache &cache,
                                    VarSupply &supply);

// ============= Type schemes (let-polymorphism without AST) =================
struct MonoScheme {
  SimpleType body;
};

struct PolyScheme {
  int generalized_above;
  SimpleType body;
};

using TypeScheme = std::variant<MonoScheme, PolyScheme>;

SimpleType freshen_above_rec(const SimpleType &t, int cutoff,
                            int at_level,
                            std::map<VariableState *, SimpleType> &memo,
                            VarSupply &supply);

SimpleType instantiate(const TypeScheme &sch, int at_level,
                      VarSupply &supply);

TypeScheme generalize(const SimpleType &rhs, int env_level);

// ======================= Demo function =======================
#ifdef SIMPLESUB_DEMO
int demo_levels();
#endif

} // namespace simplesub

#endif // BINSUB_H