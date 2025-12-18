#ifndef BINARYSUB_CORE_H
#define BINARYSUB_CORE_H

#include "binarysub-utils.h"

#include <cassert>
#include <map>
#include <memory>
#include <set>
#include <tuple>
#include <variant>
#include <vector>

namespace binarysub {

// ======================= Fresh supply & scope levels =======================
struct VarSupply {
  std::uint32_t next = 0;
  std::uint32_t fresh_id() { return next++; };
};

// Global variable supply
extern VarSupply globalVarSupply;

struct Scope {
  int level = 0;
  void enter() { ++level; };
  void leave() { --level; };
};

// ======================= SimpleType =============
struct TypeNode;
using SimpleType = value_ptr<TypeNode>;

// Convert a variable ID to a letter-based name
inline std::string var_id_to_name(std::uint32_t id) {
  std::uint32_t letter_idx = id % 26;
  std::uint32_t suffix = id / 26;

  std::string name = "'";
  name += static_cast<char>('a' + letter_idx);
  if (suffix > 0) {
    name += std::to_string(suffix);
  }
  return name;
}

struct VariableState {
  std::vector<SimpleType> lowerBounds;
  std::vector<SimpleType> upperBounds;
  std::uint32_t id;
  int level;
  VariableState(std::uint32_t i, int lvl) : id(i), level(lvl) {};

  bool operator<(const VariableState &other) const {
    if (id != other.id)
      return id < other.id;
    return level < other.level;
  }
  bool operator==(const VariableState &other) const {
    return !(*this < other) && !(other < *this);
  }
  bool operator!=(const VariableState &other) const { return !(*this == other); }
  std::string name() const {
    return var_id_to_name(id);
  }
};

struct TPrimitive {
  std::string name;

  bool operator<(const TPrimitive &other) const { return name < other.name; }
  bool operator==(const TPrimitive &other) const {
    return !(*this < other) && !(other < *this);
  }
  bool operator!=(const TPrimitive &other) const { return !(*this == other); }
};

struct TFunction {
  std::vector<SimpleType> args;
  SimpleType result;

  bool operator<(const TFunction &other) const;
  bool operator==(const TFunction &other) const {
    return !(*this < other) && !(other < *this);
  }
  bool operator!=(const TFunction &other) const { return !(*this == other); }
};

struct TRecord {
  std::vector<std::pair<std::string, SimpleType>> fields;

  bool operator<(const TRecord &other) const;
  bool operator==(const TRecord &other) const {
    return !(*this < other) && !(other < *this);
  }
  bool operator!=(const TRecord &other) const { return !(*this == other); }
};

struct TypeNode {
  std::variant<TPrimitive, VariableState, TFunction, TRecord> v;

  explicit TypeNode(TPrimitive p) : v(std::move(p)) {}
  explicit TypeNode(VariableState vs) : v(std::move(vs)) {}
  explicit TypeNode(TFunction f) : v(std::move(f)) {}
  explicit TypeNode(TRecord r) : v(std::move(r)) {}

  TPrimitive *getAsTPrimitive() { return std::get_if<TPrimitive>(&v); }
  const TPrimitive *getAsTPrimitive() const {
    return std::get_if<TPrimitive>(&v);
  }

  VariableState *getAsVariableState() { return std::get_if<VariableState>(&v); }
  const VariableState *getAsVariableState() const {
    return std::get_if<VariableState>(&v);
  }

  TFunction *getAsTFunction() { return std::get_if<TFunction>(&v); }
  const TFunction *getAsTFunction() const { return std::get_if<TFunction>(&v); }

  TRecord *getAsTRecord() { return std::get_if<TRecord>(&v); }
  const TRecord *getAsTRecord() const { return std::get_if<TRecord>(&v); }

  TFunction &getAsTFunctionRef() { return std::get<TFunction>(v); }
  const TFunction &getAsTFunctionRef() const { return std::get<TFunction>(v); }

  bool isTPrimitive() const { return std::holds_alternative<TPrimitive>(v); }
  bool isVariableState() const {
    return std::holds_alternative<VariableState>(v);
  }
  bool isTFunction() const { return std::holds_alternative<TFunction>(v); }
  bool isTRecord() const { return std::holds_alternative<TRecord>(v); }

  bool operator<(const TypeNode &other) const;
  bool operator==(const TypeNode &other) const {
    return !(*this < other) && !(other < *this);
  }
  bool operator!=(const TypeNode &other) const { return !(*this == other); }
};

// Type creation functions

// Type creation functions
inline SimpleType make_primitive(std::string name) {
  return make_value_ptr<TypeNode>(TPrimitive{std::move(name)});
}

inline SimpleType make_variable(int lvl) {
  return make_value_ptr<TypeNode>(VariableState(globalVarSupply.fresh_id(), lvl));
}

inline SimpleType fresh_variable(int lvl) {
  return make_variable(lvl);
}

inline SimpleType make_function(std::vector<SimpleType> args,
                                SimpleType result) {
  return make_value_ptr<TypeNode>(
      TFunction{std::move(args), std::move(result)});
}

inline SimpleType make_function(SimpleType a, SimpleType b) {
  std::vector<SimpleType> args;
  args.push_back(std::move(a));
  return make_function(std::move(args), std::move(b));
}

inline SimpleType
make_record(std::vector<std::pair<std::string, SimpleType>> fields) {
  std::sort(fields.begin(), fields.end(),
            [](auto &x, auto &y) { return x.first < y.first; });
  return make_value_ptr<TypeNode>(TRecord{std::move(fields)});
}

// Utility functions
// Helper function to safely extract VariableState* from SimpleType
inline VariableState *extractVariableState(const SimpleType &st) {
  auto vs = st->getAsVariableState();
  assert(vs && "SimpleType must contain VariableState");
  return vs;
}
// compute the max level contained in a type (lazy in paper; direct here)
int level_of(const SimpleType &st);

// =====================================================================

using Cache = std::set<std::pair<const TypeNode *, const TypeNode *>>;

// ======================= Subtype constraint solver with levels =============
expected<void, Error> constrain(const SimpleType &lhs, const SimpleType &rhs,
                                Cache &cache);

expected<void, Error> constrain_impl(const SimpleType &lhs,
                                     const SimpleType &rhs, Cache &cache);

// ======================= Extrusion (level-fixing copy) =====================
struct PolarVar {
  SimpleType var;
  bool pos;
  bool operator<(const PolarVar &other) const {
    return std::tie(var, pos) < std::tie(other.var, other.pos);
  }
};

// make a copy of the problematic type such that the copy has the requested
// level and soundly approximates the original type.
SimpleType extrude(const SimpleType &ty, bool pol, int lvl,
                   std::map<PolarVar, SimpleType> &cache);

} // namespace binarysub

#endif
