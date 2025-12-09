#ifndef BINARYSUB_H
#define BINARYSUB_H

#include "binarysub-core.h"
#include "binarysub-utils.h"

#include <cassert>
#include <iostream>
#include <map>
#include <optional>
#include <string>
#include <utility>

namespace binarysub {

std::string fresh_var_name();
std::string var_id_to_name(std::uint32_t id);

// ======================= User-facing types ========================

struct UTop {};
struct UBot {};
struct UTypeVariable {
  std::string name;
};
struct UPrimitiveType {
  std::string name;
};

struct UType;
using UTypePtr = std::shared_ptr<UType>;

struct UUnion {
  UTypePtr lhs, rhs;
};
struct UInter {
  UTypePtr lhs, rhs;
};
struct UFunctionType {
  std::vector<UTypePtr> args;
  UTypePtr result;
};
struct URecordType {
  std::vector<std::pair<std::string, UTypePtr>> fields;
};
struct URecursiveType {
  std::string name;
  UTypePtr body;
};

struct UType {
  std::variant<UTop, UBot, UUnion, UInter, UFunctionType, URecordType,
               URecursiveType, UTypeVariable, UPrimitiveType>
      v;

  explicit UType(UTop t) : v(std::move(t)) {}
  explicit UType(UBot b) : v(std::move(b)) {}
  explicit UType(UUnion u) : v(std::move(u)) {}
  explicit UType(UInter i) : v(std::move(i)) {}
  explicit UType(UFunctionType f) : v(std::move(f)) {}
  explicit UType(URecordType r) : v(std::move(r)) {}
  explicit UType(URecursiveType rt) : v(std::move(rt)) {}
  explicit UType(UTypeVariable tv) : v(std::move(tv)) {}
  explicit UType(UPrimitiveType pt) : v(std::move(pt)) {}
};

// Helper functions to create UType instances
inline UTypePtr make_utop() { return std::make_shared<UType>(UTop{}); }

inline UTypePtr make_ubot() { return std::make_shared<UType>(UBot{}); }

inline UTypePtr make_uunion(UTypePtr lhs, UTypePtr rhs) {
  return std::make_shared<UType>(UUnion{std::move(lhs), std::move(rhs)});
}

inline UTypePtr make_uinter(UTypePtr lhs, UTypePtr rhs) {
  return std::make_shared<UType>(UInter{std::move(lhs), std::move(rhs)});
}

inline UTypePtr make_ufunctiontype(std::vector<UTypePtr> args,
                                   UTypePtr result) {
  return std::make_shared<UType>(
      UFunctionType{std::move(args), std::move(result)});
}

inline UTypePtr
make_urecordtype(std::vector<std::pair<std::string, UTypePtr>> fields) {
  return std::make_shared<UType>(URecordType{std::move(fields)});
}

inline UTypePtr make_urecursivetype(std::string name, UTypePtr body) {
  return std::make_shared<UType>(
      URecursiveType{std::move(name), std::move(body)});
}

inline UTypePtr make_utypevariable(std::string name) {
  return std::make_shared<UType>(UTypeVariable{std::move(name)});
}

inline UTypePtr make_uprimitivetype(std::string name) {
  return std::make_shared<UType>(UPrimitiveType{std::move(name)});
}

// Pretty printing
std::string printType(const UTypePtr &ty);
void printTypeImpl(const UTypePtr &ty, std::ostream &os, int precedence = 0);

// Normalize variable names to 'a, 'b, 'c, etc. in order of appearance
UTypePtr normalizeVariableNames(const UTypePtr &ty);

// =================== Type Simplification ===========================

// Intermediate representation for simplification (Section 4.4)
struct CompactType {
  std::set<SimpleType> vars;  // type variables
  std::set<SimpleType> prims; // primitive types
  std::optional<std::map<std::string, std::shared_ptr<CompactType>>>
      record; // record fields
  std::optional<
      std::pair<std::shared_ptr<CompactType>, std::shared_ptr<CompactType>>>
      function; // function type
};

struct CompactTypeScheme {
  std::shared_ptr<CompactType> cty;
  std::map<SimpleType, std::shared_ptr<CompactType>>
      recVars; // recursive variable bounds
};

// CompactType helper functions
inline std::shared_ptr<CompactType> make_empty_compact_type() {
  return std::make_shared<CompactType>();
}
std::shared_ptr<CompactType>
merge_compact_types(bool pol, const std::shared_ptr<CompactType> &lhs,
                    const std::shared_ptr<CompactType> &rhs);
std::string toString(const CompactType &ct);

// Co-occurrence analysis data structures
struct OccurrenceData {
  std::set<SimpleType> variables;  // Only variable types
  std::set<SimpleType> primitives; // Only primitive types
};
using OccurrenceMap = std::map<PolarVar, OccurrenceData>;
OccurrenceMap analyzeOccurrences(const CompactTypeScheme &ty);
std::string toString(const OccurrenceMap &om);

// Coalesce SimpleType to UType for display purposes
UTypePtr coalesceType(const SimpleType &st);

// Simplification functions
CompactTypeScheme compactType(const SimpleType &st);
CompactTypeScheme canonicalizeType(const SimpleType &st);
CompactTypeScheme simplifyType(const CompactTypeScheme &ty);
// Coalesces a CompactTypeScheme into a Type while performing hash-consing
UTypePtr coalesceCompactType(const CompactTypeScheme &st);

// Simplification transformations
CompactTypeScheme removePolarVariables(const CompactTypeScheme &ty,
                                       const OccurrenceMap &occMap);

// ============= Type schemes (let-polymorphism without AST) =================
struct MonoScheme {
  SimpleType body;
};

struct PolyScheme {
  int generalized_above;
  SimpleType body;
};

using TypeScheme = std::variant<MonoScheme, PolyScheme>;

SimpleType freshen_above_rec(const SimpleType &t, int cutoff, int at_level,
                             std::map<SimpleType, SimpleType> &memo,
                             VarSupply &supply);

SimpleType instantiate(const TypeScheme &sch, int at_level, VarSupply &supply);

TypeScheme generalize(const SimpleType &rhs, int env_level);

} // namespace binarysub

#endif // BINARYSUB_H
