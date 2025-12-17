#ifndef BINARYSUB_CORE_CMP_H
#define BINARYSUB_CORE_CMP_H

#include "binarysub-core.h"

namespace binarysub {

// ======================= Comparison operators for types ===================

// Forward declaration for recursive comparison
inline bool compareSimpleType(const SimpleType &lhs, const SimpleType &rhs);

inline bool TFunction::operator<(const TFunction &other) const {
  // Compare argument count first
  if (args.size() != other.args.size()) {
    return args.size() < other.args.size();
  }
  // Compare arguments
  for (size_t i = 0; i < args.size(); ++i) {
    if (compareSimpleType(args[i], other.args[i])) {
      return true;
    }
    if (compareSimpleType(other.args[i], args[i])) {
      return false;
    }
  }
  // Compare result
  return compareSimpleType(result, other.result);
}

inline bool TRecord::operator<(const TRecord &other) const {
  // Compare field count first
  if (fields.size() != other.fields.size()) {
    return fields.size() < other.fields.size();
  }
  // Compare fields
  for (size_t i = 0; i < fields.size(); ++i) {
    const auto &lhs_field = fields[i];
    const auto &rhs_field = other.fields[i];
    if (lhs_field.first != rhs_field.first) {
      return lhs_field.first < rhs_field.first;
    }
    if (compareSimpleType(lhs_field.second, rhs_field.second)) {
      return true;
    }
    if (compareSimpleType(rhs_field.second, lhs_field.second)) {
      return false;
    }
  }
  return false;
}

inline bool TypeNode::operator<(const TypeNode &other) const {
  // Get the variant indices to compare type categories first
  auto lhs_idx = v.index();
  auto rhs_idx = other.v.index();

  if (lhs_idx != rhs_idx) {
    return lhs_idx < rhs_idx;
  }

  // Both have the same variant type, compare contents
  if (const auto *lhs_prim = getAsTPrimitive()) {
    const auto *rhs_prim = other.getAsTPrimitive();
    return *lhs_prim < *rhs_prim;
  } else if (const auto *lhs_var = getAsVariableState()) {
    const auto *rhs_var = other.getAsVariableState();
    return *lhs_var < *rhs_var;
  } else if (const auto *lhs_func = getAsTFunction()) {
    const auto *rhs_func = other.getAsTFunction();
    return *lhs_func < *rhs_func;
  } else if (const auto *lhs_rec = getAsTRecord()) {
    const auto *rhs_rec = other.getAsTRecord();
    return *lhs_rec < *rhs_rec;
  } else {
    // Should not happen - all cases covered
    static_assert(std::variant_size_v<decltype(TypeNode::v)> == 4,
                  "TypeNode variant has unexpected number of alternatives");
    return false;
  }
}

inline bool compareSimpleType(const SimpleType &lhs, const SimpleType &rhs) {
  // Handle null pointers
  if (!lhs && !rhs)
    return false;
  if (!lhs)
    return true;
  if (!rhs)
    return false;

  return *lhs < *rhs;
}

// Custom comparator for SimpleType that compares by value instead of pointer
// address
struct SimpleTypeValueCompare {
  bool operator()(const SimpleType &lhs, const SimpleType &rhs) const {
    return compareSimpleType(lhs, rhs);
  }
};

using SimpleTypeSet = std::set<SimpleType, SimpleTypeValueCompare>;

} // namespace binarysub

#endif
