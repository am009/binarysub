#include "binarysub.h"
#include <functional>
#include <numeric>
#include <sstream>

namespace binarysub {

// ======================= User-facing algebraic types & coalescing =========

// Generate unique variable names
static std::uint32_t var_name_counter = 0;
std::string fresh_var_name() {
  // Generate names like 'a, 'b, 'c, ..., 'z, 'a1, 'b1, etc.
  std::uint32_t idx = var_name_counter++;
  std::uint32_t letter_idx = idx % 26;
  std::uint32_t suffix = idx / 26;

  std::string name = "'";
  name += static_cast<char>('a' + letter_idx);
  if (suffix > 0) {
    name += std::to_string(suffix);
  }
  return name;
}

// Convert a variable ID to a letter-based name
std::string var_id_to_name(std::uint32_t id) {
  std::uint32_t letter_idx = id % 26;
  std::uint32_t suffix = id / 26;

  std::string name = "'";
  name += static_cast<char>('a' + letter_idx);
  if (suffix > 0) {
    name += std::to_string(suffix);
  }
  return name;
}

// Pretty printing implementation
std::string printType(const UTypePtr &ty) {
  std::ostringstream oss;
  printTypeImpl(ty, oss, 0);
  return oss.str();
}

// Normalize variable names to 'a, 'b, 'c, etc. in order of appearance
UTypePtr normalizeVariableNames(const UTypePtr &ty) {
  // First pass: collect all variable names in order of appearance
  std::vector<std::string> varOrder;
  std::set<std::string> seenVars;

  std::function<void(const UTypePtr &)> collectVars = [&](const UTypePtr &t) {
    std::visit(
        [&](auto const &n) {
          using T = std::decay_t<decltype(n)>;
          if constexpr (std::is_same_v<T, UTypeVariable>) {
            if (seenVars.find(n.name) == seenVars.end()) {
              seenVars.insert(n.name);
              varOrder.push_back(n.name);
            }
          } else if constexpr (std::is_same_v<T, UFunctionType>) {
            for (const auto &arg : n.args) {
              collectVars(arg);
            }
            collectVars(n.result);
          } else if constexpr (std::is_same_v<T, UUnion>) {
            collectVars(n.lhs);
            collectVars(n.rhs);
          } else if constexpr (std::is_same_v<T, UInter>) {
            collectVars(n.lhs);
            collectVars(n.rhs);
          } else if constexpr (std::is_same_v<T, URecordType>) {
            for (const auto &[_, fieldType] : n.fields) {
              collectVars(fieldType);
            }
          } else if constexpr (std::is_same_v<T, URecursiveType>) {
            collectVars(n.body);
          }
        },
        t->v);
  };

  collectVars(ty);

  // Create mapping from old names to new names
  std::map<std::string, std::string> nameMap;
  for (size_t i = 0; i < varOrder.size(); i++) {
    std::uint32_t letter_idx = i % 26;
    std::uint32_t suffix = i / 26;
    std::string newName = "'";
    newName += static_cast<char>('a' + letter_idx);
    if (suffix > 0) {
      newName += std::to_string(suffix);
    }
    nameMap[varOrder[i]] = newName;
  }

  // Second pass: replace all variable names
  std::function<UTypePtr(const UTypePtr &)> renameVars =
      [&](const UTypePtr &t) -> UTypePtr {
    return std::visit(
        [&](auto const &n) -> UTypePtr {
          using T = std::decay_t<decltype(n)>;
          if constexpr (std::is_same_v<T, UTop>) {
            return make_utop();
          } else if constexpr (std::is_same_v<T, UBot>) {
            return make_ubot();
          } else if constexpr (std::is_same_v<T, UPrimitiveType>) {
            return make_uprimitivetype(n.name);
          } else if constexpr (std::is_same_v<T, UTypeVariable>) {
            auto it = nameMap.find(n.name);
            if (it != nameMap.end()) {
              return make_utypevariable(it->second);
            }
            return make_utypevariable(n.name);
          } else if constexpr (std::is_same_v<T, UFunctionType>) {
            std::vector<UTypePtr> newArgs;
            for (const auto &arg : n.args) {
              newArgs.push_back(renameVars(arg));
            }
            return make_ufunctiontype(std::move(newArgs), renameVars(n.result));
          } else if constexpr (std::is_same_v<T, UUnion>) {
            return make_uunion(renameVars(n.lhs), renameVars(n.rhs));
          } else if constexpr (std::is_same_v<T, UInter>) {
            return make_uinter(renameVars(n.lhs), renameVars(n.rhs));
          } else if constexpr (std::is_same_v<T, URecordType>) {
            std::vector<std::pair<std::string, UTypePtr>> newFields;
            for (const auto &[name, fieldType] : n.fields) {
              newFields.emplace_back(name, renameVars(fieldType));
            }
            return make_urecordtype(std::move(newFields));
          } else if constexpr (std::is_same_v<T, URecursiveType>) {
            return make_urecursivetype(n.name, renameVars(n.body));
          } else {
            static_assert(!sizeof(T),
                          "Unhandled UType variant in normalizeVariableNames");
          }
        },
        t->v);
  };

  return renameVars(ty);
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

          // Print curried function: arg1 -> arg2 -> ... -> result
          if (n.args.empty()) {
            os << "() -> ";
          } else {
            for (size_t i = 0; i < n.args.size(); ++i) {
              printTypeImpl(n.args[i], os, 2);
              os << " -> ";
            }
          }
          printTypeImpl(n.result, os, 1);

          if (needParens)
            os << ")";
        } else if constexpr (std::is_same_v<T, UUnion>) {
          bool needParens = precedence > 3;
          if (needParens)
            os << "(";
          printTypeImpl(n.lhs, os, 4);
          os << " | ";
          printTypeImpl(n.rhs, os, 3);
          if (needParens)
            os << ")";
        } else if constexpr (std::is_same_v<T, UInter>) {
          bool needParens = precedence > 4;
          if (needParens)
            os << "(";
          printTypeImpl(n.lhs, os, 5);
          os << " & ";
          printTypeImpl(n.rhs, os, 4);
          if (needParens)
            os << ")";
        } else if constexpr (std::is_same_v<T, URecordType>) {
          os << "{";
          for (size_t i = 0; i < n.fields.size(); ++i) {
            if (i > 0)
              os << ", ";
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
                             std::map<SimpleType, SimpleType> &memo) {
  if (t->isTPrimitive()) {
    return t;
  } else if (auto n = t->getAsTFunction()) {
    std::vector<SimpleType> args;
    args.reserve(n->args.size());
    for (auto const &a : n->args)
      args.push_back(freshen_above_rec(a, cutoff, at_level, memo));
    return make_function(
        std::move(args),
        freshen_above_rec(n->result, cutoff, at_level, memo));
  } else if (auto n = t->getAsTRecord()) {
    std::vector<std::pair<std::string, SimpleType>> fs;
    fs.reserve(n->fields.size());
    for (auto const &[name, sub] : n->fields)
      fs.emplace_back(name,
                      freshen_above_rec(sub, cutoff, at_level, memo));
    return make_record(std::move(fs));
  } else if (auto n = t->getAsVariableState()) {
    // VariableState
    if (n->level > cutoff) {
      if (auto it = memo.find(t); it != memo.end())
        return it->second;
      auto fresh =
          fresh_variable(at_level); // empty bounds, new id/level
      memo.emplace(t, fresh);
      return fresh;
    }
    return t;
  } else {
    assert(false && "Unhandled variant type in freshen_above_rec");
  }
}

SimpleType instantiate(const TypeScheme &sch, int at_level) {
  if (auto m = std::get_if<MonoScheme>(&sch))
    return m->body;
  auto const &p = std::get<PolyScheme>(sch);
  std::map<SimpleType, SimpleType> memo;
  return freshen_above_rec(p.body, p.generalized_above, at_level, memo);
}

// Helper to wrap a rhs type at let generalization point
TypeScheme generalize(const SimpleType &rhs, int env_level) {
  return PolyScheme{env_level, rhs};
}

// =================== Type Simplification Implementation
// ===========================

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

bool CompactType::operator<(const CompactType &other) const {
  // Compare vars first
  if (vars < other.vars) {
    return true;
  }
  if (other.vars < vars) {
    return false;
  }

  // Compare prims
  if (prims < other.prims) {
    return true;
  }
  if (other.prims < prims) {
    return false;
  }

  // Compare record
  if (!record && other.record)
    return true;
  if (record && !other.record)
    return false;

  if (record && other.record) {
    auto it1 = record->begin();
    auto it2 = other.record->begin();
    auto end1 = record->end();
    auto end2 = other.record->end();

    while (it1 != end1 && it2 != end2) {
      // Compare keys
      if (it1->first < it2->first)
        return true;
      if (it2->first < it1->first)
        return false;

      // Keys equal, compare values (dereference shared_ptrs)
      if (*it1->second < *it2->second)
        return true;
      if (*it2->second < *it1->second)
        return false;

      ++it1;
      ++it2;
    }

    // If one map is a prefix of the other
    if (it1 == end1 && it2 != end2)
      return true;
    if (it1 != end1 && it2 == end2)
      return false;
  }

  // Compare function
  if (!function && other.function)
    return true;
  if (function && !other.function)
    return false;

  if (function && other.function) {
    const auto &args1 = function->first;
    const auto &args2 = other.function->first;

    // Compare argument counts
    if (args1.size() < args2.size())
      return true;
    if (args1.size() > args2.size())
      return false;

    // Compare arguments element by element
    for (size_t i = 0; i < args1.size(); ++i) {
      if (*args1[i] < *args2[i])
        return true;
      if (*args2[i] < *args1[i])
        return false;
    }

    // Compare result types
    if (*function->second < *other.function->second)
      return true;
    if (*other.function->second < *function->second)
      return false;
  }

  // All fields are equal
  return false;
}

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
    // Merge argument vectors element-wise
    std::vector<std::shared_ptr<CompactType>> mergedArgs;
    size_t maxArgs =
        std::max(lhs->function->first.size(), rhs->function->first.size());
    for (size_t i = 0; i < maxArgs; ++i) {
      if (i < lhs->function->first.size() && i < rhs->function->first.size()) {
        mergedArgs.push_back(merge_compact_types(!pol, lhs->function->first[i],
                                                 rhs->function->first[i]));
      } else if (i < lhs->function->first.size()) {
        mergedArgs.push_back(lhs->function->first[i]);
      } else {
        mergedArgs.push_back(rhs->function->first[i]);
      }
    }
    result->function = std::make_pair(
        mergedArgs,
        merge_compact_types(pol, lhs->function->second, rhs->function->second));
  } else if (lhs->function) {
    result->function = lhs->function;
  } else if (rhs->function) {
    result->function = rhs->function;
  }

  return result;
}

std::string toString(const CompactType &ct) {
  std::ostringstream oss;

  std::vector<std::string> components;

  // Add variables
  if (!ct.vars.empty()) {
    std::vector<std::string> varNames;
    for (const auto &var : ct.vars) {
      if (auto vs = var->getAsVariableState()) {
        varNames.push_back(var_id_to_name(vs->id));
      }
    }
    if (!varNames.empty()) {
      if (varNames.size() == 1) {
        components.push_back(varNames[0]);
      } else {
        components.push_back(
            "{" +
            std::accumulate(varNames.begin(), varNames.end(), std::string(),
                            [](const std::string &a, const std::string &b) {
                              return a.empty() ? b : a + ", " + b;
                            }) +
            "}");
      }
    }
  }

  // Add primitives
  if (!ct.prims.empty()) {
    std::vector<std::string> primNames;
    for (const auto &prim : ct.prims) {
      if (auto p = prim->getAsTPrimitive()) {
        primNames.push_back(p->name);
      }
    }
    if (!primNames.empty()) {
      if (primNames.size() == 1) {
        components.push_back(primNames[0]);
      } else {
        components.push_back(
            "{" +
            std::accumulate(primNames.begin(), primNames.end(), std::string(),
                            [](const std::string &a, const std::string &b) {
                              return a.empty() ? b : a + ", " + b;
                            }) +
            "}");
      }
    }
  }

  // Add record type
  if (ct.record && !ct.record->empty()) {
    std::ostringstream recordOss;
    recordOss << "{";
    bool first = true;
    for (const auto &[fieldName, fieldType] : *ct.record) {
      if (!first)
        recordOss << "; ";
      recordOss << fieldName << ": " << toString(*fieldType);
      first = false;
    }
    recordOss << "}";
    components.push_back(recordOss.str());
  }

  // Add function type
  if (ct.function) {
    std::ostringstream funOss;
    funOss << "(";
    for (size_t i = 0; i < ct.function->first.size(); ++i) {
      if (i > 0)
        funOss << ", ";
      funOss << toString(*ct.function->first[i]);
    }
    funOss << " → " << toString(*ct.function->second) << ")";
    components.push_back(funOss.str());
  }

  // Combine components
  if (components.empty()) {
    return "⊥"; // Empty type
  } else if (components.size() == 1) {
    return components[0];
  } else {
    // Multiple components - combine with union
    return std::accumulate(components.begin(), components.end(), std::string(),
                           [](const std::string &a, const std::string &b) {
                             return a.empty() ? b : a + " ∪ " + b;
                           });
  }
}

std::string toString(const OccurrenceMap &om) {
  if (om.empty()) {
    return "{}";
  }

  std::ostringstream oss;
  oss << "{";
  bool first = true;

  for (const auto &[polarVar, occData] : om) {
    if (!first) {
      oss << ", ";
    }

    // Format the PolarVar
    auto var_ptr = extractVariableState(polarVar.var);
    oss << var_id_to_name(var_ptr->id) << (polarVar.pos ? "⁺" : "⁻");
    oss << " -> {vars: {";

    // Format the variable set
    bool firstVar = true;
    for (const auto &var : occData.variables) {
      if (!firstVar) {
        oss << ", ";
      }

      if (auto vs = var->getAsVariableState()) {
        oss << var_id_to_name(vs->id);
      } else {
        oss << "?var"; // fallback
      }
      firstVar = false;
    }

    oss << "}, prims: {";

    // Format the primitive set
    bool firstPrim = true;
    for (const auto &prim : occData.primitives) {
      if (!firstPrim) {
        oss << ", ";
      }

      if (auto p = prim->getAsTPrimitive()) {
        oss << p->name;
      } else {
        oss << "?prim"; // fallback
      }
      firstPrim = false;
    }

    oss << "}}";
    first = false;
  }

  oss << "}";
  return oss.str();
}

// Coalesce SimpleType to UType for display purposes
UTypePtr coalesceType(const SimpleType &st) {
  struct PairComparator {
    bool operator()(const std::pair<SimpleType, bool> &lhs,
                    const std::pair<SimpleType, bool> &rhs) const {
      auto lhs_var = extractVariableState(lhs.first);
      auto rhs_var = extractVariableState(rhs.first);
      if (lhs_var != rhs_var)
        return lhs_var < rhs_var;
      return lhs.second < rhs.second;
    }
  };

  std::map<std::pair<SimpleType, bool>, std::string, PairComparator> recursive;
  static std::uint32_t recVarCounter = 0;

  std::function<UTypePtr(
      const SimpleType &, bool,
      std::set<std::pair<SimpleType, bool>, PairComparator> &)>
      go = [&](const SimpleType &ty, bool pol,
               std::set<std::pair<SimpleType, bool>, PairComparator> &inProcess)
      -> UTypePtr {
    if (auto n = ty->getAsTPrimitive()) {
      return make_uprimitivetype(n->name);
    } else if (auto n = ty->getAsTFunction()) {
      std::vector<UTypePtr> args;
      args.reserve(n->args.size());
      for (const auto &arg : n->args) {
        args.push_back(go(arg, !pol, inProcess));
      }
      auto rhs = go(n->result, pol, inProcess);
      return make_ufunctiontype(std::move(args), rhs);
    } else if (auto n = ty->getAsTRecord()) {
      std::vector<std::pair<std::string, UTypePtr>> fields;
      fields.reserve(n->fields.size());
      for (const auto &[name, fieldType] : n->fields) {
        fields.emplace_back(name, go(fieldType, pol, inProcess));
      }
      return make_urecordtype(std::move(fields));
    } else if (auto n = ty->getAsVariableState()) {
      auto key = std::make_pair(ty, pol);

      if (inProcess.count(key)) {
        // Recursive case - create or reuse recursive variable
        auto it = recursive.find(key);
        if (it == recursive.end()) {
          std::string recName = "μ" + std::to_string(recVarCounter++);
          recursive[key] = recName;
          return make_utypevariable(recName);
        } else {
          return make_utypevariable(it->second);
        }
      } else {
        auto newInProcess = inProcess;
        newInProcess.insert(key);

        // Collect bounds
        const auto &bounds = pol ? n->lowerBounds : n->upperBounds;

        if (bounds.empty()) {
          // No bounds - just return a type variable
          return make_utypevariable(var_id_to_name(n->id));
        }

        // Merge all bounds based on polarity
        UTypePtr result = nullptr;
        for (const auto &bound : bounds) {
          auto boundType = go(bound, pol, newInProcess);
          if (!result) {
            result = boundType;
          } else {
            if (pol) {
              // Positive: union
              result = make_uunion(result, boundType);
            } else {
              // Negative: intersection
              result = make_uinter(result, boundType);
            }
          }
        }

        // Check if we created a recursive variable
        auto recIt = recursive.find(key);
        if (recIt != recursive.end()) {
          return make_urecursivetype(recIt->second, result);
        } else {
          return result ? result : make_utypevariable(var_id_to_name(n->id));
        }
      }
    } else {
      assert(false && "Unhandled variant type in coalesceType");
    }
  };

  std::set<std::pair<SimpleType, bool>, PairComparator> inProcess;
  return go(st, true, inProcess);
}

// ======================= Type Simplification Functions =======================

// https://github.com/LPTK/simple-sub/blob/406e292f349430938de6c612494fd518c4636a84/shared/src/main/scala/simplesub/TypeSimplifier.scala#L102
CompactTypeScheme canonicalizeType(const SimpleType &st) {
  std::map<std::pair<std::shared_ptr<CompactType>, bool>, SimpleType,
           PolarCompactTypePtrCompare>
      recursive;
  std::map<SimpleType, std::shared_ptr<CompactType>, SimpleTypeValueCompare>
      recVars;

  // Helper lambda to create CompactType with specific components
  auto make_compact =
      [](SimpleTypeSet vars = {}, SimpleTypeSet prims = {},
         std::optional<std::map<std::string, std::shared_ptr<CompactType>>>
             rec = std::nullopt,
         std::optional<std::pair<std::vector<std::shared_ptr<CompactType>>,
                                 std::shared_ptr<CompactType>>>
             fun = std::nullopt) {
        auto ct = std::make_shared<CompactType>();
        ct->vars = std::move(vars);
        ct->prims = std::move(prims);
        ct->record = std::move(rec);
        ct->function = std::move(fun);
        return ct;
      };

  // Close over function to find all connected variables
  // Respects polarity: follows lowerBounds when pol=true, upperBounds when
  // pol=false
  std::function<SimpleTypeSet(SimpleTypeSet, bool)> closeOver =
      [&](SimpleTypeSet initial, bool pol) -> SimpleTypeSet {
    SimpleTypeSet done = initial;
    SimpleTypeSet workSet = initial;

    while (!workSet.empty()) {
      auto current_ty = *workSet.begin();
      workSet.erase(workSet.begin());
      auto current = current_ty->getAsVariableState();
      if (!current)
        continue;

      // Add variables from bounds (polarity-sensitive)
      const auto &bounds = pol ? current->lowerBounds : current->upperBounds;
      for (const auto &bound : bounds) {
        if (auto vs = bound->getAsVariableState()) {
          if (done.find(bound) == done.end()) {
            done.insert(bound);
            workSet.insert(bound);
          }
        }
      }
    }
    return done;
  };

  // Turn outermost layer into CompactType, leaving variables untransformed
  std::function<std::shared_ptr<CompactType>(const SimpleType &, bool)> go0 =
      [&](const SimpleType &ty, bool pol) -> std::shared_ptr<CompactType> {
    if (ty->isTPrimitive()) {
      return make_compact({}, {ty});
    } else if (auto n = ty->getAsTFunction()) {
      std::vector<std::shared_ptr<CompactType>> argCTs;
      for (const auto &arg : n->args) {
        argCTs.push_back(go0(arg, !pol));
      }
      auto resCT = go0(n->result, pol);
      return make_compact({}, {}, std::nullopt, std::make_pair(argCTs, resCT));
    } else if (auto n = ty->getAsTRecord()) {
      std::map<std::string, std::shared_ptr<CompactType>> fields;
      for (const auto &[name, fieldType] : n->fields) {
        fields[name] = go0(fieldType, pol);
      }
      return make_compact({}, {}, fields);
    } else if (auto n = ty->getAsVariableState()) {
      auto tvs = closeOver({ty}, pol);
      return make_compact(tvs);
    } else {
      assert(false && "Unhandled variant type in canonicalizeType go0");
    }
  };

  // Merge bounds and traverse the result
  std::function<std::shared_ptr<CompactType>(std::shared_ptr<CompactType>, bool,
                                             PolarCompactTypeSet &)>
      go1 =
          [&](std::shared_ptr<CompactType> ty, bool pol,
              PolarCompactTypeSet &inProcess) -> std::shared_ptr<CompactType> {
    if (ty->vars.empty() && ty->prims.empty() && !ty->record && !ty->function) {
      return ty; // Empty type
    }

    auto pty = std::make_pair(ty, pol);
    if (inProcess.count(pty)) {
      // Recursive case
      auto it = recursive.find(pty);
      if (it == recursive.end()) {
        auto freshVar = make_variable(0);
        recursive[pty] = freshVar;
        return make_compact({freshVar});
      } else {
        return make_compact({it->second});
      }
    } else {
      // Collect bounds from all variables
      auto bound = std::make_shared<CompactType>();
      for (const auto &var : ty->vars) {
        if (auto vs = var->getAsVariableState()) {
          const auto &bounds = pol ? vs->lowerBounds : vs->upperBounds;
          for (const auto &b : bounds) {
            if (!b->getAsVariableState()) { // Skip variables, only process
                                            // non-variable bounds
              auto bCompact = go0(b, pol);
              bound = merge_compact_types(pol, bound, bCompact);
            }
          }
        }
      }

      auto res = merge_compact_types(pol, ty, bound);

      auto newInProcess = inProcess;
      newInProcess.insert(pty);

      // Recursively process nested types
      auto adapted = std::make_shared<CompactType>();
      adapted->vars = res->vars;
      adapted->prims = res->prims;

      if (res->record) {
        std::map<std::string, std::shared_ptr<CompactType>> adaptedRec;
        for (const auto &[k, v] : *res->record) {
          adaptedRec[k] = go1(v, pol, newInProcess);
        }
        adapted->record = adaptedRec;
      }

      if (res->function) {
        std::vector<std::shared_ptr<CompactType>> adaptedArgs;
        for (const auto &arg : res->function->first) {
          adaptedArgs.push_back(go1(arg, !pol, newInProcess));
        }
        adapted->function = std::make_pair(
            adaptedArgs, go1(res->function->second, pol, newInProcess));
      }

      // Check if we created a recursive variable
      auto recIt = recursive.find(pty);
      if (recIt != recursive.end()) {
        auto fresh_var_type = recIt->second;
        recVars[fresh_var_type] = adapted;
        return make_compact({fresh_var_type});
      } else {
        return adapted;
      }
    }
  };

  PolarCompactTypeSet inProcess;
  auto term = go0(st, true);
  auto compactTerm = go1(term, true, inProcess);

  return CompactTypeScheme{compactTerm, recVars};
}

// Co-occurrence analysis implementation
OccurrenceMap analyzeOccurrences(const CompactTypeScheme &cty) {
  std::map<PolarVar, OccurrenceData> coOccurrences;
  std::map<SimpleType, std::shared_ptr<CompactType>> processedRecVars;

  // Traverses the type, performing the analysis
  std::function<void(std::shared_ptr<CompactType>, bool)> go =
      [&](std::shared_ptr<CompactType> ty, bool pol) -> void {
    // std::cerr << "Visiting: " << toString(*ty) << "\n";
    // Collect variables and primitives separately
    SimpleTypeSet newVars;
    SimpleTypeSet newPrims;

    // Add all variables
    for (const auto &var : ty->vars) {
      newVars.insert(var);
    }
    for (const auto &var : ty->vars) {
      if (auto vs = var->getAsVariableState()) {
        PolarVar key{var, pol};

        auto it = coOccurrences.find(key);
        if (it != coOccurrences.end()) {
          // Compute intersection with existing occurrences for variables
          SimpleTypeSet varIntersection;
          std::set_intersection(
              it->second.variables.begin(), it->second.variables.end(),
              newVars.begin(), newVars.end(),
              std::inserter(varIntersection, varIntersection.begin()));
          it->second.variables = varIntersection;
        } else {
          // First occurrence - record all co-occurring variables
          coOccurrences[key].variables = newVars;
        }

        // If this is a recursive variable, process its bound
        auto recIt = cty.recVars.find(var);
        if (recIt != cty.recVars.end() &&
            processedRecVars.find(var) == processedRecVars.end()) {
          processedRecVars[var] = recIt->second;
          go(recIt->second, pol);
        }
      }
    }

    // Add all primitives
    for (const auto &prim : ty->prims) {
      newPrims.insert(prim);
    }

    // Update co-occurrences for primitives
    for (const auto &var : ty->vars) {
      if (auto vs = var->getAsVariableState()) {
        PolarVar key{var, pol};
        auto it = coOccurrences.find(key);
        if (it != coOccurrences.end()) {
          // Compute intersection with existing occurrences for primitives
          SimpleTypeSet primIntersection;
          std::set_intersection(
              it->second.primitives.begin(), it->second.primitives.end(),
              newPrims.begin(), newPrims.end(),
              std::inserter(primIntersection, primIntersection.begin()));
          it->second.primitives = primIntersection;
        } else {
          // First occurrence - record all co-occurring primitives
          coOccurrences[key].primitives = newPrims;
        }
      }
    }

    // Recursively process record fields
    if (ty->record) {
      for (const auto &[fieldName, fieldType] : *ty->record) {
        go(fieldType, pol);
      }
    }

    // Recursively process function types
    if (ty->function) {
      for (const auto &arg : ty->function->first) {
        go(arg, !pol); // Contravariant position
      }
      go(ty->function->second, pol); // Covariant position
    }
  };

  go(cty.cty, true);
  return coOccurrences;
}

CompactTypeScheme simplifyType(const CompactTypeScheme &cty, bool printDebug) {
  // State accumulated during the analysis phase
  SimpleTypeSet allVars;
  auto recVars = cty.recVars;
  auto coOccurrences = analyzeOccurrences(cty);

  // This will be filled up after the analysis phase, to influence the
  // reconstruction phase
  std::map<SimpleType, std::optional<SimpleType>> varSubst;

  // Collect all variables from the type scheme
  std::function<void(std::shared_ptr<CompactType>)> collectVars =
      [&](std::shared_ptr<CompactType> ty) -> void {
    for (const auto &var : ty->vars) {
      assert(var->isVariableState());
      if (auto tv = var->getAsVariableState()) {
        allVars.insert(var);
      }
    }
    if (ty->record) {
      for (const auto &[_, fieldType] : *ty->record) {
        collectVars(fieldType);
      }
    }
    if (ty->function) {
      for (const auto &arg : ty->function->first) {
        collectVars(arg);
      }
      collectVars(ty->function->second);
    }
  };

  collectVars(cty.cty);
  for (const auto &[varPtr, bound] : recVars) {
    allVars.insert(varPtr);
    collectVars(bound);
  }

  // Step 1: Simplify away non-recursive variables that only occur in positive
  // or negative positions
  for (SimpleType varPtr : allVars) {
    if (recVars.find(varPtr) == recVars.end()) { // Non-recursive variable
      // Create PolarVar keys directly from the pointer
      PolarVar posKey{varPtr, true};
      PolarVar negKey{varPtr, false};

      bool hasPos = coOccurrences.find(posKey) != coOccurrences.end();
      bool hasNeg = coOccurrences.find(negKey) != coOccurrences.end();

      if ((hasPos && !hasNeg) || (!hasPos && hasNeg)) {
        // Variable only occurs in one polarity - remove it
        if (printDebug) {
          std::cerr << "Removing variable (only occurs in one polarity): "
                    << var_id_to_name(varPtr->getAsVariableState()->id) << "\n";
        }
        varSubst[varPtr] = std::nullopt;
      }
    }
  }

  // Step 2: Unify equivalent variables based on polar co-occurrence analysis
  for (SimpleType varPtr : allVars) {
    assert(varPtr->isVariableState());
    auto varState = varPtr->getAsVariableState();
    if (varSubst.find(varPtr) != varSubst.end())
      continue; // Already processed

    for (bool pol : {true, false}) {
      PolarVar varKey{varPtr, pol};
      auto varOccIt = coOccurrences.find(varKey);
      if (varOccIt == coOccurrences.end())
        continue;

      const auto &varOccData = varOccIt->second;

      // Check for variable-variable co-occurrence
      for (const auto &coOccVar : varOccData.variables) {
        assert(coOccVar->isVariableState());
        if (auto tv = coOccVar->getAsVariableState()) {
          SimpleType coOccPtr = coOccVar;

          if (coOccPtr != varPtr && varSubst.find(coOccPtr) == varSubst.end() &&
              (recVars.count(varPtr) > 0) == (recVars.count(coOccPtr) > 0)) {

            // Check if coOccVar always co-occurs with varPtr in this polarity
            // if (printDebug) {
            //   std::cerr << "Check if " << var_id_to_name(varState->id)
            //             << " always co-occurs with " <<
            //             var_id_to_name(tv->id)
            //             << "\n";
            // }
            PolarVar coOccKey{coOccPtr, pol};
            auto coOccOccIt = coOccurrences.find(coOccKey);

            if (coOccOccIt != coOccurrences.end()) {
              // Check if coOccVar's variable occurrences include varPtr
              bool alwaysCoOccurs = coOccOccIt->second.variables.find(varPtr) !=
                                    coOccOccIt->second.variables.end();

              if (alwaysCoOccurs) {
                if (printDebug) {
                  std::cerr << "In polarity " << pol << ", "
                            << var_id_to_name(varState->id)
                            << " always co-occurs with "
                            << var_id_to_name(tv->id) << "\n";
                }
                // Unify coOccPtr into varPtr
                varSubst[coOccPtr] = varPtr;

                // If both are recursive, merge their bounds
                if (recVars.count(varPtr) && recVars.count(coOccPtr)) {
                  auto mergedBound = merge_compact_types(pol, recVars[varPtr],
                                                         recVars[coOccPtr]);
                  recVars[varPtr] = mergedBound;
                  recVars.erase(coOccPtr);
                } else {
                  // If non recursive, fix coOccurrences map.
                  // When unifying coOccPtr into varPtr, we need to update the
                  // opposite polarity co-occurrences
                  PolarVar oppCoOccKey{coOccPtr, !pol};
                  auto oppCoOccIt = coOccurrences.find(oppCoOccKey);

                  if (oppCoOccIt != coOccurrences.end()) {
                    // Update varPtr's opposite polarity co-occurrences to be
                    // the intersection with coOccPtr's opposite polarity
                    // co-occurrences
                    PolarVar oppVarKey{varPtr, !pol};
                    auto oppVarIt = coOccurrences.find(oppVarKey);

                    if (oppVarIt != coOccurrences.end()) {
                      // Keep only variables that occur in both sets (plus
                      // varPtr itself)
                      SimpleTypeSet newVarOccs;
                      for (const auto &var : oppVarIt->second.variables) {
                        if (var == varPtr ||
                            oppCoOccIt->second.variables.count(var) > 0) {
                          newVarOccs.insert(var);
                        }
                      }
                      oppVarIt->second.variables = newVarOccs;

                      // Keep only primitives that occur in both sets
                      SimpleTypeSet newPrimOccs;
                      for (const auto &prim : oppVarIt->second.primitives) {
                        if (oppCoOccIt->second.primitives.count(prim) > 0) {
                          newPrimOccs.insert(prim);
                        }
                      }
                      oppVarIt->second.primitives = newPrimOccs;
                    }
                  }
                }
              }
            }
          }
        }
      }

      // Check for variable-primitive co-occurrence
      for (const auto &prim : varOccData.primitives) {
        if (auto p = prim->getAsTPrimitive()) {
          // Check if variable also occurs in opposite polarity with the same
          // primitive
          PolarVar oppKey{varPtr, !pol};
          auto oppOccIt = coOccurrences.find(oppKey);

          if (oppOccIt != coOccurrences.end()) {
            for (const auto &oppPrim : oppOccIt->second.primitives) {
              if (auto oppP = oppPrim->getAsTPrimitive()) {
                if (oppP->name == p->name) {
                  if (printDebug) {
                    std::cerr
                        << "Variable "
                        << var_id_to_name(varPtr->getAsVariableState()->id)
                        << " always occurs with the primitive " << p->name
                        << " in both polarities";
                  }
                  // Remove the variable
                  varSubst[varPtr] = std::nullopt;
                  goto next_var; // Break out of all nested loops for this
                                 // variable
                }
              }
            }
          }
        }
      }
    }
  next_var:;
  }

  // Step 3: Reconstruct the type with substitutions applied
  std::function<std::shared_ptr<CompactType>(std::shared_ptr<CompactType>)>
      reconstruct =
          [&](std::shared_ptr<CompactType> ty) -> std::shared_ptr<CompactType> {
    auto result = std::make_shared<CompactType>();

    // Apply substitutions to variables
    for (const auto &var : ty->vars) {
      if (auto tv = var->getAsVariableState()) {
        auto substIt = varSubst.find(var);
        if (substIt != varSubst.end()) {
          if (substIt->second.has_value()) {
            result->vars.insert(*substIt->second);
          } else {
            // If nullopt, remove the variable (don't add to result)
          }
        } else {
          // Keep the variable unchanged
          result->vars.insert(var);
        }
      }
    }

    // Keep primitives unchanged
    result->prims = ty->prims;

    // Recursively reconstruct record fields
    if (ty->record) {
      std::map<std::string, std::shared_ptr<CompactType>> newRecord;
      for (const auto &[fieldName, fieldType] : *ty->record) {
        newRecord[fieldName] = reconstruct(fieldType);
      }
      result->record = newRecord;
    }

    // Recursively reconstruct function types
    if (ty->function) {
      std::vector<std::shared_ptr<CompactType>> reconstructedArgs;
      for (const auto &arg : ty->function->first) {
        reconstructedArgs.push_back(reconstruct(arg));
      }
      result->function =
          std::make_pair(reconstructedArgs, reconstruct(ty->function->second));
    }

    return result;
  };

  // Reconstruct the main type
  auto newTerm = reconstruct(cty.cty);

  // Reconstruct recursive variable bounds with substitutions applied
  std::map<SimpleType, std::shared_ptr<CompactType>, SimpleTypeValueCompare>
      newRecVars;
  for (const auto &[varPtr, bound] : recVars) {
    auto substIt = varSubst.find(varPtr);
    if (substIt == varSubst.end() || substIt->second.has_value()) {
      // Keep this recursive variable (possibly with new pointer)
      SimpleType newVarPtr =
          (substIt != varSubst.end() && substIt->second.has_value())
              ? substIt->second.value()
              : varPtr;
      newRecVars[newVarPtr] = reconstruct(bound);
    }
  }

  return CompactTypeScheme{newTerm, newRecVars};
}

UTypePtr coalesceCompactType(const CompactTypeScheme &cty) {
  std::map<std::pair<std::shared_ptr<CompactType>, bool>, std::string>
      recursive;
  static std::uint32_t recVarCounter = 0;

  std::function<UTypePtr(std::shared_ptr<CompactType>, bool,
                         std::map<std::pair<std::shared_ptr<CompactType>, bool>,
                                  std::function<UTypePtr()>> &)>
      go = [&](std::shared_ptr<CompactType> ty, bool pol,
               std::map<std::pair<std::shared_ptr<CompactType>, bool>,
                        std::function<UTypePtr()>> &inProcess) -> UTypePtr {
    auto key = std::make_pair(ty, pol);
    auto it = inProcess.find(key);
    if (it != inProcess.end()) {
      // Recursive case - this creates a recursive type
      return it->second();
    }

    bool isRecursive = false;
    std::string recVarName;
    std::function<UTypePtr()> recVarGetter = [&]() -> UTypePtr {
      isRecursive = true;
      if (recVarName.empty()) {
        recVarName = "μ" + std::to_string(recVarCounter++);
      }
      return make_utypevariable(recVarName);
    };

    auto newInProcess = inProcess;
    newInProcess[key] = recVarGetter;

    // Build the type components
    std::vector<UTypePtr> components;

    // Add variables (convert SimpleType variables to type variable names)
    for (const auto &var : ty->vars) {
      if (auto vs = var->getAsVariableState()) {
        // Check if this is a recursive variable
        auto recIt = cty.recVars.find(var);
        if (recIt != cty.recVars.end()) {
          // Recursive variable - process its bound
          auto boundType = go(recIt->second, pol, newInProcess);
          components.push_back(boundType);
        } else {
          // Regular variable
          components.push_back(make_utypevariable(var_id_to_name(vs->id)));
        }
      }
    }

    // Add primitives
    for (const auto &prim : ty->prims) {
      if (auto p = prim->getAsTPrimitive()) {
        components.push_back(make_uprimitivetype(p->name));
      }
    }

    // Add record type
    if (ty->record) {
      std::vector<std::pair<std::string, UTypePtr>> fields;
      for (const auto &[fieldName, fieldType] : *ty->record) {
        fields.emplace_back(fieldName, go(fieldType, pol, newInProcess));
      }
      components.push_back(make_urecordtype(std::move(fields)));
    }

    // Add function type
    if (ty->function) {
      std::vector<UTypePtr> funArgs;
      for (const auto &arg : ty->function->first) {
        funArgs.push_back(go(arg, !pol, newInProcess));
      }
      auto rhs = go(ty->function->second, pol, newInProcess);
      components.push_back(make_ufunctiontype(std::move(funArgs), rhs));
    }

    // Combine components based on polarity
    UTypePtr result;
    if (components.empty()) {
      result = pol ? make_ubot() : make_utop();
    } else if (components.size() == 1) {
      result = components[0];
    } else {
      result = components[0];
      for (size_t i = 1; i < components.size(); ++i) {
        if (pol) {
          // Positive: union
          result = make_uunion(result, components[i]);
        } else {
          // Negative: intersection
          result = make_uinter(result, components[i]);
        }
      }
    }

    // If we detected recursion, wrap in a recursive type
    if (isRecursive) {
      return make_urecursivetype(recVarName, result);
    } else {
      return result;
    }
  };

  std::map<std::pair<std::shared_ptr<CompactType>, bool>,
           std::function<UTypePtr()>>
      inProcess;
  return go(cty.cty, true, inProcess);
}

} // namespace binarysub
