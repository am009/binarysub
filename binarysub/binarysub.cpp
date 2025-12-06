#include "binarysub.h"
#include <numeric>
#include <functional>
#include <sstream>

namespace binarysub {

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
          if (n.args.empty()) {
            os << "()";
          } else {
            for (size_t i = 0; i < n.args.size(); ++i) {
              if (i > 0)
                os << " × ";
              printTypeImpl(n.args[i], os, 2);
            }
          }
          os << " → ";
          printTypeImpl(n.result, os, 1);
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
                             std::map<SimpleType, SimpleType> &memo,
                             VarSupply &supply) {
  return std::visit(
      [&](auto const &n) -> SimpleType {
        using T = std::decay_t<decltype(n)>;
        if constexpr (isTPrimitiveType<T>()) {
          return t;
        } else if constexpr (isTFunctionType<T>()) {
          std::vector<SimpleType> args;
          args.reserve(n.args.size());
          for (auto const &a : n.args)
            args.push_back(
                freshen_above_rec(a, cutoff, at_level, memo, supply));
          return make_function(
              std::move(args),
              freshen_above_rec(n.result, cutoff, at_level, memo, supply));
        } else if constexpr (isTRecordType<T>()) {
          std::vector<std::pair<std::string, SimpleType>> fs;
          fs.reserve(n.fields.size());
          for (auto const &[name, sub] : n.fields)
            fs.emplace_back(
                name, freshen_above_rec(sub, cutoff, at_level, memo, supply));
          return make_record(std::move(fs));
        } else if constexpr (isVariableStateType<T>()) {
          // VariableState
          if (n.level > cutoff) {
            if (auto it = memo.find(t); it != memo.end())
              return it->second;
            auto fresh =
                fresh_variable(supply, at_level); // empty bounds, new id/level
            memo.emplace(t, fresh);
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
  std::map<SimpleType, SimpleType> memo;
  return freshen_above_rec(p.body, p.generalized_above, at_level, memo, supply);
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
  std::ostringstream oss;

  std::vector<std::string> components;

  // Add variables
  if (!ct.vars.empty()) {
    std::vector<std::string> varNames;
    for (const auto &var : ct.vars) {
      if (auto vs = var->getAsVariableState()) {
        varNames.push_back("α" + std::to_string(vs->id));
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
    std::string lhs = toString(*ct.function->first);
    std::string rhs = toString(*ct.function->second);
    components.push_back("(" + lhs + " → " + rhs + ")");
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
    oss << "α" << var_ptr->id << (polarVar.pos ? "⁺" : "⁻");
    oss << " → {vars: {";

    // Format the variable set
    bool firstVar = true;
    for (const auto &var : occData.variables) {
      if (!firstVar) {
        oss << ", ";
      }

      if (auto vs = var->getAsVariableState()) {
        oss << "α" << vs->id;
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
    return std::visit(
        [&](auto const &n) -> UTypePtr {
          using T = std::decay_t<decltype(n)>;

          if constexpr (isTPrimitiveType<T>()) {
            return make_uprimitivetype(n.name);
          } else if constexpr (isTFunctionType<T>()) {
            std::vector<UTypePtr> args;
            args.reserve(n.args.size());
            for (const auto &arg : n.args) {
              args.push_back(go(arg, !pol, inProcess));
            }
            auto rhs = go(n.result, pol, inProcess);
            return make_ufunctiontype(std::move(args), rhs);
          } else if constexpr (isTRecordType<T>()) {
            std::vector<std::pair<std::string, UTypePtr>> fields;
            fields.reserve(n.fields.size());
            for (const auto &[name, fieldType] : n.fields) {
              fields.emplace_back(name, go(fieldType, pol, inProcess));
            }
            return make_urecordtype(std::move(fields));
          } else if constexpr (isVariableStateType<T>()) {
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
              const auto &bounds = pol ? n.lowerBounds : n.upperBounds;

              if (bounds.empty()) {
                // No bounds - just return a type variable
                return make_utypevariable("α" + std::to_string(n.id));
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
                return result ? result
                              : make_utypevariable("α" + std::to_string(n.id));
              }
            }
          } else {
            static_assert(!sizeof(T), "Unhandled variant type in coalesceType");
          }
        },
        ty->v);
  };

  std::set<std::pair<SimpleType, bool>, PairComparator> inProcess;
  return go(st, true, inProcess);
}

// ======================= Type Simplification Functions =======================

CompactTypeScheme compactType(const SimpleType &st) {
  std::map<PolarVar, std::shared_ptr<VariableState>> recursive;
  std::map<SimpleType, std::shared_ptr<CompactType>> recVars;
  VarSupply freshSupply; // For creating fresh variables when needed

  auto empty_compact = make_empty_compact_type();

  // Helper lambda to create CompactType with specific components
  auto make_compact =
      [](std::set<SimpleType> vars = {}, std::set<SimpleType> prims = {},
         std::optional<std::map<std::string, std::shared_ptr<CompactType>>>
             rec = std::nullopt,
         std::optional<std::pair<std::shared_ptr<CompactType>,
                                 std::shared_ptr<CompactType>>>
             fun = std::nullopt) {
        auto ct = std::make_shared<CompactType>();
        ct->vars = std::move(vars);
        ct->prims = std::move(prims);
        ct->record = std::move(rec);
        ct->function = std::move(fun);
        return ct;
      };

  std::function<std::shared_ptr<CompactType>(
      const SimpleType &, bool, std::set<std::shared_ptr<VariableState>>,
      std::set<PolarVar> &)>
      go = [&](const SimpleType &ty, bool pol,
               std::set<std::shared_ptr<VariableState>> parents,
               std::set<PolarVar> &inProcess) -> std::shared_ptr<CompactType> {
    return std::visit(
        [&](auto const &n) -> std::shared_ptr<CompactType> {
          using T = std::decay_t<decltype(n)>;

          if constexpr (isTPrimitiveType<T>()) {
            return make_compact({}, {ty});
          } else if constexpr (isTFunctionType<T>()) {
            auto resCT = go(n.result, pol, {}, inProcess);
            for (auto it = n.args.rbegin(); it != n.args.rend(); ++it) {
              auto argCT = go(*it, !pol, {}, inProcess);
              resCT = make_compact({}, {}, std::nullopt,
                                   std::make_pair(argCT, resCT));
            }
            return resCT;
          } else if constexpr (isTRecordType<T>()) {
            std::map<std::string, std::shared_ptr<CompactType>> fields;
            for (const auto &[name, fieldType] : n.fields) {
              fields[name] = go(fieldType, pol, {}, inProcess);
            }
            return make_compact({}, {}, fields);
          } else if constexpr (isVariableStateType<T>()) {
            const auto &bounds = pol ? n.lowerBounds : n.upperBounds;
            PolarVar tv_pol{ty, pol};

            if (inProcess.count(tv_pol)) {
              if (parents.count(std::make_shared<VariableState>(n))) {
                // Spurious cycle: ignore the bound
                return make_compact();
              } else {
                // Create recursive variable
                auto it = recursive.find(tv_pol);
                if (it == recursive.end()) {
                  auto freshVar = std::make_shared<VariableState>(
                      freshSupply.fresh_id(), 0);
                  recursive[tv_pol] = freshVar;
                  return make_compact({std::make_shared<TypeNode>(*freshVar)});
                } else {
                  return make_compact(
                      {std::make_shared<TypeNode>(*(it->second))});
                }
              }
            } else {
              auto newInProcess = inProcess;
              newInProcess.insert(tv_pol);
              auto newParents = parents;
              newParents.insert(std::make_shared<VariableState>(n));

              // Start with the variable itself
              auto bound = make_compact({ty});

              // Merge all bounds
              for (const auto &b : bounds) {
                auto boundCompact = go(b, pol, newParents, newInProcess);
                bound = merge_compact_types(pol, bound, boundCompact);
              }

              // Check if we created a recursive variable
              auto recIt = recursive.find(tv_pol);
              if (recIt != recursive.end()) {
                auto fresh_var_type =
                    std::make_shared<TypeNode>(*(recIt->second));
                recVars[fresh_var_type] = bound;
                return make_compact({fresh_var_type});
              } else {
                return bound;
              }
            }
          } else {
            static_assert(!sizeof(T), "Unhandled variant type in compactType");
          }
        },
        ty->v);
  };

  std::set<PolarVar> inProcess;
  auto compactTerm = go(st, true, {}, inProcess);

  return CompactTypeScheme{compactTerm, recVars};
}

CompactTypeScheme canonicalizeType(const SimpleType &st) {
  std::map<std::pair<std::shared_ptr<CompactType>, bool>,
           std::shared_ptr<VariableState>>
      recursive;
  std::map<SimpleType, std::shared_ptr<CompactType>> recVars;
  VarSupply freshSupply;

  auto empty_compact = make_empty_compact_type();

  // Helper lambda to create CompactType with specific components
  auto make_compact =
      [](std::set<SimpleType> vars = {}, std::set<SimpleType> prims = {},
         std::optional<std::map<std::string, std::shared_ptr<CompactType>>>
             rec = std::nullopt,
         std::optional<std::pair<std::shared_ptr<CompactType>,
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
  std::function<std::set<std::shared_ptr<VariableState>>(
      std::set<std::shared_ptr<VariableState>>)>
      closeOver = [&](std::set<std::shared_ptr<VariableState>> initial)
      -> std::set<std::shared_ptr<VariableState>> {
    std::set<std::shared_ptr<VariableState>> result = initial;
    std::set<std::shared_ptr<VariableState>> workSet = initial;

    while (!workSet.empty()) {
      auto current = *workSet.begin();
      workSet.erase(workSet.begin());

      // Add variables from bounds
      for (const auto &bound : current->lowerBounds) {
        if (auto vs = bound->getAsVariableState()) {
          auto vs_ptr = std::make_shared<VariableState>(*vs);
          if (result.find(vs_ptr) == result.end()) {
            result.insert(vs_ptr);
            workSet.insert(vs_ptr);
          }
        }
      }
      for (const auto &bound : current->upperBounds) {
        if (auto vs = bound->getAsVariableState()) {
          auto vs_ptr = std::make_shared<VariableState>(*vs);
          if (result.find(vs_ptr) == result.end()) {
            result.insert(vs_ptr);
            workSet.insert(vs_ptr);
          }
        }
      }
    }
    return result;
  };

  // Turn outermost layer into CompactType, leaving variables untransformed
  std::function<std::shared_ptr<CompactType>(const SimpleType &, bool)> go0 =
      [&](const SimpleType &ty, bool pol) -> std::shared_ptr<CompactType> {
    return std::visit(
        [&](auto const &n) -> std::shared_ptr<CompactType> {
          using T = std::decay_t<decltype(n)>;

          if constexpr (isTPrimitiveType<T>()) {
            return make_compact({}, {ty});
          } else if constexpr (isTFunctionType<T>()) {
            auto resCT = go0(n.result, pol);
            for (auto it = n.args.rbegin(); it != n.args.rend(); ++it) {
              auto argCT = go0(*it, !pol);
              resCT = make_compact({}, {}, std::nullopt,
                                   std::make_pair(argCT, resCT));
            }
            return resCT;
          } else if constexpr (isTRecordType<T>()) {
            std::map<std::string, std::shared_ptr<CompactType>> fields;
            for (const auto &[name, fieldType] : n.fields) {
              fields[name] = go0(fieldType, pol);
            }
            return make_compact({}, {}, fields);
          } else if constexpr (isVariableStateType<T>()) {
            auto vs_ptr = std::make_shared<VariableState>(n);
            auto tvs = closeOver({vs_ptr});

            std::set<SimpleType> varSet;
            for (const auto &vs : tvs) {
              varSet.insert(std::make_shared<TypeNode>(*vs));
            }
            return make_compact(varSet);
          } else {
            static_assert(!sizeof(T),
                          "Unhandled variant type in canonicalizeType go0");
          }
        },
        ty->v);
  };

  // Merge bounds and traverse the result
  std::function<std::shared_ptr<CompactType>(
      std::shared_ptr<CompactType>, bool,
      std::set<std::pair<std::shared_ptr<CompactType>, bool>> &)>
      go1 = [&](std::shared_ptr<CompactType> ty, bool pol,
                std::set<std::pair<std::shared_ptr<CompactType>, bool>>
                    &inProcess) -> std::shared_ptr<CompactType> {
    if (ty->vars.empty() && ty->prims.empty() && !ty->record && !ty->function) {
      return ty; // Empty type
    }

    auto pty = std::make_pair(ty, pol);
    if (inProcess.count(pty)) {
      // Recursive case
      auto it = recursive.find(pty);
      if (it == recursive.end()) {
        auto freshVar =
            std::make_shared<VariableState>(freshSupply.fresh_id(), 0);
        recursive[pty] = freshVar;
        return make_compact({std::make_shared<TypeNode>(*freshVar)});
      } else {
        return make_compact({std::make_shared<TypeNode>(*(it->second))});
      }
    } else {
      // Collect bounds from all variables
      auto bound = empty_compact;
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
        adapted->function =
            std::make_pair(go1(res->function->first, !pol, newInProcess),
                           go1(res->function->second, pol, newInProcess));
      }

      // Check if we created a recursive variable
      auto recIt = recursive.find(pty);
      if (recIt != recursive.end()) {
        auto fresh_var_type = std::make_shared<TypeNode>(*(recIt->second));
        recVars[fresh_var_type] = adapted;
        return make_compact({fresh_var_type});
      } else {
        return adapted;
      }
    }
  };

  std::set<std::pair<std::shared_ptr<CompactType>, bool>> inProcess;
  auto term = go0(st, true);
  auto compactTerm = go1(term, true, inProcess);

  return CompactTypeScheme{compactTerm, recVars};
}

// Co-occurrence analysis implementation
OccurrenceMap analyzeOccurrences(const CompactTypeScheme &cty) {
  std::map<PolarVar, OccurrenceData> coOccurrences;
  std::set<VariableState *> allVars;
  std::map<SimpleType, std::shared_ptr<CompactType>> processedRecVars;

  // Traverses the type, performing the analysis
  std::function<void(std::shared_ptr<CompactType>, bool)> go =
      [&](std::shared_ptr<CompactType> ty, bool pol) -> void {
    // std::cerr << "Visiting: " << toString(*ty) << "\n";
    // Collect variables and primitives separately
    std::set<SimpleType> newVars;
    std::set<SimpleType> newPrims;

    // Add all variables
    for (const auto &var : ty->vars) {
      newVars.insert(var);
    }
    for (const auto &var : ty->vars) {
      if (auto vs = var->getAsVariableState()) {
        allVars.insert(vs);

        PolarVar key{var, pol};

        auto it = coOccurrences.find(key);
        if (it != coOccurrences.end()) {
          // Compute intersection with existing occurrences for variables
          std::set<SimpleType> varIntersection;
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
          std::set<SimpleType> primIntersection;
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
      go(ty->function->first, !pol); // Contravariant position
      go(ty->function->second, pol); // Covariant position
    }
  };

  go(cty.cty, true);
  return coOccurrences;
}

CompactTypeScheme simplifyType(const CompactTypeScheme &cty) {
  // State accumulated during the analysis phase
  std::set<SimpleType> allVars;
  std::map<SimpleType, std::shared_ptr<CompactType>> recVars = cty.recVars;
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
      collectVars(ty->function->first);
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
        // std::cerr << "Removing variable (only occurs in one polarity): " <<
        // "α"  << std::to_string(varPtr->id) << "\n";
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
            std::cerr << "Check if α" << std::to_string(varState->id)
                      << " always co-occurs with α" << std::to_string(tv->id)
                      << "\n";
            PolarVar coOccKey{coOccPtr, pol};
            auto coOccOccIt = coOccurrences.find(coOccKey);

            if (coOccOccIt != coOccurrences.end()) {
              // Check if coOccVar's variable occurrences include varPtr
              bool alwaysCoOccurs = coOccOccIt->second.variables.find(varPtr) !=
                                    coOccOccIt->second.variables.end();

              if (alwaysCoOccurs) {
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
                      std::set<SimpleType> newVarOccs;
                      for (const auto &var : oppVarIt->second.variables) {
                        if (var == varPtr ||
                            oppCoOccIt->second.variables.count(var) > 0) {
                          newVarOccs.insert(var);
                        }
                      }
                      oppVarIt->second.variables = newVarOccs;

                      // Keep only primitives that occur in both sets
                      std::set<SimpleType> newPrimOccs;
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
                  // Variable always occurs with the same primitive in both
                  // polarities Remove the variable
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
  VarSupply freshSupply;

  std::function<std::shared_ptr<CompactType>(std::shared_ptr<CompactType>)>
      reconstruct =
          [&](std::shared_ptr<CompactType> ty) -> std::shared_ptr<CompactType> {
    auto result = std::make_shared<CompactType>();

    // Apply substitutions to variables
    for (const auto &var : ty->vars) {
      if (auto tv = var->getAsVariableState()) {
        VariableState *varPtr = tv;
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
      result->function = std::make_pair(reconstruct(ty->function->first),
                                        reconstruct(ty->function->second));
    }

    return result;
  };

  // Reconstruct the main type
  auto newTerm = reconstruct(cty.cty);

  // Reconstruct recursive variable bounds with substitutions applied
  std::map<SimpleType, std::shared_ptr<CompactType>> newRecVars;
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
          components.push_back(
              make_utypevariable("α" + std::to_string(vs->id)));
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
      std::set<const CompactType *> seen;
      auto current = ty;
      while (current && current->function &&
             seen.insert(current.get()).second) {
        funArgs.push_back(go(current->function->first, !pol, newInProcess));
        current = current->function->second;
      }
      auto rhs = go(current ? current : ty, pol, newInProcess);
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
