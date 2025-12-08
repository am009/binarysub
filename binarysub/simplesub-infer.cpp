#include "simplesub-infer.h"
#include <functional>
#include <map>

namespace simplesub {

// ======================= TypeScheme Implementation ========================

binarysub::SimpleType TypeScheme::instantiate(int lvl, binarysub::VarSupply& supply) {
  return std::visit([&](auto&& arg) -> binarysub::SimpleType {
    using T = std::decay_t<decltype(arg)>;
    if constexpr (std::is_same_v<T, binarysub::SimpleType>) {
      return arg;
    } else if constexpr (std::is_same_v<T, PolymorphicType>) {
      // For PolymorphicType, we need to freshen variables above the polymorphic level
      // This is handled by the Typer's freshenAbove method
      return arg.body;
    } else {
      static_assert(!sizeof(T), "Unhandled TypeScheme variant");
    }
  }, v);
}

// ======================= Typer Implementation ========================

Typer::Typer() {
  // Initialize built-in types
  auto BoolType = binarysub::make_primitive("bool");
  auto IntType = binarysub::make_primitive("int");

  builtins["true"] = TypeScheme(BoolType);
  builtins["false"] = TypeScheme(BoolType);
  builtins["not"] = TypeScheme(binarysub::make_function(BoolType, BoolType));
  builtins["succ"] = TypeScheme(binarysub::make_function(IntType, IntType));
  builtins["add"] = TypeScheme(
    binarysub::make_function(IntType, binarysub::make_function(IntType, IntType))
  );

  // if: bool -> 'a -> 'a -> 'a
  auto v = binarysub::fresh_variable(supply, 1);
  builtins["if"] = TypeScheme(PolymorphicType(0,
    binarysub::make_function(BoolType,
      binarysub::make_function(v,
        binarysub::make_function(v, v)))
  ));
}

std::vector<binarysub::expected<PolymorphicType, binarysub::Error>>
Typer::inferTypes(const Pgrm& pgrm, const Ctx& ctx) {
  std::vector<binarysub::expected<PolymorphicType, binarysub::Error>> results;
  Ctx current_ctx = ctx;

  for (const auto& def : pgrm.defs) {
    bool isRec = std::get<0>(def);
    const std::string& name = std::get<1>(def);
    const TermPtr& rhs = std::get<2>(def);

    auto ty_sch = typeLetRhs(isRec, name, rhs, current_ctx, 0);

    if (ty_sch.has_value()) {
      current_ctx[name] = TypeScheme(ty_sch.value());
    } else {
      // On error, add a fresh variable to continue type checking
      current_ctx[name] = TypeScheme(binarysub::fresh_variable(supply, 0));
    }

    results.push_back(std::move(ty_sch));
  }

  return results;
}

binarysub::expected<binarysub::SimpleType, binarysub::Error>
Typer::inferType(const TermPtr& term, const Ctx& ctx, int lvl) {
  return typeTerm(term, ctx, lvl);
}

binarysub::expected<PolymorphicType, binarysub::Error>
Typer::typeLetRhs(bool isRec, const std::string& name, const TermPtr& rhs,
                  const Ctx& ctx, int lvl) {
  binarysub::SimpleType res;

  if (isRec) {
    // For recursive bindings, create a fresh variable and add it to context
    auto e_ty = binarysub::fresh_variable(supply, lvl + 1);
    Ctx new_ctx = ctx;
    new_ctx[name] = TypeScheme(e_ty);

    auto ty_result = typeTerm(rhs, new_ctx, lvl + 1);
    if (!ty_result.has_value()) {
      return binarysub::make_unexpected(ty_result.error());
    }

    auto ty = ty_result.value();
    binarysub::Cache cache;
    auto constrain_result = binarysub::constrain(ty, e_ty, cache, supply);
    if (!constrain_result.has_value()) {
      return binarysub::make_unexpected(constrain_result.error());
    }

    res = e_ty;
  } else {
    auto ty_result = typeTerm(rhs, ctx, lvl + 1);
    if (!ty_result.has_value()) {
      return binarysub::make_unexpected(ty_result.error());
    }
    res = ty_result.value();
  }

  return PolymorphicType(lvl, res);
}

binarysub::SimpleType Typer::freshenAbove(int lim, const binarysub::SimpleType& ty, int lvl) {
  std::map<binarysub::VariableState*, binarysub::SimpleType> freshened;

  std::function<binarysub::SimpleType(const binarysub::SimpleType&)> freshen;
  freshen = [&](const binarysub::SimpleType& t) -> binarysub::SimpleType {
    if (binarysub::level_of(t) <= lim) {
      return t;
    }

    return std::visit([&](auto&& arg) -> binarysub::SimpleType {
      using T = std::decay_t<decltype(arg)>;
      if constexpr (binarysub::isVariableStateType<T>()) {
        auto* vs = t->getAsVariableState();
        auto it = freshened.find(vs);
        if (it != freshened.end()) {
          return it->second;
        }

        auto v = binarysub::fresh_variable(supply, lvl);
        freshened[vs] = v;

        auto* new_vs = v->getAsVariableState();
        for (const auto& lb : vs->lowerBounds) {
          new_vs->lowerBounds.push_back(freshen(lb));
        }
        for (const auto& ub : vs->upperBounds) {
          new_vs->upperBounds.push_back(freshen(ub));
        }

        return v;
      } else if constexpr (binarysub::isTFunctionType<T>()) {
        auto* func = t->getAsTFunction();
        std::vector<binarysub::SimpleType> new_args;
        for (const auto& arg : func->args) {
          new_args.push_back(freshen(arg));
        }
        return binarysub::make_function(std::move(new_args), freshen(func->result));
      } else if constexpr (binarysub::isTRecordType<T>()) {
        auto* rec = t->getAsTRecord();
        std::vector<std::pair<std::string, binarysub::SimpleType>> new_fields;
        for (const auto& field : rec->fields) {
          new_fields.push_back({field.first, freshen(field.second)});
        }
        return binarysub::make_record(std::move(new_fields));
      } else if constexpr (binarysub::isTPrimitiveType<T>()) {
        return t;
      } else {
        static_assert(!sizeof(T), "Unhandled SimpleType variant in freshenAbove");
      }
    }, ty->v);
  };

  return freshen(ty);
}

binarysub::expected<binarysub::SimpleType, binarysub::Error>
Typer::typeTerm(const TermPtr& term, const Ctx& ctx, int lvl) {
  return std::visit([&](auto&& arg) -> binarysub::expected<binarysub::SimpleType, binarysub::Error> {
    using T = std::decay_t<decltype(arg)>;

    if constexpr (std::is_same_v<T, Var>) {
      // Variable lookup
      auto it = ctx.find(arg.name);
      if (it == ctx.end()) {
        return binarysub::make_unexpected(
          binarysub::Error::make("identifier not found: " + arg.name)
        );
      }

      // Instantiate the type scheme
      auto& scheme = it->second;
      return std::visit([&](auto&& scheme_arg) -> binarysub::SimpleType {
        using ST = std::decay_t<decltype(scheme_arg)>;
        if constexpr (std::is_same_v<ST, binarysub::SimpleType>) {
          return scheme_arg;
        } else if constexpr (std::is_same_v<ST, PolymorphicType>) {
          return freshenAbove(scheme_arg.level, scheme_arg.body, lvl);
        } else {
          static_assert(!sizeof(ST), "Unhandled TypeScheme variant");
        }
      }, scheme.v);

    } else if constexpr (std::is_same_v<T, Lam>) {
      // Lambda: fun name -> body
      auto param = binarysub::fresh_variable(supply, lvl);
      Ctx new_ctx = ctx;
      new_ctx[arg.name] = TypeScheme(param);

      auto body_ty_result = typeTerm(arg.rhs, new_ctx, lvl);
      if (!body_ty_result.has_value()) {
        return binarysub::make_unexpected(body_ty_result.error());
      }

      return binarysub::make_function(param, body_ty_result.value());

    } else if constexpr (std::is_same_v<T, App>) {
      // Application: f a
      auto f_ty_result = typeTerm(arg.lhs, ctx, lvl);
      if (!f_ty_result.has_value()) {
        return binarysub::make_unexpected(f_ty_result.error());
      }

      auto a_ty_result = typeTerm(arg.rhs, ctx, lvl);
      if (!a_ty_result.has_value()) {
        return binarysub::make_unexpected(a_ty_result.error());
      }

      auto res = binarysub::fresh_variable(supply, lvl);
      auto f_ty = f_ty_result.value();
      auto a_ty = a_ty_result.value();

      binarysub::Cache cache;
      auto constrain_result = binarysub::constrain(
        f_ty,
        binarysub::make_function(a_ty, res),
        cache,
        supply
      );

      if (!constrain_result.has_value()) {
        return binarysub::make_unexpected(constrain_result.error());
      }

      return res;

    } else if constexpr (std::is_same_v<T, Lit>) {
      // Integer literal
      return binarysub::make_primitive("int");

    } else if constexpr (std::is_same_v<T, Sel>) {
      // Field selection: obj.name
      auto obj_ty_result = typeTerm(arg.receiver, ctx, lvl);
      if (!obj_ty_result.has_value()) {
        return binarysub::make_unexpected(obj_ty_result.error());
      }

      auto res = binarysub::fresh_variable(supply, lvl);
      std::vector<std::pair<std::string, binarysub::SimpleType>> fields;
      fields.push_back({arg.fieldName, res});

      binarysub::Cache cache;
      auto constrain_result = binarysub::constrain(
        obj_ty_result.value(),
        binarysub::make_record(std::move(fields)),
        cache,
        supply
      );

      if (!constrain_result.has_value()) {
        return binarysub::make_unexpected(constrain_result.error());
      }

      return res;

    } else if constexpr (std::is_same_v<T, Rcd>) {
      // Record: {f1: t1, f2: t2, ...}
      std::vector<std::pair<std::string, binarysub::SimpleType>> fields;

      for (const auto& field : arg.fields) {
        auto field_ty_result = typeTerm(field.second, ctx, lvl);
        if (!field_ty_result.has_value()) {
          return binarysub::make_unexpected(field_ty_result.error());
        }
        fields.push_back({field.first, field_ty_result.value()});
      }

      return binarysub::make_record(std::move(fields));

    } else if constexpr (std::is_same_v<T, Let>) {
      // Let binding: let name = rhs in body
      auto n_ty_result = typeLetRhs(arg.isRec, arg.name, arg.rhs, ctx, lvl);
      if (!n_ty_result.has_value()) {
        return binarysub::make_unexpected(n_ty_result.error());
      }

      Ctx new_ctx = ctx;
      new_ctx[arg.name] = TypeScheme(n_ty_result.value());

      return typeTerm(arg.body, new_ctx, lvl);

    } else {
      static_assert(!sizeof(T), "Unhandled Term variant in typeTerm");
    }
  }, term->v);
}

} // namespace simplesub
