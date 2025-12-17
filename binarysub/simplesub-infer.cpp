#include "simplesub-infer.h"
#include <functional>
#include <iostream>
#include <map>

namespace simplesub {

// ======================= TypeScheme Implementation ========================

binarysub::SimpleType TypeScheme::instantiate(int lvl) {
  if (auto *st = std::get_if<binarysub::SimpleType>(&v)) {
    return *st;
  } else if (auto *pt = std::get_if<PolymorphicType>(&v)) {
    // For PolymorphicType, we need to freshen variables above the
    // polymorphic level This is handled by the Typer's freshenAbove
    // method
    return pt->body;
  } else {
    assert(false && "Unhandled TypeScheme variant");
    return binarysub::SimpleType(); // unreachable
  }
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
  builtins["add"] = TypeScheme(binarysub::make_function(
      IntType, binarysub::make_function(IntType, IntType)));

  // if: bool -> 'a -> 'a -> 'a
  auto v = binarysub::fresh_variable(1);
  builtins["if"] = TypeScheme(PolymorphicType(
      0, binarysub::make_function(
             BoolType,
             binarysub::make_function(v, binarysub::make_function(v, v)))));
}

std::vector<binarysub::expected<PolymorphicType, binarysub::Error>>
Typer::inferTypes(const Pgrm &pgrm, const Ctx &ctx) {
  std::vector<binarysub::expected<PolymorphicType, binarysub::Error>> results;
  Ctx current_ctx = ctx;

  for (const auto &def : pgrm.defs) {
    bool isRec = std::get<0>(def);
    const std::string &name = std::get<1>(def);
    const TermPtr &rhs = std::get<2>(def);

    auto ty_sch = typeLetRhs(isRec, name, rhs, current_ctx, 0);

    if (ty_sch.has_value()) {
      current_ctx.insert_or_assign(name, TypeScheme(ty_sch.value()));
    } else {
      // On error, add a fresh variable to continue type checking
      current_ctx[name] = TypeScheme(binarysub::fresh_variable(0));
    }

    results.push_back(std::move(ty_sch));
  }

  return results;
}

binarysub::expected<binarysub::SimpleType, binarysub::Error>
Typer::inferType(const TermPtr &term, const Ctx &ctx, int lvl) {
  return typeTerm(term, ctx, lvl);
}

binarysub::expected<PolymorphicType, binarysub::Error>
Typer::typeLetRhs(bool isRec, const std::string &name, const TermPtr &rhs,
                  const Ctx &ctx, int lvl) {
  binarysub::SimpleType res;

  if (isRec) {
    // For recursive bindings, create a fresh variable and add it to context
    auto e_ty = binarysub::fresh_variable(lvl + 1);
    Ctx new_ctx = ctx;
    new_ctx[name] = TypeScheme(e_ty);

    auto ty_result = typeTerm(rhs, new_ctx, lvl + 1);
    if (!ty_result.has_value()) {
      return binarysub::make_unexpected(ty_result.error());
    }

    auto ty = ty_result.value();
    binarysub::Cache cache;
    auto constrain_result = binarysub::constrain(ty, e_ty, cache);
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

binarysub::SimpleType
Typer::freshenAbove(int lim, const binarysub::SimpleType &ty, int lvl) {
  std::map<binarysub::VariableState *, binarysub::SimpleType> freshened;

  std::function<binarysub::SimpleType(const binarysub::SimpleType &)> freshen;
  freshen = [&](const binarysub::SimpleType &t) -> binarysub::SimpleType {
    if (binarysub::level_of(t) <= lim) {
      return t;
    }

    if (auto *vs = t->getAsVariableState()) {
      auto it = freshened.find(vs);
      if (it != freshened.end()) {
        return it->second;
      }

      auto v = binarysub::fresh_variable(lvl);
      freshened[vs] = v;

      auto *new_vs = v->getAsVariableState();
      for (const auto &lb : vs->lowerBounds) {
        new_vs->lowerBounds.push_back(freshen(lb));
      }
      for (const auto &ub : vs->upperBounds) {
        new_vs->upperBounds.push_back(freshen(ub));
      }

      return v;
    } else if (auto *func = t->getAsTFunction()) {
      std::vector<binarysub::SimpleType> new_args;
      for (const auto &arg : func->args) {
        new_args.push_back(freshen(arg));
      }
      return binarysub::make_function(std::move(new_args),
                                      freshen(func->result));
    } else if (auto *rec = t->getAsTRecord()) {
      std::vector<std::pair<std::string, binarysub::SimpleType>> new_fields;
      for (const auto &field : rec->fields) {
        new_fields.push_back({field.first, freshen(field.second)});
      }
      return binarysub::make_record(std::move(new_fields));
    } else if (t->getAsTPrimitive()) {
      return t;
    } else {
      assert(false && "Unhandled SimpleType variant in freshenAbove");
      return binarysub::SimpleType(); // unreachable
    }
  };

  return freshen(ty);
}

binarysub::expected<binarysub::SimpleType, binarysub::Error>
Typer::typeTerm(const TermPtr &term, const Ctx &ctx, int lvl) {
  if (auto *var = std::get_if<Var>(&term->v)) {
    // Variable lookup
    auto it = ctx.find(var->name);
    if (it == ctx.end()) {
      return binarysub::make_unexpected(
          binarysub::Error::make("identifier not found: " + var->name));
    }

    // Instantiate the type scheme
    auto &scheme = it->second;
    if (auto *st = std::get_if<binarysub::SimpleType>(&scheme->v)) {
      return *st;
    } else if (auto *pt = std::get_if<PolymorphicType>(&scheme->v)) {
      return freshenAbove(pt->level, pt->body, lvl);
    } else {
      assert(false && "Unhandled TypeScheme variant");
      return binarysub::make_unexpected(
          binarysub::Error::make("Unhandled TypeScheme variant"));
    }

  } else if (auto *lam = std::get_if<Lam>(&term->v)) {
    // Lambda: fun name -> body
    auto param = binarysub::fresh_variable(lvl);
    Ctx new_ctx = ctx;
    new_ctx[lam->name] = TypeScheme(param);

    auto body_ty_result = typeTerm(lam->rhs, new_ctx, lvl);
    if (!body_ty_result.has_value()) {
      return binarysub::make_unexpected(body_ty_result.error());
    }

    return binarysub::make_function(param, body_ty_result.value());

  } else if (auto *app = std::get_if<App>(&term->v)) {
    // Application: f a
    auto f_ty_result = typeTerm(app->lhs, ctx, lvl);
    if (!f_ty_result.has_value()) {
      return binarysub::make_unexpected(f_ty_result.error());
    }

    auto a_ty_result = typeTerm(app->rhs, ctx, lvl);
    if (!a_ty_result.has_value()) {
      return binarysub::make_unexpected(a_ty_result.error());
    }

    auto res = binarysub::fresh_variable(lvl);
    auto f_ty = f_ty_result.value();
    auto a_ty = a_ty_result.value();

    binarysub::Cache cache;
    auto constrain_result = binarysub::constrain(
        f_ty, binarysub::make_function(a_ty, res), cache);

    if (!constrain_result.has_value()) {
      return binarysub::make_unexpected(constrain_result.error());
    }

    return res;

  } else if (auto *lit = std::get_if<Lit>(&term->v)) {
    // Integer literal
    return binarysub::make_primitive("int");

  } else if (auto *sel = std::get_if<Sel>(&term->v)) {
    // Field selection: obj.name
    auto obj_ty_result = typeTerm(sel->receiver, ctx, lvl);
    if (!obj_ty_result.has_value()) {
      return binarysub::make_unexpected(obj_ty_result.error());
    }

    auto res = binarysub::fresh_variable(lvl);
    std::vector<std::pair<std::string, binarysub::SimpleType>> fields;
    fields.push_back({sel->fieldName, res});

    binarysub::Cache cache;
    auto constrain_result = binarysub::constrain(
        obj_ty_result.value(), binarysub::make_record(std::move(fields)), cache);

    if (!constrain_result.has_value()) {
      return binarysub::make_unexpected(constrain_result.error());
    }

    return res;

  } else if (auto *rcd = std::get_if<Rcd>(&term->v)) {
    // Record: {f1: t1, f2: t2, ...}
    std::vector<std::pair<std::string, binarysub::SimpleType>> fields;

    for (const auto &field : rcd->fields) {
      auto field_ty_result = typeTerm(field.second, ctx, lvl);
      if (!field_ty_result.has_value()) {
        return binarysub::make_unexpected(field_ty_result.error());
      }
      fields.push_back({field.first, field_ty_result.value()});
    }

    return binarysub::make_record(std::move(fields));

  } else if (auto *let = std::get_if<Let>(&term->v)) {
    // Let binding: let name = rhs in body
    auto n_ty_result = typeLetRhs(let->isRec, let->name, let->rhs, ctx, lvl);
    if (!n_ty_result.has_value()) {
      return binarysub::make_unexpected(n_ty_result.error());
    }

    Ctx new_ctx = ctx;
    new_ctx[let->name] = TypeScheme(n_ty_result.value());

    return typeTerm(let->body, new_ctx, lvl);

  } else {
    assert(false && "Unhandled Term variant in typeTerm");
    return binarysub::make_unexpected(
        binarysub::Error::make("Unhandled Term variant"));
  }
}

} // namespace simplesub
