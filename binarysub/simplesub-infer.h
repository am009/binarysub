#ifndef SIMPLESUB_INFER_H
#define SIMPLESUB_INFER_H

#include "binarysub-core.h"
#include "binarysub-utils.h"
#include "simplesub-parser.h"
#include <map>
#include <optional>
#include <string>
#include <variant>
#include <vector>

namespace simplesub {

// ======================= Type Scheme ========================

// Forward declaration
struct TypeScheme;

// A type with universally quantified type variables
struct PolymorphicType {
  int level;
  binarysub::SimpleType body;

  PolymorphicType(int lvl, binarysub::SimpleType b)
    : level(lvl), body(std::move(b)) {}
};

// A type scheme can be either a SimpleType or a PolymorphicType
struct TypeScheme {
  std::variant<binarysub::SimpleType, PolymorphicType> v;

  explicit TypeScheme(binarysub::SimpleType st) : v(std::move(st)) {}
  explicit TypeScheme(PolymorphicType pt) : v(std::move(pt)) {}

  // Instantiate the type scheme at a given level
  binarysub::SimpleType instantiate(int lvl, binarysub::VarSupply& supply);
};

// ======================= Typer Context ========================

using Ctx = std::map<std::string, std::optional<TypeScheme>>;

// ======================= Typer Class ========================

class Typer {
public:
  Typer();

  // Main type inference function for a program
  std::vector<binarysub::expected<PolymorphicType, binarysub::Error>>
    inferTypes(const Pgrm& pgrm, const Ctx& ctx);

  // Infer the type of a single term
  binarysub::expected<binarysub::SimpleType, binarysub::Error>
    inferType(const TermPtr& term, const Ctx& ctx, int lvl);

  // Get the built-in context
  const Ctx& getBuiltins() const { return builtins; }

private:
  binarysub::VarSupply supply;
  binarysub::Scope scope;
  Ctx builtins;

  // Infer the type of a let binding right-hand side
  binarysub::expected<PolymorphicType, binarysub::Error>
    typeLetRhs(bool isRec, const std::string& name, const TermPtr& rhs,
               const Ctx& ctx, int lvl);

  // Infer the type of a term (internal implementation)
  binarysub::expected<binarysub::SimpleType, binarysub::Error>
    typeTerm(const TermPtr& term, const Ctx& ctx, int lvl);

  // Freshen type variables above a certain level
  binarysub::SimpleType freshenAbove(int lim, const binarysub::SimpleType& ty, int lvl);
};

} // namespace simplesub

#endif // SIMPLESUB_INFER_H
