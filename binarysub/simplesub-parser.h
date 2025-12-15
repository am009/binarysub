#ifndef SIMPLESUB_PARSER_H
#define SIMPLESUB_PARSER_H

#include "binarysub-utils.h"
#include <memory>
#include <string>
#include <variant>
#include <vector>

namespace simplesub {

// ======================= AST Types ========================

// Forward declarations
struct Term;
using TermPtr = std::shared_ptr<Term>;

// Term types
struct Lit {
  int value;
};

struct Var {
  std::string name;
};

struct Lam {
  std::string name;
  TermPtr rhs;
};

struct App {
  TermPtr lhs;
  TermPtr rhs;
};

struct Rcd {
  std::vector<std::pair<std::string, TermPtr>> fields;
};

struct Sel {
  TermPtr receiver;
  std::string fieldName;
};

struct Let {
  bool isRec;
  std::string name;
  TermPtr rhs;
  TermPtr body;
};

struct Term {
  std::variant<Lit, Var, Lam, App, Rcd, Sel, Let> v;

  explicit Term(Lit l) : v(std::move(l)) {}
  explicit Term(Var var) : v(std::move(var)) {}
  explicit Term(Lam lam) : v(std::move(lam)) {}
  explicit Term(App app) : v(std::move(app)) {}
  explicit Term(Rcd rcd) : v(std::move(rcd)) {}
  explicit Term(Sel sel) : v(std::move(sel)) {}
  explicit Term(Let let) : v(std::move(let)) {}

  template <typename T> T *getAs() { return std::get_if<T>(&v); }

  template <typename T> const T *getAs() const { return std::get_if<T>(&v); }

  std::string str() const;
};

// Helper functions to create Term instances
inline TermPtr make_lit(int value) {
  return std::make_shared<Term>(Lit{value});
}

inline TermPtr make_var(std::string name) {
  return std::make_shared<Term>(Var{std::move(name)});
}

inline TermPtr make_lam(std::string name, TermPtr rhs) {
  return std::make_shared<Term>(Lam{std::move(name), std::move(rhs)});
}

inline TermPtr make_app(TermPtr lhs, TermPtr rhs) {
  return std::make_shared<Term>(App{std::move(lhs), std::move(rhs)});
}

inline TermPtr make_rcd(std::vector<std::pair<std::string, TermPtr>> fields) {
  return std::make_shared<Term>(Rcd{std::move(fields)});
}

inline TermPtr make_sel(TermPtr receiver, std::string fieldName) {
  return std::make_shared<Term>(Sel{std::move(receiver), std::move(fieldName)});
}

inline TermPtr make_let(bool isRec, std::string name, TermPtr rhs,
                        TermPtr body) {
  return std::make_shared<Term>(
      Let{isRec, std::move(name), std::move(rhs), std::move(body)});
}

// Program structure
struct Pgrm {
  std::vector<std::tuple<bool, std::string, TermPtr>> defs;
};

// ======================= Parser Result Types ========================

template <typename T>
using ParseResultT =
    std::pair<std::string, binarysub::expected<T, binarysub::Error>>;

// ======================= Parser Functions ========================

// Utility functions
std::string skipWhitespace(const std::string &str);
bool isLetter(char c);
bool isDigit(char c);
bool isKeyword(const std::string &str);

// Basic parsers
ParseResultT<int> parseNumber(const std::string &str);
ParseResultT<std::string> parseIdent(const std::string &str);

// Term parsers
ParseResultT<TermPtr> parseTerm(const std::string &str);
ParseResultT<TermPtr> parseConst(const std::string &str);
ParseResultT<TermPtr> parseVariable(const std::string &str);
ParseResultT<TermPtr> parseParens(const std::string &str);
ParseResultT<TermPtr> parseRecord(const std::string &str);
ParseResultT<TermPtr> parseSubtermNoSel(const std::string &str);
ParseResultT<TermPtr> parseSubterm(const std::string &str);
ParseResultT<TermPtr> parseFun(const std::string &str);
ParseResultT<TermPtr> parseLet(const std::string &str);
ParseResultT<TermPtr> parseIte(const std::string &str);
ParseResultT<TermPtr> parseApps(const std::string &str);

// Top-level parsers
ParseResultT<TermPtr> parseExpr(const std::string &str);
ParseResultT<std::tuple<bool, std::string, TermPtr>>
parseToplvl(const std::string &str);
ParseResultT<Pgrm> parsePgrm(const std::string &str);

} // namespace simplesub

#endif // SIMPLESUB_PARSER_H
