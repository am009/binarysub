#include "simplesub-parser.h"
#include <cctype>
#include <set>

namespace simplesub {

// ======================= Utility Functions ========================

static const std::set<std::string> keywords = {
    "let", "rec", "in", "fun", "if", "then", "else", "true", "false"};

std::string skipWhitespace(const std::string &str) {
  size_t i = 0;
  while (i < str.size() && std::isspace(str[i])) {
    ++i;
  }
  return str.substr(i);
}

bool isLetter(char c) {
  return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z');
}

bool isDigit(char c) { return c >= '0' && c <= '9'; }

bool isKeyword(const std::string &str) {
  return keywords.find(str) != keywords.end();
}

// ======================= Basic Parsers ========================

ParseResultT<int> parseNumber(const std::string &str) {
  std::string rest = skipWhitespace(str);
  if (rest.empty() || !isDigit(rest[0])) {
    return {rest, binarysub::make_unexpected(
                      binarysub::Error::make("parseNumber: Expected number"))};
  }

  size_t end = 0;
  while (end < rest.size() && isDigit(rest[end])) {
    ++end;
  }

  int num = std::stoi(rest.substr(0, end));
  return {rest.substr(end), num};
}

ParseResultT<std::string> parseIdent(const std::string &str) {
  std::string rest = skipWhitespace(str);
  if (rest.empty() || !(isLetter(rest[0]) || rest[0] == '_')) {
    return {rest, binarysub::make_unexpected(
                      binarysub::Error::make("parseIdent: Expected identifier"))};
  }

  size_t end = 0;
  while (end < rest.size() &&
         (isLetter(rest[end]) || isDigit(rest[end]) || rest[end] == '_' ||
          rest[end] == '\'')) {
    ++end;
  }

  std::string ident = rest.substr(0, end);
  if (isKeyword(ident)) {
    return {rest, binarysub::make_unexpected(binarysub::Error::make(
                      "parseIdent: Identifier is a keyword"))};
  }

  return {rest.substr(end), ident};
}

// ======================= Helper Functions ========================

static bool consumeKeyword(std::string &str, const std::string &kw) {
  std::string rest = skipWhitespace(str);
  if (rest.size() >= kw.size() && rest.substr(0, kw.size()) == kw) {
    // Check that keyword is not followed by letter/digit/_/'
    if (rest.size() > kw.size()) {
      char next = rest[kw.size()];
      if (isLetter(next) || isDigit(next) || next == '_' || next == '\'') {
        return false;
      }
    }
    str = rest.substr(kw.size());
    return true;
  }
  return false;
}

static bool consumeChar(std::string &str, char c) {
  std::string rest = skipWhitespace(str);
  if (!rest.empty() && rest[0] == c) {
    str = rest.substr(1);
    return true;
  }
  return false;
}

static bool consumeString(std::string &str, const std::string &s) {
  std::string rest = skipWhitespace(str);
  if (rest.size() >= s.size() && rest.substr(0, s.size()) == s) {
    str = rest.substr(s.size());
    return true;
  }
  return false;
}

// ======================= Term Parsers ========================

ParseResultT<TermPtr> parseConst(const std::string &str) {
  auto [rest, result] = parseNumber(str);
  if (!result) {
    return {rest, binarysub::make_unexpected(result.error())};
  }
  return {rest, make_lit(result.value())};
}

ParseResultT<TermPtr> parseVariable(const std::string &str) {
  std::string rest = skipWhitespace(str);

  // Check for "true" or "false"
  if (rest.size() >= 4 && rest.substr(0, 4) == "true") {
    char next = rest.size() > 4 ? rest[4] : '\0';
    if (!isLetter(next) && !isDigit(next) && next != '_' && next != '\'') {
      return {rest.substr(4), make_var("true")};
    }
  }
  if (rest.size() >= 5 && rest.substr(0, 5) == "false") {
    char next = rest.size() > 5 ? rest[5] : '\0';
    if (!isLetter(next) && !isDigit(next) && next != '_' && next != '\'') {
      return {rest.substr(5), make_var("false")};
    }
  }

  auto [rest2, result] = parseIdent(str);
  if (!result) {
    return {rest2, binarysub::make_unexpected(result.error())};
  }
  return {rest2, make_var(result.value())};
}

ParseResultT<TermPtr> parseParens(const std::string &str);
ParseResultT<TermPtr> parseRecord(const std::string &str);
ParseResultT<TermPtr> parseSubtermNoSel(const std::string &str);
ParseResultT<TermPtr> parseSubterm(const std::string &str);
ParseResultT<TermPtr> parseFun(const std::string &str);
ParseResultT<TermPtr> parseLet(const std::string &str);
ParseResultT<TermPtr> parseIte(const std::string &str);
ParseResultT<TermPtr> parseApps(const std::string &str);
ParseResultT<TermPtr> parseTerm(const std::string &str);

ParseResultT<TermPtr> parseParens(const std::string &str) {
  std::string rest = str;
  if (!consumeChar(rest, '(')) {
    return {rest, binarysub::make_unexpected(
                      binarysub::Error::make("parseParens: Expected '('"))};
  }

  auto [rest2, term] = parseTerm(rest);
  if (!term) {
    return {rest2, binarysub::make_unexpected(term.error())};
  }

  rest = rest2;
  if (!consumeChar(rest, ')')) {
    return {rest, binarysub::make_unexpected(
                      binarysub::Error::make("parseParens: Expected ')'"))};
  }

  return {rest, term.value()};
}

ParseResultT<TermPtr> parseRecord(const std::string &str) {
  std::string rest = str;
  if (!consumeChar(rest, '{')) {
    return {rest, binarysub::make_unexpected(
                      binarysub::Error::make("parseRecord: Expected '{'"))};
  }

  std::vector<std::pair<std::string, TermPtr>> fields;
  std::set<std::string> fieldNames;

  rest = skipWhitespace(rest);
  if (!rest.empty() && rest[0] == '}') {
    rest = rest.substr(1);
    return {rest, make_rcd(fields)};
  }

  while (true) {
    auto [rest2, ident] = parseIdent(rest);
    if (!ident) {
      return {rest2, binarysub::make_unexpected(ident.error())};
    }

    rest = rest2;
    if (!consumeChar(rest, '=')) {
      return {rest, binarysub::make_unexpected(
                        binarysub::Error::make("parseRecord: Expected '='"))};
    }

    auto [rest3, term] = parseTerm(rest);
    if (!term) {
      return {rest3, binarysub::make_unexpected(term.error())};
    }

    // Check for duplicate field names
    if (fieldNames.find(ident.value()) != fieldNames.end()) {
      return {rest3,
              binarysub::make_unexpected(binarysub::Error::make(
                  "parseRecord: Duplicate field name: " + ident.value()))};
    }
    fieldNames.insert(ident.value());
    fields.push_back({ident.value(), term.value()});

    rest = rest3;
    rest = skipWhitespace(rest);

    if (!rest.empty() && rest[0] == '}') {
      rest = rest.substr(1);
      break;
    }

    if (!consumeChar(rest, ';')) {
      return {rest, binarysub::make_unexpected(
                        binarysub::Error::make("parseRecord: Expected ';' or '}'"))};
    }

    rest = skipWhitespace(rest);
    if (!rest.empty() && rest[0] == '}') {
      rest = rest.substr(1);
      break;
    }
  }

  return {rest, make_rcd(fields)};
}

ParseResultT<TermPtr> parseSubtermNoSel(const std::string &str) {
  std::string rest = skipWhitespace(str);

  // Try parens
  if (!rest.empty() && rest[0] == '(') {
    return parseParens(str);
  }

  // Try record
  if (!rest.empty() && rest[0] == '{') {
    return parseRecord(str);
  }

  // Try const
  if (!rest.empty() && isDigit(rest[0])) {
    return parseConst(str);
  }

  // Try variable
  return parseVariable(str);
}

ParseResultT<TermPtr> parseSubterm(const std::string &str) {
  auto [rest, st] = parseSubtermNoSel(str);
  if (!st) {
    return {rest, binarysub::make_unexpected(st.error())};
  }

  TermPtr result = st.value();
  std::string current = rest;

  while (true) {
    current = skipWhitespace(current);
    if (current.empty() || current[0] != '.') {
      break;
    }
    current = current.substr(1); // consume '.'

    auto [rest2, fieldName] = parseIdent(current);
    if (!fieldName) {
      return {rest2, binarysub::make_unexpected(fieldName.error())};
    }

    result = make_sel(result, fieldName.value());
    current = rest2;
  }

  return {current, result};
}

ParseResultT<TermPtr> parseFun(const std::string &str) {
  std::string rest = str;
  if (!consumeKeyword(rest, "fun")) {
    return {rest, binarysub::make_unexpected(
                      binarysub::Error::make("parseFun: Expected 'fun'"))};
  }

  auto [rest2, name] = parseIdent(rest);
  if (!name) {
    return {rest2, binarysub::make_unexpected(name.error())};
  }

  rest = rest2;
  if (!consumeString(rest, "->")) {
    return {rest, binarysub::make_unexpected(
                      binarysub::Error::make("parseFun: Expected '->'"))};
  }

  auto [rest3, body] = parseTerm(rest);
  if (!body) {
    return {rest3, binarysub::make_unexpected(body.error())};
  }

  return {rest3, make_lam(name.value(), body.value())};
}

ParseResultT<TermPtr> parseLet(const std::string &str) {
  std::string rest = str;
  if (!consumeKeyword(rest, "let")) {
    return {rest, binarysub::make_unexpected(
                      binarysub::Error::make("parseLet: Expected 'let'"))};
  }

  bool isRec = consumeKeyword(rest, "rec");

  auto [rest2, name] = parseIdent(rest);
  if (!name) {
    return {rest2, binarysub::make_unexpected(name.error())};
  }

  rest = rest2;
  if (!consumeChar(rest, '=')) {
    return {rest, binarysub::make_unexpected(
                      binarysub::Error::make("parseLet: Expected '='"))};
  }

  auto [rest3, rhs] = parseTerm(rest);
  if (!rhs) {
    return {rest3, binarysub::make_unexpected(rhs.error())};
  }

  rest = rest3;
  if (!consumeKeyword(rest, "in")) {
    return {rest, binarysub::make_unexpected(
                      binarysub::Error::make("parseLet: Expected 'in'"))};
  }

  auto [rest4, body] = parseTerm(rest);
  if (!body) {
    return {rest4, binarysub::make_unexpected(body.error())};
  }

  return {rest4, make_let(isRec, name.value(), rhs.value(), body.value())};
}

ParseResultT<TermPtr> parseIte(const std::string &str) {
  std::string rest = str;
  if (!consumeKeyword(rest, "if")) {
    return {rest, binarysub::make_unexpected(
                      binarysub::Error::make("parseIte: Expected 'if'"))};
  }

  auto [rest2, cond] = parseTerm(rest);
  if (!cond) {
    return {rest2, binarysub::make_unexpected(cond.error())};
  }

  rest = rest2;
  if (!consumeKeyword(rest, "then")) {
    return {rest, binarysub::make_unexpected(
                      binarysub::Error::make("parseIte: Expected 'then'"))};
  }

  auto [rest3, thenBranch] = parseTerm(rest);
  if (!thenBranch) {
    return {rest3, binarysub::make_unexpected(thenBranch.error())};
  }

  rest = rest3;
  if (!consumeKeyword(rest, "else")) {
    return {rest, binarysub::make_unexpected(
                      binarysub::Error::make("parseIte: Expected 'else'"))};
  }

  auto [rest4, elseBranch] = parseTerm(rest);
  if (!elseBranch) {
    return {rest4, binarysub::make_unexpected(elseBranch.error())};
  }

  // Desugar: if cond then thenBranch else elseBranch
  // becomes: ((if cond) thenBranch) elseBranch
  TermPtr ifVar = make_var("if");
  TermPtr app1 = make_app(ifVar, cond.value());
  TermPtr app2 = make_app(app1, thenBranch.value());
  TermPtr app3 = make_app(app2, elseBranch.value());

  return {rest4, app3};
}

ParseResultT<TermPtr> parseApps(const std::string &str) {
  std::vector<TermPtr> terms;
  std::string rest = str;

  while (true) {
    auto [rest2, term] = parseSubterm(rest);
    if (!term) {
      if (terms.empty()) {
        return {rest2, binarysub::make_unexpected(term.error())};
      }
      break;
    }

    terms.push_back(term.value());
    rest = rest2;

    // Check if we can continue parsing more subterms
    std::string peek = skipWhitespace(rest);
    if (peek.empty()) {
      break;
    }

    // Stop if we see a keyword or closing delimiter
    char c = peek[0];
    if (c == ')' || c == '}' || c == ';') {
      break;
    }

    // Check for keywords
    bool isKw = false;
    for (const auto &kw : keywords) {
      if (kw == "true" || kw == "false") continue;
      if (peek.size() >= kw.size() && peek.substr(0, kw.size()) == kw) {
        if (peek.size() == kw.size() ||
            (!isLetter(peek[kw.size()]) && !isDigit(peek[kw.size()]) &&
             peek[kw.size()] != '_' && peek[kw.size()] != '\'')) {
          isKw = true;
          break;
        }
      }
    }
    if (isKw) {
      break;
    }
  }

  if (terms.empty()) {
    return {rest, binarysub::make_unexpected(
                      binarysub::Error::make("parseApps: Expected at least one term"))};
  }

  // Left-associate applications
  TermPtr result = terms[0];
  for (size_t i = 1; i < terms.size(); ++i) {
    result = make_app(result, terms[i]);
  }

  return {rest, result};
}

ParseResultT<TermPtr> parseTerm(const std::string &str) {
  std::string rest = skipWhitespace(str);

  // Try let
  if (rest.size() >= 3 && rest.substr(0, 3) == "let") {
    char next = rest.size() > 3 ? rest[3] : '\0';
    if (!isLetter(next) && !isDigit(next) && next != '_' && next != '\'') {
      return parseLet(str);
    }
  }

  // Try fun
  if (rest.size() >= 3 && rest.substr(0, 3) == "fun") {
    char next = rest.size() > 3 ? rest[3] : '\0';
    if (!isLetter(next) && !isDigit(next) && next != '_' && next != '\'') {
      return parseFun(str);
    }
  }

  // Try if
  if (rest.size() >= 2 && rest.substr(0, 2) == "if") {
    char next = rest.size() > 2 ? rest[2] : '\0';
    if (!isLetter(next) && !isDigit(next) && next != '_' && next != '\'') {
      return parseIte(str);
    }
  }

  // Default to expr or apps
  return parseApps(str);
}

// ======================= Top-level Parsers ========================

ParseResultT<TermPtr> parseExpr(const std::string &str) {
  auto [rest, term] = parseTerm(str);
  if (!term) {
    return {rest, binarysub::make_unexpected(term.error())};
  }

  rest = skipWhitespace(rest);
  if (!rest.empty()) {
    return {rest, binarysub::make_unexpected(binarysub::Error::make(
                      "parseExpr: Unexpected input after expression"))};
  }

  return {rest, term.value()};
}

ParseResultT<std::tuple<bool, std::string, TermPtr>>
parseToplvl(const std::string &str) {
  std::string rest = str;
  if (!consumeKeyword(rest, "let")) {
    return {rest, binarysub::make_unexpected(
                      binarysub::Error::make("parseToplvl: Expected 'let'"))};
  }

  bool isRec = consumeKeyword(rest, "rec");

  auto [rest2, name] = parseIdent(rest);
  if (!name) {
    return {rest2, binarysub::make_unexpected(name.error())};
  }

  rest = rest2;
  if (!consumeChar(rest, '=')) {
    return {rest, binarysub::make_unexpected(
                      binarysub::Error::make("parseToplvl: Expected '='"))};
  }

  auto [rest3, rhs] = parseTerm(rest);
  if (!rhs) {
    return {rest3, binarysub::make_unexpected(rhs.error())};
  }

  return {rest3, std::make_tuple(isRec, name.value(), rhs.value())};
}

ParseResultT<Pgrm> parsePgrm(const std::string &str) {
  std::vector<std::tuple<bool, std::string, TermPtr>> defs;
  std::string rest = skipWhitespace(str);

  while (!rest.empty()) {
    auto [rest2, def] = parseToplvl(rest);
    if (!def) {
      return {rest2, binarysub::make_unexpected(def.error())};
    }

    defs.push_back(def.value());
    rest = skipWhitespace(rest2);
  }

  return {rest, Pgrm{defs}};
}

} // namespace simplesub
