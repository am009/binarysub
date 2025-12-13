#include "binarysub.h"
#include "simplesub-infer.h"
#include "simplesub-parser.h"
#include <cassert>
#include <iostream>

using namespace binarysub;

// Helper function to display CompactTypeScheme
void printCompactTypeScheme(const CompactTypeScheme &cts,
                            const std::string &title) {
  std::cout << title << ":\n";
  std::cout << "  Main type: " << toString(*cts.cty) << "\n";
  if (!cts.recVars.empty()) {
    std::cout << "  Recursive variables:\n";
    for (const auto &[varSimpleType, bound] : cts.recVars) {
      auto varPtr = extractVariableState(varSimpleType);
      std::cout << "    " << var_id_to_name(varPtr->id) << " = "
                << toString(*bound) << "\n";
    }
  }
  std::cout << "\n";
}

UTypePtr simplifyType(SimpleType ty, bool printDebug) {
  if (printDebug) {
    std::cout << "Original type: " << printType(coalesceType(ty)) << "\n";
  }

  // Process through the pipeline
  auto compact = compactType(ty);
  if (printDebug) {
    std::cout << "✓ Compacted successfully\n";
    printCompactTypeScheme(compact, "CompactType before simplification");
  }

  auto simplified = simplifyType(compact);
  if (printDebug) {
    std::cout << "✓ Simplified successfully\n";
    printCompactTypeScheme(simplified, "CompactType after simplification");
  }
  auto final = coalesceCompactType(simplified);

  // Normalize variable names to 'a, 'b, 'c, etc.
  auto normalized = normalizeVariableNames(final);

  if (printDebug) {
    std::cout << "Final type: " << printType(normalized) << "\n\n";
  }
  return normalized;
}

UTypePtr getTypeForExpr(const char *str, bool printDebug) {
  using namespace simplesub;
    if (printDebug) {
    std::cout << "[#] getTypeForExpr: infer type for: " << str << "\n";
  }
  auto [rest, term1] = parseTerm(str);
  if (!term1) {
    std::cout << __FILE__ << ":" << __LINE__ << ": ";
    std::cout << term1.error().msg << "\n";
    assert(false && "Type error in test!!");
  }
  if (printDebug) {
    std::cout << "  Parsed Term: " << term1.value()->str() + "\n";
  }
  auto typer = Typer();
  auto tyRes = typer.inferType(term1.value(), typer.getBuiltins(), 0);
  if (!tyRes) {
    std::cout << __FILE__ << ":" << __LINE__ << ": ";
    std::cout << tyRes.error().msg << "\n";
    assert(false && "Type error in test!!");
  }
  auto ty = tyRes.value();
  auto final = simplifyType(ty, printDebug);
  return final;
}

void doTest(const char *str, const char *expected) {
  auto ty = getTypeForExpr(str, !expected);
  if (expected) {
    auto strTy = printType(ty);
    if (strTy != expected) {
      std::cerr << "Error: Test Failed! expect: " << expected << "\n";
      std::cerr << "Got: " << strTy << "\n";
      assert(false && "Test Failed!");
    }
  }
}

// Enhanced doTest for programs with multiple definitions
void doTestProgram(const char *str, const std::vector<const char *> &expected) {
  using namespace simplesub;

  bool printDebug = false;
  for (auto exp : expected) {
    if (exp == nullptr || std::string(exp).empty()) {
      printDebug = true;
      break;
    }
  }

  // Parse the program
  auto [rest, pgrmResult] = parsePgrm(str);
  if (!pgrmResult) {
    std::cout << __FILE__ << ":" << __LINE__ << ": ";
    std::cout << "Parse error: " << pgrmResult.error().msg << "\n";
    assert(false && "Parse error in test!");
  }

  auto pgrm = pgrmResult.value();

  // Type inference
  auto typer = Typer();
  auto types = typer.inferTypes(pgrm, typer.getBuiltins());

  // Check that we have the right number of results
  assert(types.size() == expected.size() &&
         "Mismatch in number of definitions!");

  // Process each definition
  bool hasFailure = false;
  std::cout << "Processing " << types.size() << " definitions...\n";
  std::cout.flush();

  for (size_t i = 0; i < types.size(); i++) {
    std::cout << "Processing definition " << i << "...\n";

    auto &tyResult = types[i];
    auto exp = expected[i];

    if (!tyResult) {
      std::cout << __FILE__ << ":" << __LINE__ << ": ";
      std::cout << "Type error in definition " << i << ": "
                << tyResult.error().msg << "\n";

      hasFailure = true;
      continue;
    }

    auto polyTy = tyResult.value();

    // Instantiate at level 0
    VarSupply supply;
    auto ty = polyTy.body;

    std::cout << "Simplifying type for definition " << i << "...\n";

    // Simplify the type
    auto final = simplifyType(ty, printDebug);

    std::cout << "Printing type for definition " << i << "...\n";

    auto result = printType(final);

    std::cout << "Comparing result for definition " << i << "...\n";

    if (exp && std::string(exp).length() > 0) {
      if (result != exp) {
        std::cout << "Test failed for definition " << i << ":\n";
        std::cout << "  Expected: " << exp << "\n";
        std::cout << "  Got:      " << result << "\n";

        hasFailure = true;
      } else if (printDebug) {
        std::cout << "✓ Definition " << i << " passed: " << result << "\n";
      }
    } else {
      std::cout << "Definition " << i << ": " << result << "\n";
    }
  }

  if (hasFailure) {
    std::cout << "\n*** Test had failures! ***\n\n";
    assert(false && "Test Failed!");
  } else {
    std::cout << "All definitions passed!\n";
  }
}

// ======================= Test Cases from Scala ==============

int test_mlsub() {
  std::cout << "=== Testing mlsub examples ===\n";
  doTestProgram(R"(
    let id = fun x -> x
    let twice = fun f -> fun x -> f (f x)
    let object1 = { x = 42; y = id }
    let object2 = { x = 17; y = false }
    let pick_an_object = fun b ->
      if b then object1 else object2
    let rec recursive_monster = fun x ->
      { thing = x;
        self = recursive_monster x }
  )",
                {
                    "'a -> 'a",
                    "('a -> 'a & 'b) -> 'a -> 'b",
                    "{x: int, y: 'a -> 'a}",
                    "{x: int, y: bool}",
                    "bool -> {x: int, y: bool | ('a -> 'a)}",
                    "'a -> {self: 'b, thing: 'a} as 'b",
                });
  std::cout << "✓ test_mlsub passed\n\n";
  return 0;
}

int test_top_level_polymorphism() {
  std::cout << "=== Testing top-level polymorphism ===\n";
  doTestProgram(R"(
    let id = fun x -> x
    let ab = {u = id 0; v = id true}
  )",
                {
                    "'a -> 'a",
                    "{u: int, v: bool}",
                });
  std::cout << "✓ test_top_level_polymorphism passed\n\n";
  return 0;
}

int test_rec_producer_consumer() {
  std::cout << "=== Testing recursive producer-consumer ===\n";
  doTestProgram(R"(
    let rec produce = fun arg -> { head = arg; tail = produce (succ arg) }
    let rec consume = fun strm -> add strm.head (consume strm.tail)

    let codata = produce 42
    let res = consume codata

    let rec codata2 = { head = 0; tail = { head = 1; tail = codata2 } }
    let res = consume codata2

    let rec produce3 = fun b -> { head = 123; tail = if b then codata else codata2 }
    let res = fun x -> consume (produce3 x)

    let consume2 =
      let rec go = fun strm -> add strm.head (add strm.tail.head (go strm.tail.tail))
      in fun strm -> add strm.head (go strm.tail)
    let res = consume2 codata2
  )",
                {
                    "int -> {head: int, tail: 'a} as 'a",
                    "{head: int, tail: 'a} as 'a -> int",
                    "{head: int, tail: 'a} as 'a",
                    "int",
                    "{head: int, tail: {head: int, tail: 'a}} as 'a",
                    "int",
                    "bool -> {head: int, tail: {head: int, tail: 'a}} as 'a",
                    "bool -> int",
                    "{head: int, tail: {head: int, tail: 'a}} as 'a -> int",
                    "int",
                });
  std::cout << "✓ test_rec_producer_consumer passed\n\n";
  return 0;
}

int test_misc() {
  std::cout << "=== Testing misc examples ===\n";
  doTestProgram(
      R"(
    let rec r = fun a -> r
    let join = fun a -> fun b -> if true then a else b
    let s = join r r

    let rec f = fun x -> fun y -> add (f x.tail y) (f x y)
    let rec f = fun x -> fun y -> add (f x.tail y) (f y x)
    let rec f = fun x -> fun y -> add (f x.tail y) (f x y.tail)
    let rec f = fun x -> fun y -> add (f x.tail y.tail) (f x.tail y.tail)
    let rec f = fun x -> fun y -> add (f x.tail x.tail) (f y.tail y.tail)
    let rec f = fun x -> fun y -> add (f x.tail x) (f y.tail y)
    let rec f = fun x -> fun y -> add (f x.tail y) (f y.tail x)

    let f = fun x -> fun y -> if true then { l = x; r = y } else { l = y; r = x }

    let rec f = fun x -> fun y -> if true then x else { t = f x.t y.t }
  )",
      {
          "(⊤ -> 'a) as 'a",
          "'a -> 'a -> 'a",
          "(⊤ -> 'a) as 'a",

          "{tail: 'a} as 'a -> ⊤ -> int",
          "{tail: 'a} as 'a -> {tail: 'b} as 'b -> int",
          "{tail: 'a} as 'a -> {tail: 'b} as 'b -> int",
          "{tail: 'a} as 'a -> {tail: 'b} as 'b -> int",
          "{tail: {tail: 'a} as 'a} -> {tail: {tail: 'b} as 'b} -> int",
          "{tail: 'a} as 'a -> {tail: {tail: 'b} as 'b} -> int",
          "{tail: 'a} as 'a -> {tail: {tail: 'b} as 'b} -> int",

          "'a -> 'a -> {l: 'a, r: 'a}",

          "('b & {t: 'a}) as 'a -> {t: 'c} as 'c -> ('b | {t: 'd}) as 'd",
      });
  std::cout << "✓ test_misc passed\n\n";
  return 0;
}

int main() {
  std::cout << "\n=== Simple-sub Type Inference Tests ===\n\n";

  // Run the new test cases from Scala
  int result_mlsub = test_mlsub();
  if (result_mlsub != 0) {
    std::cerr << "test_mlsub failed\n";
    return result_mlsub;
  }

  int result_poly = test_top_level_polymorphism();
  if (result_poly != 0) {
    std::cerr << "test_top_level_polymorphism failed\n";
    return result_poly;
  }

  int result_rec = test_rec_producer_consumer();
  if (result_rec != 0) {
    std::cerr << "test_rec_producer_consumer failed\n";
    return result_rec;
  }

  int result_misc = test_misc();
  if (result_misc != 0) {
    std::cerr << "test_misc failed\n";
    return result_misc;
  }

  std::cout << "All tests passed! ✓\n";
  return 0;
}
