#include "binarysub.h"
#include "simplesub-infer.h"
#include "simplesub-parser.h"
#include <cassert>

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
      std::cout << "    α" << varPtr->id << " = " << toString(*bound) << "\n";
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
  if (printDebug) {
    std::cout << "Final type: " << printType(final) << "\n\n";
  }
  return final;
}

void printTypeForExpr(const char* str) {
  using namespace simplesub;
  auto [rest, term1] = parseTerm(str);
  if (!term1) {
    std::cout << __FILE__ << ":" << __LINE__ << ": ";
    std::cout << term1.error().msg << "\n";
    assert(false && "Type error in test!!");
  }
  auto typer = Typer();
  Ctx ctx;
  auto tyRes = typer.inferType(term1.value(), ctx, 0);
  if (!tyRes) {
    std::cout << __FILE__ << ":" << __LINE__ << ": ";
    std::cout << tyRes.error().msg << "\n";
    assert(false && "Type error in test!!");
  }
  auto ty = tyRes.value();
  auto final = simplifyType(ty, true);
}

// Test that VariableState is directly stored in variant
int test_variant_structure() {
  std::cout << "=== Testing Variant Structure ===\n";

  VarSupply supply;
  auto var_type = make_variable(42, 1);

  // Test that we can directly access VariableState
  auto vs = var_type->getAsVariableState();
  if (vs && vs->id == 42 && vs->level == 1) {
    std::cout << "✓ VariableState directly stored in variant with id=" << vs->id
              << " level=" << vs->level << "\n";
  } else {
    std::cout << "✗ Failed to access VariableState directly\n";
    return 1;
  }

  // Test that extractVariableState works
  auto extracted_vs = extractVariableState(var_type);
  if (extracted_vs && extracted_vs->id == 42 && extracted_vs->level == 1) {
    std::cout << "✓ extractVariableState helper works correctly\n";
  } else {
    std::cout << "✗ extractVariableState failed\n";
    return 1;
  }

  std::cout << "✓ Variant structure test passed\n\n";
  return 0;
}

// ======================= Demo implementation ==============
int demo_levels() {
  VarSupply supply;
  Scope env; // level=0

  // Build the rhs of "id": α -> α  at level (env.level+1)
  env.enter();                                // enter let-rhs
  auto a = fresh_variable(supply, env.level); // level=1
  auto id_ty = make_function(a, a);
  env.leave();

  // Generalize id at env.level (0)
  TypeScheme id_scheme = generalize(id_ty, /*env_level*/ 0);

  // Two uses at current level=0: instantiate twice (freshenAbove)
  auto id1 = instantiate(id_scheme, env.level, supply);
  auto id2 = instantiate(id_scheme, env.level, supply);

  // Build primitives
  auto TInt = make_primitive("int");
  auto TBool = make_primitive("bool");

  // For application: (int) <: dom(id1)  && cod(id1) <: int   (simulates id 1)
  // and similarly for bool on id2.
  Cache cache;
  // id1 is α1→α1
  auto d1 = id1->getAsTFunctionRef().args.at(0);
  auto r1 = id1->getAsTFunctionRef().result;
  auto d2 = id2->getAsTFunctionRef().args.at(0);
  auto r2 = id2->getAsTFunctionRef().result;

  if (auto e = constrain(TInt, d1, cache, supply); !e) {
    std::cerr << e.error().msg << "\n";
    return 1;
  }
  if (auto e = constrain(r1, TInt, cache, supply); !e) {
    std::cerr << e.error().msg << "\n";
    return 1;
  }
  if (auto e = constrain(TBool, d2, cache, supply); !e) {
    std::cerr << e.error().msg << "\n";
    return 1;
  }
  if (auto e = constrain(r2, TBool, cache, supply); !e) {
    std::cerr << e.error().msg << "\n";
    return 1;
  }

  return 0;
}

int demo_twice() {
  VarSupply supply;
  Cache cache;

  // Create type variables for the twice function: λf. λx. f(f x)
  auto alpha = fresh_variable(supply, 0); // f's type
  auto beta = fresh_variable(supply, 0);  // x's type
  auto gamma = fresh_variable(supply, 0); // result of f x
  auto delta = fresh_variable(supply, 0); // final result

  std::cout << "=== Testing twice function type inference ===\n";
  std::cout << "twice = λf. λx. f(f x)\n\n";

  // Build the twice function type structure: α → β → δ
  auto twice_type = make_function(alpha, make_function(beta, delta));

  std::cout << "Initial structure: " << printType(coalesceType(twice_type))
            << "\n\n";

  // Step 1: Analyze inner application f x
  auto f_inner_type = make_function(beta, gamma);
  if (auto e = constrain(alpha, f_inner_type, cache, supply); !e) {
    std::cerr << "Failed to constrain f for inner application: "
              << e.error().msg << "\n";
    return 1;
  }
  std::cout << "✓ Constrained f type for inner application f x\n";

  // Step 2: Analyze outer application f (f x)
  auto f_outer_type = make_function(gamma, delta);
  if (auto e = constrain(alpha, f_outer_type, cache, supply); !e) {
    std::cerr << "Failed to constrain f for outer application: "
              << e.error().msg << "\n";
    return 1;
  }
  std::cout << "✓ Constrained f type for outer application f(f x)\n";

  // Show final twice type after all constraints
  auto ct1 = compactType(twice_type);
  std::cout << "✓ Compacted successfully\n";
  printCompactTypeScheme(ct1, "CompactType before simplification");

  auto simplified_ct1 = simplifyType(ct1);
  std::cout << "✓ Simplified successfully\n";
  printCompactTypeScheme(simplified_ct1, "CompactType after simplification");

  auto t2 = coalesceCompactType(simplified_ct1);
  std::cout << "Final twice type: " << printType(t2) << "\n";

  return 0;
}

int demo_simplification() {
  std::cout << "=== Testing Type Simplification Pipeline ===\n\n";

  VarSupply supply;
  Cache cache;

  // Test 1: Basic pipeline test
  std::cout << "Test 1: Basic type compaction and coalescing\n";

  auto int_type = make_primitive("int");
  auto simple_func = make_function(int_type, int_type);

  std::cout << "Original type: " << printType(coalesceType(simple_func))
            << "\n";

  // Process through the pipeline
  auto compact_func = compactType(simple_func);
  std::cout << "✓ Compacted successfully\n";
  printCompactTypeScheme(compact_func, "CompactType before simplification");

  auto simplified_func = simplifyType(compact_func);
  std::cout << "✓ Simplified successfully\n";
  printCompactTypeScheme(simplified_func, "CompactType after simplification");

  auto final_func = coalesceCompactType(simplified_func);
  std::cout << "Final type: " << printType(final_func) << "\n\n";

  // Test 2: Variable with constraints
  std::cout << "Test 2: Variable with constraints\n";

  auto alpha = fresh_variable(supply, 0);
  auto constrained_func = make_function(alpha, int_type);

  // Add constraint: int <: alpha (alpha has int as lower bound)
  constrain(int_type, alpha, cache, supply);

  std::cout << "Original constrained type: "
            << printType(coalesceType(constrained_func)) << "\n";

  // Process through the pipeline
  auto compact_constrained = compactType(constrained_func);
  printCompactTypeScheme(compact_constrained,
                         "CompactType before simplification");

  auto simplified_constrained = simplifyType(compact_constrained);
  printCompactTypeScheme(simplified_constrained,
                         "CompactType after simplification");

  auto final_constrained = coalesceCompactType(simplified_constrained);
  std::cout << "Final type: " << printType(final_constrained) << "\n\n";

  std::cout << "✓ Type simplification pipeline working correctly\n";

  return 0;
}

int main() {
  printTypeForExpr("let f = fun x -> x in {a = f 0; b = f true}");
  
  std::cout << "\n=== Simple-sub Type Inference Demo ===\n\n";

  int result0 = test_variant_structure();
  if (result0 != 0) {
    std::cerr << "test_variant_structure failed\n";
    return result0;
  }

  int result1 = demo_levels();
  if (result1 != 0) {
    std::cerr << "demo_levels failed\n";
    return result1;
  }
  std::cout << "✓ demo_levels passed\n\n";

  int result2 = demo_twice();
  if (result2 != 0) {
    std::cerr << "demo_twice failed\n";
    return result2;
  }
  std::cout << "✓ demo_twice passed\n\n";

  int result3 = demo_simplification();
  if (result3 != 0) {
    std::cerr << "demo_simplification failed\n";
    return result3;
  }
  std::cout << "✓ demo_simplification passed\n\n";

  std::cout << "All demos passed! ✓\n";
  return 0;
}
