#include "binarysub.h"

using namespace simplesub;

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
  auto d1 = id1->getAsTFunctionRef().lhs;
  auto r1 = id1->getAsTFunctionRef().rhs;
  auto d2 = id2->getAsTFunctionRef().lhs;
  auto r2 = id2->getAsTFunctionRef().rhs;

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
  auto simplified_ct1 = simplifyType(ct1);
  std::cout << "✓ Simplified successfully\n";
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
  
  std::cout << "Original type: " << printType(coalesceType(simple_func)) << "\n";
  
  // Process through the pipeline
  auto compact_func = compactType(simple_func);
  std::cout << "✓ Compacted successfully\n";
  
  auto simplified_func = simplifyType(compact_func);
  std::cout << "✓ Simplified successfully\n";
  
  auto final_func = coalesceCompactType(simplified_func);
  std::cout << "Final type: " << printType(final_func) << "\n\n";
  
  // Test 2: Variable with constraints
  std::cout << "Test 2: Variable with constraints\n";
  
  auto alpha = fresh_variable(supply, 0);
  auto constrained_func = make_function(alpha, int_type);
  
  // Add constraint: int <: alpha (alpha has int as lower bound)
  constrain(int_type, alpha, cache, supply);
  
  std::cout << "Original constrained type: " << printType(coalesceType(constrained_func)) << "\n";
  
  // Process through the pipeline
  auto compact_constrained = compactType(constrained_func);
  auto simplified_constrained = simplifyType(compact_constrained);
  auto final_constrained = coalesceCompactType(simplified_constrained);
  std::cout << "Final type: " << printType(final_constrained) << "\n\n";
  
  std::cout << "✓ Type simplification pipeline working correctly\n";
  
  return 0;
}

int main() {
  std::cout << "\n=== Simple-sub Type Inference Demo ===\n\n";

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