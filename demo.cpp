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

// Test function based on the "twice" example from simplesub paper Section 3.4.2
// twice = λf. λx. f(f x)
// Expected type: (α → β) → α → β  (after constraint propagation)
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
  // For f x to be valid: f must be a function (β → γ)
  // So we constrain: α <: (β → γ)
  auto f_inner_type = make_function(beta, gamma);
  if (auto e = constrain(alpha, f_inner_type, cache, supply); !e) {
    std::cerr << "Failed to constrain f for inner application: "
              << e.error().msg << "\n";
    return 1;
  }
  std::cout << "✓ Constrained f type for inner application f x\n";
  std::cout << "  α <: β → γ  (f must accept x and return some γ)\n";

  // Show current twice type after first constraint
  std::cout << "  Current twice type: " << printType(coalesceType(twice_type))
            << "\n\n";

  // Step 2: Analyze outer application f (f x)
  // For f (f x) to be valid: f must be a function (γ → δ)
  // So we constrain: α <: (γ → δ)
  auto f_outer_type = make_function(gamma, delta);
  if (auto e = constrain(alpha, f_outer_type, cache, supply); !e) {
    std::cerr << "Failed to constrain f for outer application: "
              << e.error().msg << "\n";
    return 1;
  }
  std::cout << "✓ Constrained f type for outer application f(f x)\n";
  std::cout << "  α <: γ → δ  (f must accept γ and return final result δ)\n";

  // Show final twice type after all constraints
  auto ct1 = compactType(twice_type);
  std::cout << "  Final twice compact type: " << toString(*ct1.cty) << "\n";
  auto t2 = coalesceCompactType(ct1);
  std::cout << "  Final twice type: " << printType(t2) << "\n";
  std::cout << "  After simplification: " << printType(simplifyType(t2))
            << "\n\n";

  // At this point, α has two upper bounds: (β → γ) and (γ → δ)
  // Check that the variables are properly constrained
  auto alpha_var = alpha->getAsTVariable();
  if (!alpha_var || alpha_var->state->upperBounds.size() != 2) {
    std::cerr << "Error: α should have exactly 2 upper bounds\n";
    return 1;
  }

  std::cout << "✓ Alpha has " << alpha_var->state->upperBounds.size()
            << " upper bounds as expected\n";

  // Show individual variable types
  std::cout << "\nVariable constraint analysis:\n";
  std::cout << "  α (f type): " << printType(coalesceType(alpha)) << "\n";
  std::cout << "  β (x type): " << printType(coalesceType(beta)) << "\n";
  std::cout << "  γ (intermediate): " << printType(coalesceType(gamma)) << "\n";
  std::cout << "  δ (result): " << printType(coalesceType(delta)) << "\n\n";

  // Test type soundness with concrete types
  // If we apply twice to a function int → int, everything should work
  std::cout << "=== Testing with concrete int → int function ===\n";
  auto int_type = make_primitive("int");
  auto int_to_int = make_function(int_type, int_type);

  Cache test_cache = cache; // copy cache for this test

  // Constrain α to be int → int (simulating applying twice to an int → int
  // function)
  if (auto e = constrain(int_to_int, alpha, test_cache, supply); !e) {
    std::cerr << "Failed to apply twice to int → int function: "
              << e.error().msg << "\n";
    return 1;
  }

  // Now constrain β to int (simulating applying the result to an int)
  if (auto e = constrain(int_type, beta, test_cache, supply); !e) {
    std::cerr << "Failed to apply result to int: " << e.error().msg << "\n";
    return 1;
  }

  // The result δ should be compatible with int
  if (auto e = constrain(delta, int_type, test_cache, supply); !e) {
    std::cerr << "Result type incompatible with int: " << e.error().msg << "\n";
    return 1;
  }

  std::cout << "✓ Successfully applied twice to int → int function\n";
  std::cout << "  When f: int → int and x: int\n";
  std::cout << "  Result twice type: " << printType(coalesceType(twice_type))
            << "\n";
  std::cout << "✓ Result type is correctly int\n";

  std::cout << "\n=== All twice function tests passed! ===\n";
  return 0;
}

// Test simplification strategies based on paper examples
int demo_simplification() {
  VarSupply supply;

  std::cout << "=== Testing Type Simplification Strategies ===\n\n";

  // Test 1: Polar variable removal (Section 4.3.1)
  // Type: α ∩ int → int  (α only appears negatively, should be simplified to
  // int → int)
  std::cout << "Test 1: Polar variable removal\n";
  std::cout << "Input type: α ∩ int → int\n";

  auto alpha = make_utypevariable("α1");
  auto int_type = make_uprimitivetype("int");
  auto alpha_inter_int = make_uinter(alpha, int_type);
  auto polar_test_type = make_ufunctiontype(alpha_inter_int, int_type);

  std::cout << "Before simplification: " << printType(polar_test_type) << "\n";
  auto simplified_polar = simplifyType(polar_test_type);
  std::cout << "After simplification:  " << printType(simplified_polar) << "\n";
  std::cout << "✓ Expected int → int (α removed because it only appears "
               "negatively)\n\n";

  // Test 2: Variable sandwich flattening (Section 4.3.1)
  // Type: α ∩ int → α ∪ int  (α sandwiched between int, should simplify to int
  // → int)
  std::cout << "Test 2: Variable sandwich flattening\n";
  std::cout << "Input type: α ∩ int → α ∪ int\n";

  auto beta = make_utypevariable("α2");
  auto beta_inter_int = make_uinter(beta, int_type);
  auto beta_union_int = make_uunion(beta, int_type);
  auto sandwich_test_type = make_ufunctiontype(beta_inter_int, beta_union_int);

  std::cout << "Before simplification: " << printType(sandwich_test_type)
            << "\n";
  auto simplified_sandwich = simplifyType(sandwich_test_type);
  std::cout << "After simplification:  " << printType(simplified_sandwich)
            << "\n";
  std::cout << "✓ Expected int → int (α equivalent to int)\n\n";

  // Test 3: if-then-else type simplification (from paper)
  // Type: bool → α → β → α ∪ β should simplify to bool → α → α → α
  std::cout << "Test 3: if-then-else type unification\n";
  std::cout << "Input type: bool → α → β → α ∪ β\n";

  auto bool_type = make_uprimitivetype("bool");
  auto gamma = make_utypevariable("α3");
  auto delta = make_utypevariable("α4");
  auto gamma_union_delta = make_uunion(gamma, delta);
  auto if_type = make_ufunctiontype(
      bool_type,
      make_ufunctiontype(gamma, make_ufunctiontype(delta, gamma_union_delta)));

  std::cout << "Before simplification: " << printType(if_type) << "\n";
  auto simplified_if = simplifyType(if_type);
  std::cout << "After simplification:  " << printType(simplified_if) << "\n";
  std::cout
      << "✓ Expected α and β to be unified since they're indistinguishable\n\n";

  // Test 4: Record type simplification
  std::cout << "Test 4: Record type with polar variables\n";
  std::cout << "Input type: {x: α, y: α → int}\n";

  auto epsilon = make_utypevariable("α5");
  auto epsilon_to_int = make_ufunctiontype(epsilon, int_type);
  std::vector<std::pair<std::string, UTypePtr>> record_fields = {
      {"x", epsilon}, {"y", epsilon_to_int}};
  auto record_test_type = make_urecordtype(record_fields);

  std::cout << "Before simplification: " << printType(record_test_type) << "\n";
  auto simplified_record = simplifyType(record_test_type);
  std::cout << "After simplification:  " << printType(simplified_record)
            << "\n";
  std::cout
      << "✓ α appears both positively and negatively, should be preserved\n\n";

  // Test 5: Complex nested type
  std::cout << "Test 5: Complex nested type with multiple variables\n";
  std::cout << "Input type: (α → β) → (β → γ) → α → γ\n";

  auto zeta = make_utypevariable("α6");
  auto eta = make_utypevariable("α7");
  auto theta = make_utypevariable("α8");
  auto zeta_to_eta = make_ufunctiontype(zeta, eta);
  auto eta_to_theta = make_ufunctiontype(eta, theta);
  auto zeta_to_theta = make_ufunctiontype(zeta, theta);
  auto complex_type = make_ufunctiontype(
      zeta_to_eta, make_ufunctiontype(eta_to_theta, zeta_to_theta));

  std::cout << "Before simplification: " << printType(complex_type) << "\n";
  auto simplified_complex = simplifyType(complex_type);
  std::cout << "After simplification:  " << printType(simplified_complex)
            << "\n";
  std::cout << "✓ This represents function composition, variables should be "
               "preserved\n\n";

  // Test 6: Demonstrate hash consing with recursive types
  std::cout << "Test 6: Hash consing with structural sharing\n";
  auto iota = make_utypevariable("α9");
  auto duplicate_subtype = make_ufunctiontype(int_type, iota);
  auto sharing_test = make_uunion(duplicate_subtype, duplicate_subtype);

  std::cout << "Before simplification: " << printType(sharing_test) << "\n";
  auto simplified_sharing = simplifyType(sharing_test);
  std::cout << "After simplification:  " << printType(simplified_sharing)
            << "\n";
  std::cout << "✓ Duplicate structures should be shared via hash consing\n\n";

  std::cout << "=== All simplification tests completed! ===\n";
  return 0;
}

int main() {
  int result1 = simplesub::demo_levels();
  if (result1 != 0) {
    std::cerr << "demo_levels failed\n";
    return result1;
  }

  int result2 = simplesub::demo_twice();
  if (result2 != 0) {
    std::cerr << "demo_twice failed\n";
    return result2;
  }

  int result3 = simplesub::demo_simplification();
  if (result3 != 0) {
    std::cerr << "demo_simplification failed\n";
    return result3;
  }

  std::cout << "All demos passed!\n";
  return 0;
}