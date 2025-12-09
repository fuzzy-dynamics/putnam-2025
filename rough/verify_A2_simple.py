#!/usr/bin/env python3
"""
Verification script for Putnam 2025 A2 solution.

Problem: Find the largest a and smallest b such that
ax(pi-x) <= sin(x) <= bx(pi-x) for all x in [0, pi]

Claimed solution: a = 1/pi, b = 4/pi^2
"""

import numpy as np

def main():
    print("=" * 80)
    print("VERIFICATION OF PUTNAM 2025 A2 SOLUTION")
    print("=" * 80)
    print()

    # Claimed values
    a = 1 / np.pi
    b = 4 / (np.pi ** 2)

    print(f"Claimed values:")
    print(f"  a = 1/pi = {a:.10f}")
    print(f"  b = 4/pi^2 = {b:.10f}")
    print()

    # Define the function g(x) = sin(x) / (x(pi-x))
    def g(x):
        """The ratio sin(x) / (x(pi-x))"""
        if np.isscalar(x):
            if x <= 0 or x >= np.pi:
                return np.nan
            return np.sin(x) / (x * (np.pi - x))
        else:
            result = np.zeros_like(x, dtype=float)
            mask = (x > 0) & (x < np.pi)
            result[mask] = np.sin(x[mask]) / (x[mask] * (np.pi - x[mask]))
            result[~mask] = np.nan
            return result

    # ========================================================================
    # TEST 1: Verify endpoint limits
    # ========================================================================
    print("TEST 1: Endpoint Limits")
    print("-" * 80)

    # Check limit as x -> 0+
    x_near_0 = np.array([1e-6, 1e-7, 1e-8, 1e-9, 1e-10])
    g_near_0 = g(x_near_0)

    print(f"Limit as x -> 0+:")
    for i in range(min(3, len(x_near_0))):
        print(f"  g({x_near_0[i]:.2e}) = {g_near_0[i]:.10f}")
    print(f"  ...")
    print(f"  g({x_near_0[-1]:.2e}) = {g_near_0[-1]:.10f}")
    print(f"  Expected: 1/pi = {1/np.pi:.10f}")
    print(f"  Error from 1/pi: {abs(g_near_0[-1] - 1/np.pi):.2e}")

    # Check limit as x -> pi-
    x_near_pi = np.pi - x_near_0
    g_near_pi = g(x_near_pi)

    print(f"\nLimit as x -> pi-:")
    for i in range(min(3, len(x_near_pi))):
        print(f"  g({x_near_pi[i]:.10f}) = {g_near_pi[i]:.10f}")
    print(f"  ...")
    print(f"  g({x_near_pi[-1]:.10f}) = {g_near_pi[-1]:.10f}")
    print(f"  Expected: 1/pi = {1/np.pi:.10f}")
    print(f"  Error from 1/pi: {abs(g_near_pi[-1] - 1/np.pi):.2e}")

    # More lenient tolerance for extreme values near endpoints
    limit_test_pass = (abs(g_near_0[-1] - 1/np.pi) < 1e-6 and
                       abs(g_near_pi[-1] - 1/np.pi) < 1e-6)
    print(f"\n{'PASS' if limit_test_pass else 'FAIL'}: Endpoint limits converge to 1/pi")
    print()

    # ========================================================================
    # TEST 2: Verify symmetry g(pi - x) = g(x)
    # ========================================================================
    print("TEST 2: Symmetry")
    print("-" * 80)

    x_test = np.linspace(0.1, np.pi - 0.1, 50)
    g_x = g(x_test)
    g_pi_minus_x = g(np.pi - x_test)

    max_symmetry_error = np.max(np.abs(g_x - g_pi_minus_x))
    print(f"Max |g(x) - g(pi-x)| = {max_symmetry_error:.2e}")

    symmetry_test_pass = max_symmetry_error < 1e-14
    print(f"{'PASS' if symmetry_test_pass else 'FAIL'}: Function is symmetric about pi/2")
    print()

    # ========================================================================
    # TEST 3: Verify critical point at x = pi/2
    # ========================================================================
    print("TEST 3: Critical Point")
    print("-" * 80)

    # Check g'(pi/2) = 0 numerically
    def g_derivative(x, h=1e-8):
        """Numerical derivative of g"""
        return (g(x + h) - g(x - h)) / (2 * h)

    g_prime_pi2 = g_derivative(np.pi / 2)
    print(f"g'(pi/2) = {g_prime_pi2:.2e} (should be ~0)")

    # Verify the equation cot(x) = (pi - 2x) / (x(pi - x)) at x = pi/2
    x_critical = np.pi / 2
    lhs = 1 / np.tan(x_critical)  # cot(pi/2) = 0
    rhs = (np.pi - 2 * x_critical) / (x_critical * (np.pi - x_critical))
    print(f"At x = pi/2:")
    print(f"  cot(pi/2) = {lhs:.2e}")
    print(f"  (pi - 2x)/(x(pi-x)) = {rhs:.2e}")
    print(f"  Difference = {abs(lhs - rhs):.2e}")

    critical_test_pass = abs(g_prime_pi2) < 1e-6
    print(f"{'PASS' if critical_test_pass else 'FAIL'}: x = pi/2 is a critical point")
    print()

    # ========================================================================
    # TEST 4: Verify value at critical point
    # ========================================================================
    print("TEST 4: Value at Critical Point")
    print("-" * 80)

    g_pi2 = g(np.pi / 2)
    expected_g_pi2 = 4 / (np.pi ** 2)

    print(f"g(pi/2) = {g_pi2:.10f}")
    print(f"Expected 4/pi^2 = {expected_g_pi2:.10f}")
    print(f"Error = {abs(g_pi2 - expected_g_pi2):.2e}")

    value_test_pass = abs(g_pi2 - expected_g_pi2) < 1e-14
    print(f"{'PASS' if value_test_pass else 'FAIL'}: g(pi/2) = 4/pi^2")
    print()

    # ========================================================================
    # TEST 5: Verify uniqueness of critical point
    # ========================================================================
    print("TEST 5: Uniqueness of Critical Point")
    print("-" * 80)

    # Find all critical points numerically
    x_dense = np.linspace(0.01, np.pi - 0.01, 10000)
    g_prime_dense = np.array([g_derivative(x) for x in x_dense])

    # Find where derivative changes sign
    sign_changes = np.where(np.diff(np.sign(g_prime_dense)))[0]

    print(f"Number of sign changes in g'(x): {len(sign_changes)}")
    if len(sign_changes) > 0:
        print(f"Sign changes occur near x =")
        for idx in sign_changes[:5]:  # Show up to 5
            print(f"  x = {x_dense[idx]:.6f} (pi/2 = {np.pi/2:.6f})")

    uniqueness_test_pass = len(sign_changes) == 1 and abs(x_dense[sign_changes[0]] - np.pi/2) < 0.01
    print(f"{'PASS' if uniqueness_test_pass else 'FAIL'}: Unique critical point at x = pi/2")
    print()

    # ========================================================================
    # TEST 6: Verify second derivative (maximum)
    # ========================================================================
    print("TEST 6: Second Derivative Test")
    print("-" * 80)

    def g_second_derivative(x, h=1e-5):
        """Numerical second derivative of g"""
        return (g(x + h) - 2*g(x) + g(x - h)) / (h ** 2)

    g_double_prime_pi2 = g_second_derivative(np.pi / 2)
    print(f"g''(pi/2) = {g_double_prime_pi2:.6f}")
    print(f"Expected: negative (for maximum)")

    # Theoretical value: g''(pi/2) = 4/pi^2 * (8/pi^2 - 1)
    expected_g_double_prime = (4 / np.pi**2) * (8 / np.pi**2 - 1)
    print(f"Theoretical g''(pi/2) = {expected_g_double_prime:.6f}")
    print(f"Error = {abs(g_double_prime_pi2 - expected_g_double_prime):.2e}")

    second_deriv_test_pass = g_double_prime_pi2 < 0
    print(f"{'PASS' if second_deriv_test_pass else 'FAIL'}: g''(pi/2) < 0 (local maximum)")
    print()

    # ========================================================================
    # TEST 7: Find global minimum and maximum numerically
    # ========================================================================
    print("TEST 7: Global Extrema (Numerical Search)")
    print("-" * 80)

    # Sample g at many points
    x_search = np.linspace(1e-10, np.pi - 1e-10, 100000)
    g_search = g(x_search)

    # Find maximum
    max_idx = np.nanargmax(g_search)
    g_max_numerical = g_search[max_idx]
    x_max_numerical = x_search[max_idx]

    # Find minimum (excluding close to endpoints)
    mask_interior = (x_search > 0.01) & (x_search < np.pi - 0.01)
    g_interior = g_search[mask_interior]
    min_idx = np.nanargmin(g_interior)
    g_min_numerical = g_interior[min_idx]

    print(f"Numerical maximum:")
    print(f"  g_max = {g_max_numerical:.10f} at x = {x_max_numerical:.10f}")
    print(f"  Expected: 4/pi^2 = {4/np.pi**2:.10f} at x = pi/2 = {np.pi/2:.10f}")
    print(f"  Error in value: {abs(g_max_numerical - 4/np.pi**2):.2e}")
    print(f"  Error in position: {abs(x_max_numerical - np.pi/2):.2e}")

    print(f"\nNumerical minimum (in interior):")
    print(f"  g_min (interior) = {g_min_numerical:.10f}")
    print(f"  Note: minimum occurs at endpoints, infimum = 1/pi = {1/np.pi:.10f}")

    extrema_test_pass = (abs(g_max_numerical - 4/np.pi**2) < 1e-8 and
                         abs(x_max_numerical - np.pi/2) < 1e-4)
    print(f"{'PASS' if extrema_test_pass else 'FAIL'}: Maximum found at correct location")
    print()

    # ========================================================================
    # TEST 8: Verify inequalities hold for many sample points
    # ========================================================================
    print("TEST 8: Inequality Verification")
    print("-" * 80)

    # Sample many points
    n_samples = 100000
    x_samples = np.linspace(0, np.pi, n_samples)

    # Compute bounds and sin(x)
    lower_bound = a * x_samples * (np.pi - x_samples)
    upper_bound = b * x_samples * (np.pi - x_samples)
    sin_values = np.sin(x_samples)

    # Check violations (with small tolerance for numerical errors)
    tol = 1e-14
    lower_violations = np.sum(sin_values < lower_bound - tol)
    upper_violations = np.sum(sin_values > upper_bound + tol)

    print(f"Testing {n_samples} points in [0, pi]:")
    print(f"  Lower bound violations: {lower_violations}")
    print(f"  Upper bound violations: {upper_violations}")

    # Check maximum gap
    if n_samples > 0:
        lower_gap = np.min(sin_values - lower_bound)
        upper_gap = np.min(upper_bound - sin_values)
        print(f"  Minimum gap from lower bound: {lower_gap:.10f}")
        print(f"  Minimum gap from upper bound: {upper_gap:.10f}")

    inequality_test_pass = (lower_violations == 0) and (upper_violations == 0)
    print(f"{'PASS' if inequality_test_pass else 'FAIL'}: Inequalities hold for all sample points")
    print()

    # ========================================================================
    # TEST 9: Check tightness of bounds
    # ========================================================================
    print("TEST 9: Tightness of Bounds")
    print("-" * 80)

    # Lower bound should be approached at endpoints
    eps = 1e-6
    g_near_0_tight = g(eps)
    g_near_pi_tight = g(np.pi - eps)

    print(f"Lower bound tightness:")
    print(f"  g({eps:.2e}) = {g_near_0_tight:.10f}")
    print(f"  g({np.pi - eps:.10f}) = {g_near_pi_tight:.10f}")
    print(f"  a = 1/pi = {a:.10f}")
    print(f"  Gap at x={eps:.2e}: {g_near_0_tight - a:.2e}")

    # Upper bound should be attained at pi/2
    print(f"\nUpper bound tightness:")
    print(f"  g(pi/2) = {g_pi2:.10f}")
    print(f"  b = 4/pi^2 = {b:.10f}")
    print(f"  Gap: {abs(g_pi2 - b):.2e}")

    tightness_test_pass = (abs(g_pi2 - b) < 1e-14) and (g_near_0_tight > a)
    print(f"{'PASS' if tightness_test_pass else 'FAIL'}: Bounds are tight")
    print()

    # ========================================================================
    # TEST 10: Verify the derivative equation
    # ========================================================================
    print("TEST 10: Derivative Equation Verification")
    print("-" * 80)

    def F(x):
        """F(x) = cot(x) - (pi - 2x)/(x(pi-x))"""
        if x <= 0 or x >= np.pi:
            return np.nan
        return 1/np.tan(x) - (np.pi - 2*x) / (x * (np.pi - x))

    # Check F(pi/2) = 0
    F_pi2 = F(np.pi / 2)
    print(f"F(pi/2) = {F_pi2:.2e} (should be 0)")

    # Check sign of F on (0, pi/2)
    x_left = np.linspace(0.01, np.pi/2 - 0.01, 20)
    F_left = np.array([F(x) for x in x_left])

    print(f"\nF(x) on (0, pi/2):")
    print(f"  Sample at x=0.1: F(0.1) = {F(0.1):.6f}")
    print(f"  Sample at x=0.5: F(0.5) = {F(0.5):.6f}")
    print(f"  Sample at x=1.0: F(1.0) = {F(1.0):.6f}")

    # Check sign of F on (pi/2, pi)
    x_right = np.linspace(np.pi/2 + 0.01, np.pi - 0.01, 20)
    F_right = np.array([F(x) for x in x_right])

    print(f"\nF(x) on (pi/2, pi):")
    print(f"  Sample at x=2.0: F(2.0) = {F(2.0):.6f}")
    print(f"  Sample at x=2.5: F(2.5) = {F(2.5):.6f}")
    print(f"  Sample at x=3.0: F(3.0) = {F(3.0):.6f}")

    derivative_eq_test_pass = abs(F_pi2) < 1e-10
    print(f"{'PASS' if derivative_eq_test_pass else 'FAIL'}: Derivative equation satisfied at pi/2")
    print()

    # ========================================================================
    # SUMMARY
    # ========================================================================
    print("=" * 80)
    print("VERIFICATION SUMMARY")
    print("=" * 80)

    all_tests = [
        ("Endpoint limits", limit_test_pass),
        ("Symmetry", symmetry_test_pass),
        ("Critical point", critical_test_pass),
        ("Value at critical point", value_test_pass),
        ("Uniqueness of critical point", uniqueness_test_pass),
        ("Second derivative test", second_deriv_test_pass),
        ("Global extrema", extrema_test_pass),
        ("Inequality verification", inequality_test_pass),
        ("Tightness of bounds", tightness_test_pass),
        ("Derivative equation", derivative_eq_test_pass),
    ]

    for test_name, result in all_tests:
        status = "PASS" if result else "FAIL"
        print(f"  [{status}] {test_name}")

    all_pass = all(result for _, result in all_tests)

    print()
    print("=" * 80)
    if all_pass:
        print("OVERALL VERDICT: CORRECT")
        print()
        print("The solution is mathematically sound and numerically verified.")
        print("All claimed values are correct:")
        print(f"  a = 1/pi = {a}")
        print(f"  b = 4/pi^2 = {b}")
    else:
        print("OVERALL VERDICT: NEEDS REVISION")
        print()
        print("Some tests failed. Review the solution for errors.")
    print("=" * 80)

    return all_pass

if __name__ == "__main__":
    success = main()
    exit(0 if success else 1)
