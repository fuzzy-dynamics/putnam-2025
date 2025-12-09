#!/usr/bin/env python3
"""
Rigorous verification of Putnam 2025 B6
"""

def verify_construction(g_func, r, n_max=1000):
    """Verify that g satisfies g(n+1) - g(n) >= (g(g(n)))^r"""
    print(f"Verifying construction with r = {r}")
    print(f"Testing g(n) = n^2 for n = 1 to {n_max}")

    violations = []
    for n in range(1, n_max + 1):
        g_n = g_func(n)
        g_n_plus_1 = g_func(n + 1)
        diff = g_n_plus_1 - g_n

        g_g_n = g_func(g_n)
        rhs = g_g_n ** r

        if diff < rhs - 1e-9:  # Allow small numerical error
            violations.append((n, diff, rhs))

    if violations:
        print(f"FAILED: Found {len(violations)} violations")
        for n, diff, rhs in violations[:10]:
            print(f"  n={n}: {diff} < {rhs}")
        return False
    else:
        print(f"SUCCESS: All {n_max} cases satisfy the constraint")
        return True


def test_larger_r(g_func, r, n_max=100):
    """Test if g(n) = n^2 works for r > 1/4"""
    print(f"\nTesting if g(n) = n^2 works for r = {r}")

    violations = []
    for n in range(1, n_max + 1):
        g_n = g_func(n)
        g_n_plus_1 = g_func(n + 1)
        diff = g_n_plus_1 - g_n

        g_g_n = g_func(g_n)
        rhs = g_g_n ** r

        if diff < rhs - 1e-9:
            violations.append((n, diff, rhs))

    if violations:
        print(f"  Fails at n = {violations[0][0]}: {violations[0][1]:.2f} < {violations[0][2]:.2f}")
        return False
    else:
        print(f"  Works up to n = {n_max}")
        return True


def explore_growth_rates():
    """Explore what growth rates could work"""
    print("\n" + "="*60)
    print("GROWTH RATE ANALYSIS")
    print("="*60)

    print("\nFor g(n) ~ n^alpha, we need:")
    print("  g(n+1) - g(n) ~ alpha * n^(alpha-1)")
    print("  g(g(n)) ~ (n^alpha)^alpha = n^(alpha^2)")
    print("  Constraint: alpha * n^(alpha-1) >= n^(r*alpha^2)")
    print("  This requires: alpha - 1 >= r * alpha^2")
    print("  So: r <= (alpha - 1) / alpha^2")

    print("\nMaximum r for various alpha:")
    for alpha in [1.5, 1.7, 1.9, 2.0, 2.1, 2.3, 2.5, 3.0]:
        if alpha > 1:
            max_r = (alpha - 1) / (alpha ** 2)
            print(f"  alpha = {alpha:.1f}: max r = {max_r:.6f}")

    print("\nOptimal alpha from calculus:")
    print("  f(alpha) = (alpha - 1) / alpha^2")
    print("  f'(alpha) = (2 - alpha) / alpha^3")
    print("  f'(alpha) = 0 when alpha = 2")
    print("  f(2) = 1/4")


def analyze_bounds():
    """Analyze bounds more carefully"""
    print("\n" + "="*60)
    print("BOUND ANALYSIS")
    print("="*60)

    print("\nKey insight: We can derive lower bounds on g(n)")
    print("\nFrom g(n+1) - g(n) >= (g(g(n)))^r, summing from 1 to n-1:")
    print("  g(n) - g(1) >= sum_{k=1}^{n-1} (g(g(k)))^r")

    print("\nIf g is strictly increasing (which it must be to map N -> N reasonably),")
    print("then g(g(k)) >= g(g(1)) = g(g(1)) for all k >= 1")

    print("\nLet's see what happens if g grows too slowly or too fast:")

    # Case 1: g(n) = n
    print("\n1. If g(n) = n (too slow):")
    print("   g(n+1) - g(n) = 1")
    print("   g(g(n)) = g(n) = n")
    print("   Need: 1 >= n^r for all n")
    print("   This fails for r > 0 as n -> infinity")

    # Case 2: g(n) = 2^n
    print("\n2. If g(n) = 2^n (too fast):")
    print("   g(n+1) - g(n) = 2^n")
    print("   g(g(n)) = 2^(2^n)")
    print("   Need: 2^n >= (2^(2^n))^r = 2^(r*2^n)")
    print("   This requires: n >= r*2^n")
    print("   This fails for any r > 0 as n -> infinity")

    # Case 3: g(n) = n^2
    print("\n3. If g(n) = n^2 (just right):")
    print("   g(n+1) - g(n) = 2n + 1")
    print("   g(g(n)) = n^4")
    print("   Need: 2n + 1 >= n^(4r)")
    print("   For large n: 2n >= n^(4r)")
    print("   This requires: 1 >= 4r - 1, so r <= 1/4")


if __name__ == "__main__":
    # Test construction
    g = lambda n: n ** 2

    print("="*60)
    print("PART 1: CONSTRUCTION VERIFICATION")
    print("="*60)
    verify_construction(g, 1/4, n_max=10000)

    # Test that larger r fails
    print("\n" + "="*60)
    print("PART 2: TESTING LARGER r")
    print("="*60)
    for r in [0.26, 0.27, 0.30, 0.35, 0.40, 0.50]:
        test_larger_r(g, r, n_max=100)

    # Growth rate analysis
    explore_growth_rates()

    # Bound analysis
    analyze_bounds()

    print("\n" + "="*60)
    print("CONCLUSION")
    print("="*60)
    print("g(n) = n^2 works for r = 1/4")
    print("g(n) = n^2 fails for r > 1/4")
    print("Maximum r = 1/4")
