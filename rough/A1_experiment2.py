"""
Test cases with larger initial gcd(2m_0+1, 2n_0+1)
"""

from math import gcd

def compute_sequence_detailed(m0, n0, num_iterations=30):
    """
    Compute the sequence and analyze gcd behavior in detail
    """
    print(f"\n=== m_0 = {m0}, n_0 = {n0} ===")
    print(f"Initial gcd(2m_0+1, 2n_0+1) = gcd({2*m0+1}, {2*n0+1}) = {gcd(2*m0+1, 2*n0+1)}")
    print(f"\n{'k':<4} {'m_k':<12} {'n_k':<12} {'2m_k+1':<12} {'2n_k+1':<12} {'gcd(2m_k+1,2n_k+1)':<20}")
    print("-" * 80)

    m, n = m0, n0
    gcd_history = []

    for k in range(num_iterations):
        a, b = 2*m + 1, 2*n + 1
        g_odd = gcd(a, b)

        print(f"{k:<4} {m:<12} {n:<12} {a:<12} {b:<12} {g_odd:<20}")
        gcd_history.append(g_odd)

        # Check if we've stabilized
        if len(gcd_history) >= 3 and all(x == 1 for x in gcd_history[-3:]):
            print(f"\nStabilized to 1 at k = {k-2}")
            break

        # Compute next iteration
        m_next = a
        n_next = b
        g = gcd(m_next, n_next)
        m = m_next // g
        n = n_next // g

    return gcd_history

# Find cases where gcd(2m_0+1, 2n_0+1) > 1
print("=" * 80)
print("TESTING CASES WITH LARGE INITIAL gcd(2m_0+1, 2n_0+1)")
print("=" * 80)

# Look for patterns
test_cases = []

# Find some cases with gcd > 1
for m in range(1, 20):
    for n in range(m+1, 20):
        g = gcd(2*m + 1, 2*n + 1)
        if g > 1:
            test_cases.append((m, n, g))

# Sort by gcd value
test_cases.sort(key=lambda x: x[2], reverse=True)

print(f"\nFound {len(test_cases)} cases with gcd(2m_0+1, 2n_0+1) > 1 for m,n < 20:")
for m, n, g in test_cases[:10]:
    print(f"  m_0={m}, n_0={n}: gcd({2*m+1}, {2*n+1}) = {g}")

# Test a few interesting cases
print("\n" + "=" * 80)
print("DETAILED TRACES")
print("=" * 80)

# Case with gcd = 3
compute_sequence_detailed(1, 4, 15)

# Case with gcd = 5
compute_sequence_detailed(2, 7, 15)

# Case with gcd = 7
compute_sequence_detailed(3, 10, 15)

# Case with gcd = 9
compute_sequence_detailed(4, 13, 15)

# Case with gcd = 11
compute_sequence_detailed(5, 16, 15)

# Case with gcd = 13
compute_sequence_detailed(6, 19, 15)

# Larger case
compute_sequence_detailed(10, 31, 15)

print("\n" + "=" * 80)
print("PATTERN ANALYSIS")
print("=" * 80)

# Analyze the relationship between gcd(2m+1, 2n+1) across iterations
def analyze_gcd_evolution(m0, n0, num_iterations=10):
    """
    Track how gcd evolves and look for patterns
    """
    m, n = m0, n0

    print(f"\nm_0={m0}, n_0={n0}:")
    for k in range(num_iterations):
        a, b = 2*m + 1, 2*n + 1
        g = gcd(a, b)

        # Also check gcd of the reduced fractions
        g_mn = gcd(m, n)

        print(f"  k={k}: gcd({a}, {b}) = {g}, gcd(m_k, n_k) = {g_mn}")

        if g == 1:
            print(f"  -> Reached gcd=1 at k={k}")
            break

        # Next iteration
        m_next = a
        n_next = b
        g_frac = gcd(m_next, n_next)
        m = m_next // g_frac
        n = n_next // g_frac

print("\nGCD Evolution for various starting points:")
analyze_gcd_evolution(1, 4)
analyze_gcd_evolution(2, 7)
analyze_gcd_evolution(4, 13)
analyze_gcd_evolution(10, 31)
