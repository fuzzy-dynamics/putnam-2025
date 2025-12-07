"""
Numerical experiments for Putnam 2025 A1
"""

from math import gcd
from fractions import Fraction

def compute_sequence(m0, n0, num_iterations=20):
    """
    Compute the sequence (m_k, n_k) and track gcd(2m_k+1, 2n_k+1)
    """
    print(f"\n=== Starting with m_0 = {m0}, n_0 = {n0} ===")
    print(f"{'k':<4} {'m_k':<10} {'n_k':<10} {'m_k/n_k':<20} {'gcd(m_k,n_k)':<15} {'gcd(2m_k+1,2n_k+1)':<20}")
    print("-" * 90)

    m, n = m0, n0
    gcd_history = []

    for k in range(num_iterations):
        g_mn = gcd(m, n)
        g_odd = gcd(2*m + 1, 2*n + 1)
        ratio = Fraction(m, n)

        print(f"{k:<4} {m:<10} {n:<10} {str(ratio):<20} {g_mn:<15} {g_odd:<20}")
        gcd_history.append(g_odd)

        # Compute next iteration
        m_next = 2*m + 1
        n_next = 2*n + 1
        g = gcd(m_next, n_next)
        m = m_next // g
        n = n_next // g

    # Find when gcd stabilizes to 1
    stable_index = None
    for i in range(len(gcd_history)):
        if all(gcd_history[j] == 1 for j in range(i, len(gcd_history))):
            stable_index = i
            break

    print(f"\ngcd(2m_k+1, 2n_k+1) history: {gcd_history[:15]}")
    if stable_index is not None:
        print(f"gcd stabilizes to 1 starting at k = {stable_index}")
    else:
        print("gcd has not stabilized to 1 in the range explored")

    return gcd_history

# Test cases
print("=" * 90)
print("NUMERICAL EXPLORATION OF PUTNAM 2025 A1")
print("=" * 90)

# Test case 1: m_0 = 1, n_0 = 2
compute_sequence(1, 2, 25)

# Test case 2: m_0 = 2, n_0 = 3
compute_sequence(2, 3, 25)

# Test case 3: m_0 = 3, n_0 = 5
compute_sequence(3, 5, 25)

# Test case 4: m_0 = 1, n_0 = 3
compute_sequence(1, 3, 25)

# Test case 5: m_0 = 5, n_0 = 7
compute_sequence(5, 7, 25)

# Test case 6: m_0 = 1, n_0 = 4
compute_sequence(1, 4, 25)

print("\n" + "=" * 90)
print("ANALYSIS")
print("=" * 90)
print("\nKey observations to look for:")
print("1. Does gcd(2m_k+1, 2n_k+1) eventually become 1?")
print("2. If so, how many steps does it take?")
print("3. What is the pattern in the gcd values before stabilization?")
