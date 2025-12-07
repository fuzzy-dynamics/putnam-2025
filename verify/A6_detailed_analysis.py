#!/usr/bin/env python3
"""
Detailed analysis to understand how to prove v_2(s_{k+1} - s_k) = k.

The key insight is to track how d_n evolves as we iterate from 2^k to 2^{k+1}.
"""

def v2(n):
    """2-adic valuation."""
    if n == 0:
        return float('inf')
    count = 0
    while n % 2 == 0:
        count += 1
        n //= 2
    return count

def compute_d_mod(n, modulus):
    """Compute d_n mod modulus."""
    d = 1
    for i in range(n):
        d = (d * (d - 1) + 3) % modulus
    return d

def analyze_doubling_structure():
    """
    Analyze how d_{2n} relates to d_n.

    The key observation: if we iterate the map n times starting from d_0,
    we get d_n. To get d_{2n}, we iterate n more times starting from d_n.
    """
    print("="*80)
    print("Analyzing the doubling structure")
    print("="*80)
    print()

    # Let's track d_n for n = 2^k and see the pattern
    for k in range(1, 6):
        n = 2**k
        mod = 2**(k+4)  # Work modulo a sufficiently large power of 2

        d_n = compute_d_mod(n, mod)
        d_2n = compute_d_mod(2*n, mod)

        # Extract s_k: d_n = 1 + 2^{k+2} s_k
        if (d_n - 1) % (2**(k+2)) == 0:
            s_k = ((d_n - 1) // (2**(k+2))) % (2**(k+2))
        else:
            s_k = "ERROR"

        # Extract s_{k+1}: d_{2n} = 1 + 2^{k+3} s_{k+1}
        if (d_2n - 1) % (2**(k+3)) == 0:
            s_k1 = ((d_2n - 1) // (2**(k+3))) % (2**(k+3))
        else:
            s_k1 = "ERROR"

        print(f"k = {k}:")
        print(f"  n = {n}, 2n = {2*n}")
        print(f"  d_{{{n}}} ≡ {d_n} (mod {mod})")
        print(f"  d_{{{2*n}}} ≡ {d_2n} (mod {mod})")

        if isinstance(s_k, int) and isinstance(s_k1, int):
            print(f"  s_{k} ≡ {s_k} (mod {2**(k+2)})")
            print(f"  s_{{{k+1}}} ≡ {s_k1} (mod {2**(k+3)})")

            # Compare in the smaller modulus
            s_k1_reduced = s_k1 % (2**(k+2))
            diff = (s_k1_reduced - s_k) % (2**(k+2))
            v = v2(diff) if diff != 0 else f">= {k+2}"

            print(f"  s_{{{k+1}}} ≡ {s_k1_reduced} (mod {2**(k+2)})")
            print(f"  s_{{{k+1}}} - s_{k} ≡ {diff} (mod {2**(k+2)})")
            print(f"  v_2(s_{{{k+1}}} - s_{k}) = {v}, expected = {k}")
        print()

def analyze_iteration_from_k_to_k1():
    """
    Analyze what happens when we iterate from index 2^k to 2^{k+1}.

    Key idea: The map d -> d(d-1) + 3 is being applied 2^k times.
    We want to understand how the 2-adic valuation changes.
    """
    print("="*80)
    print("Tracking iteration from 2^k to 2^{k+1}")
    print("="*80)
    print()

    for k in range(1, 5):
        start_idx = 2**k
        end_idx = 2**(k+1)
        num_iterations = end_idx - start_idx

        print(f"k = {k}: iterating from index {start_idx} to {end_idx} ({num_iterations} steps)")

        # Work modulo 2^{k+4}
        mod = 2**(k+4)
        d_start = compute_d_mod(start_idx, mod)

        print(f"  d_{{{start_idx}}} ≡ {d_start} (mod {mod})")
        print(f"  Applying map {num_iterations} times...")

        # Track key intermediate points
        checkpoints = [start_idx, start_idx + 2**(k-1), start_idx + 2*k, end_idx]
        for idx in checkpoints:
            if idx <= end_idx:
                d_val = compute_d_mod(idx, mod)
                v = v2(d_val - 1)
                print(f"    d_{{{idx}}} ≡ {d_val} (mod {mod}), v_2(d-1) = {v}")

        print()

def find_pattern_in_s_differences():
    """
    Try to find an explicit formula or pattern for s_{k+1} - s_k.
    """
    print("="*80)
    print("Pattern in s_{k+1} - s_k")
    print("="*80)
    print()

    s_vals = []
    for k in range(1, 8):
        mod = 2**(k+4)
        idx = 2**k
        d_k = compute_d_mod(idx, mod)
        s_k = ((d_k - 1) // (2**(k+2))) % (2**(k+4))
        s_vals.append((k, s_k))

    print("Values of s_k (in high enough modulus):")
    for k, s_k in s_vals:
        print(f"  s_{k} ≡ {s_k} (mod 2^{{{k+4}}})")
    print()

    print("Differences s_{k+1} - s_k:")
    for i in range(len(s_vals) - 1):
        k, s_k = s_vals[i]
        k1, s_k1 = s_vals[i+1]

        # Compute difference in appropriate modulus
        mod = 2**(k+3)
        diff = (s_k1 - s_k) % mod
        v = v2(diff) if diff != 0 else f">= {v2(mod)}"

        # Factor out 2^k
        if isinstance(v, int) and v >= k:
            quotient = diff // (2**k)
            print(f"  s_{{{k+1}}} - s_{k} ≡ {diff} = 2^{k} * {quotient} (mod {mod})")
            print(f"    v_2(diff) = {v}, quotient is odd: {quotient % 2 == 1}")
        else:
            print(f"  s_{{{k+1}}} - s_{k} ≡ {diff} (mod {mod}), v_2 = {v}")
    print()

def verify_algebraic_structure():
    """
    Try to understand the algebraic structure that forces v_2(s_{k+1} - s_k) = k.

    Key observation: The map d -> d(d-1) + 3 = d^2 - d + 3 has special properties
    when iterated starting from d_{2^k} = 1 + 2^{k+2} s_k.
    """
    print("="*80)
    print("Algebraic structure of the map")
    print("="*80)
    print()

    print("The recurrence is: d_{n+1} = d_n^2 - d_n + 3")
    print()
    print("If d_n = 1 + 2^m * t where t is odd, what is d_{n+1} modulo 2^{m+2}?")
    print()

    for m in range(2, 7):
        print(f"m = {m}:")
        # d = 1 + 2^m * t
        # d^2 = 1 + 2^{m+1} * t + 2^{2m} * t^2
        # d^2 - d = 2^m * t + 2^{m+1} * t + 2^{2m} * t^2 = 2^m * t + 2^{m+1} * t (+ higher)
        #         = 2^m * t (1 + 2)  = 3 * 2^m * t (mod 2^{m+2} if 2m >= m+2, i.e., m >= 2)
        # d^2 - d + 3 = 3 * 2^m * t + 3 = 3(1 + 2^m * t) (mod 2^{m+2})

        print(f"  d_{{{m}}} = 1 + 2^{m} * t, where t is odd")
        print(f"  d_{{{m+1}}} = d^2 - d + 3")
        print(f"           = (1 + 2^{m}*t)^2 - (1 + 2^{m}*t) + 3")
        print(f"           = 1 + 2^{{{m+1}}}*t + 2^{{{2*m}}}*t^2 - 1 - 2^{m}*t + 3")

        if 2*m >= m + 2:
            print(f"  Since 2m = {2*m} >= {m+2} = m+2:")
            print(f"           ≡ 3 + 2^{{{m+1}}}*t - 2^{m}*t (mod 2^{{{m+2}}})")
            print(f"           ≡ 3 + 2^{m}*t (mod 2^{{{m+2}}})")
            print(f"           = 3(1 + 2^{m}*t/3)")
            print(f"  This doesn't directly give us v_2(d_{{{m+1}}} - 1) = m+1")
        print()

if __name__ == "__main__":
    analyze_doubling_structure()
    analyze_iteration_from_k_to_k1()
    find_pattern_in_s_differences()
    verify_algebraic_structure()
