#!/usr/bin/env python3
"""
Analyze the commutation condition for Weyl matrices.

For A_i = X^a Z^b and A_j = X^c Z^d where i = ak + b, j = ck + d:
- They commute iff bc ≡ ad (mod k)

For cycle C_n with n = k^2:
- i and j are adjacent iff |i-j| = 1 or |i-j| = n-1
"""

def index_to_coords(i, k):
    """Convert linear index to (a, b) coordinates."""
    return i // k, i % k

def coords_to_index(a, b, k):
    """Convert (a, b) coordinates to linear index."""
    return a * k + b

def is_adjacent_cycle(i, j, n):
    """Check if i and j are adjacent in cycle C_n."""
    diff = abs(i - j)
    return diff == 1 or diff == n - 1

def weyl_commute_condition(i, j, k):
    """Check if A_i and A_j commute using Weyl condition."""
    a, b = index_to_coords(i, k)
    c, d = index_to_coords(j, k)
    return (b * c) % k == (a * d) % k

def analyze_pattern(n, k):
    """Analyze if Weyl pattern matches cycle pattern."""
    print(f"\nAnalyzing n={n}, k={k}")
    print(f"  n = k^2? {n == k*k}")

    mismatches = []

    for i in range(n):
        for j in range(i + 1, n):
            cycle_adjacent = is_adjacent_cycle(i, j, n)
            weyl_commute = weyl_commute_condition(i, j, k)

            if cycle_adjacent != weyl_commute:
                a, b = index_to_coords(i, k)
                c, d = index_to_coords(j, k)
                mismatches.append({
                    'i': i, 'j': j,
                    'a': a, 'b': b, 'c': c, 'd': d,
                    'cycle': cycle_adjacent,
                    'weyl': weyl_commute,
                    'bc_mod': (b*c) % k,
                    'ad_mod': (a*d) % k
                })

    if mismatches:
        print(f"  MISMATCH: {len(mismatches)} pairs don't match!")
        print(f"\n  First 10 mismatches:")
        for m in mismatches[:10]:
            print(f"    ({m['i']:3d}, {m['j']:3d}): "
                  f"coords=({m['a']},{m['b']}), ({m['c']},{m['d']}), "
                  f"cycle={m['cycle']}, weyl={m['weyl']}, "
                  f"bc%k={m['bc_mod']}, ad%k={m['ad_mod']}")
    else:
        print(f"  SUCCESS: All {n*(n-1)//2} pairs match!")

    return len(mismatches) == 0

# Test small cases
print("="*70)
print("WEYL VS CYCLE COMMUTATION PATTERN ANALYSIS")
print("="*70)

results = []
for k in range(2, 16):
    n = k * k
    success = analyze_pattern(n, k)
    results.append((n, k, success))

# Summary
print("\n" + "="*70)
print("SUMMARY")
print("="*70)
print(f"{'n':>6} | {'k':>6} | {'Match':>8}")
print("-" * 70)
for n, k, success in results:
    print(f"{n:6d} | {k:6d} | {'YES' if success else 'NO':>8}")

# Test n=2025, k=45
print("\n" + "="*70)
print("CHECKING n=2025, k=45")
print("="*70)
success_2025 = analyze_pattern(2025, 45)
print(f"\nResult: {'SUCCESS - k=45 works!' if success_2025 else 'FAILED - k=45 does not work'}")

# If it fails, what about other factorizations?
if not success_2025:
    print("\n" + "="*70)
    print("Testing other factorizations of 2025 = 3^4 × 5^2 = 81 × 25")
    print("="*70)

    # 2025 = 81 * 25, so we could try different grid sizes
    test_cases = [
        (2025, 81),  # 81 x 25 grid
        (2025, 75),  # 75 x 27 grid
        (2025, 50),
        (2025, 60),
    ]

    for n, k in test_cases:
        if n % k == 0 or k * k == n:
            print(f"\nTrying k={k}...")
            success = analyze_pattern(n, k)
