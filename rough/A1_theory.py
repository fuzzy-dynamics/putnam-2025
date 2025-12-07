"""
Theoretical analysis of the gcd behavior

Key observation from experiments:
- When gcd(2m_k+1, 2n_k+1) > 1, after one iteration we always get (m_{k+1}, n_{k+1}) = (1, 3)
- This suggests there's a strong algebraic relationship

Let's investigate:
If d = gcd(2m_k+1, 2n_k+1) > 1, then:
  2m_k+1 ≡ 0 (mod d)
  2n_k+1 ≡ 0 (mod d)

This means 2m_k ≡ -1 (mod d) and 2n_k ≡ -1 (mod d)
So 2m_k ≡ 2n_k (mod d), which means 2(m_k - n_k) ≡ 0 (mod d)

Since d is odd (d divides odd numbers), we have m_k ≡ n_k (mod d)
"""

from math import gcd

def analyze_congruence(m, n):
    """
    Analyze the relationship when gcd(2m+1, 2n+1) > 1
    """
    d = gcd(2*m + 1, 2*n + 1)
    if d == 1:
        print(f"m={m}, n={n}: gcd(2m+1, 2n+1) = 1")
        return

    print(f"\nm={m}, n={n}: gcd({2*m+1}, {2*n+1}) = {d}")
    print(f"  2m+1 = {2*m+1} = {d} * {(2*m+1)//d}")
    print(f"  2n+1 = {2*n+1} = {d} * {(2*n+1)//d}")
    print(f"  m ≡ {m % d} (mod {d})")
    print(f"  n ≡ {n % d} (mod {d})")
    print(f"  n - m = {n - m}")

    # Check what happens after reduction
    a, b = 2*m + 1, 2*n + 1
    g = gcd(a, b)
    m_next = a // g
    n_next = b // g

    print(f"  After reduction: m_1 = {m_next}, n_1 = {n_next}")
    print(f"  gcd(2m_1+1, 2n_1+1) = gcd({2*m_next+1}, {2*n_next+1}) = {gcd(2*m_next+1, 2*n_next+1)}")

print("=" * 80)
print("CONGRUENCE ANALYSIS")
print("=" * 80)

# Test cases with gcd > 1
test_cases = [
    (1, 4),   # gcd = 3
    (2, 7),   # gcd = 5
    (3, 10),  # gcd = 7
    (4, 13),  # gcd = 9
    (5, 16),  # gcd = 11
    (6, 19),  # gcd = 13
    (10, 31), # gcd = 21
]

for m, n in test_cases:
    analyze_congruence(m, n)

print("\n" + "=" * 80)
print("PATTERN DISCOVERY")
print("=" * 80)

# Look for the relationship
print("\nLooking for pattern in (m_0, n_0) pairs where gcd(2m_0+1, 2n_0+1) > 1:")
print(f"{'m_0':<6} {'n_0':<6} {'n_0-m_0':<10} {'gcd':<6} {'(2m+1)/gcd':<12} {'(2n+1)/gcd':<12} {'Pattern'}")
print("-" * 80)

for m in range(1, 20):
    for n in range(m+1, 40):
        d = gcd(2*m + 1, 2*n + 1)
        if d > 1:
            a = (2*m + 1) // d
            b = (2*n + 1) // d
            pattern = f"({a}, {b})"
            print(f"{m:<6} {n:<6} {n-m:<10} {d:<6} {a:<12} {b:<12} {pattern}")
            if n - m > 30:
                break

print("\n" + "=" * 80)
print("KEY INSIGHT")
print("=" * 80)

print("\nWhen gcd(2m_0+1, 2n_0+1) = d > 1:")
print("We can write 2m_0+1 = d*a and 2n_0+1 = d*b where gcd(a,b) = 1")
print("Then m_1 = a and n_1 = b")
print("\nIn ALL cases above, we get (a, b) = (1, 3) after one step!")
print("This means n_0 = (3d - 1)/2 and m_0 = (d - 1)/2")
print("\nVerifying this pattern:")

for d in [3, 5, 7, 9, 11, 13, 15, 17, 19, 21]:
    if d % 2 == 1:  # d must be odd
        m = (d - 1) // 2
        n = (3*d - 1) // 2
        actual_gcd = gcd(2*m + 1, 2*n + 1)
        if actual_gcd == d:
            a = (2*m + 1) // d
            b = (2*n + 1) // d
            print(f"  d={d:2}: m_0={m:3}, n_0={n:3} -> 2m_0+1={2*m+1:3}, 2n_0+1={2*n+1:3} -> ({a}, {b})")
        else:
            print(f"  d={d:2}: m_0={m:3}, n_0={n:3} -> gcd={actual_gcd} (NOT {d}!)")

print("\n" + "=" * 80)
print("ALTERNATIVE PATTERNS")
print("=" * 80)

print("\nChecking if there are OTHER patterns besides (1,3):")

seen_patterns = {}
for m in range(1, 100):
    for n in range(m+1, 100):
        d = gcd(2*m + 1, 2*n + 1)
        if d > 1:
            a = (2*m + 1) // d
            b = (2*n + 1) // d
            pattern = (a, b)
            if pattern not in seen_patterns:
                seen_patterns[pattern] = []
            seen_patterns[pattern].append((m, n, d))

print(f"\nFound {len(seen_patterns)} distinct patterns (a,b):")
for pattern, examples in sorted(seen_patterns.items()):
    print(f"  {pattern}: {len(examples)} examples")
    if len(examples) <= 5:
        for m, n, d in examples[:5]:
            print(f"    m={m}, n={n}, d={d}")
