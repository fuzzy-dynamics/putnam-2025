#!/usr/bin/env python3
"""
Attempt to construct a rigorous proof that composites are in S.

Key idea: For composite n, use Chinese Remainder Theorem.
n | (2025^k - 15^k) IFF 135^k ≡ 1 (mod n)
We need to find k in S such that 135^k ≡ 1 (mod n).
"""

from math import gcd, lcm

def mult_order(a, n):
    """Multiplicative order of a mod n (if gcd(a,n)=1)."""
    if gcd(a, n) != 1:
        return None
    order, current = 1, a % n
    while current != 1:
        current = (current * a) % n
        order += 1
        if order > n:
            return None
    return order

def factorize(n):
    """Prime factorization."""
    factors = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        factors[n] = 1
    return factors

print("="*80)
print("RIGOROUS PROOF ATTEMPT: All composites are in S")
print("="*80)
print()

print("Recall: 135 = 3^3 * 5")
print("For n coprime to 135:")
print("  n | (2025^k - 15^k) = 15^k(135^k - 1)  IFF  n | (135^k - 1)")
print("                                         IFF  135^k ≡ 1 (mod n)")
print("                                         IFF  ord_n(135) | k")
print()

print("KEY THEOREM (to prove):")
print("  For any composite n, there exists k in S with ord_n(135) | k")
print()

print("-"*80)
print("APPROACH: Use Chinese Remainder Theorem")
print("-"*80)
print()

print("For n = p1^{a1} * ... * pr^{ar}, we have:")
print("  ord_n(135) = lcm(ord_{p1^{a1}}(135), ..., ord_{pr^{ar}}(135))")
print()
print("So we need to understand ord_{p^a}(135) for prime powers p^a.")
print()

print("LEMMA: For prime p not dividing 135:")
print("  ord_{p^a}(135) divides p^{a-1} * ord_p(135)")
print()
print("Moreover, by standard theory:")
print("  ord_{p^a}(135) = p^{v} * ord_p(135)")
print("  where v is some integer with 0 ≤ v ≤ a-1")
print()

print("Since ord_p(135) < p (we proved this!), we have:")
print("  ord_{p^a}(135) ≤ p^{a-1} * ord_p(135) < p^{a-1} * p = p^a")
print()
print("So ord_{p^a}(135) < p^a = n (when n = p^a)")
print()

print("For general composite n = p1^{a1} * ... * pr^{ar}:")
print("  ord_n(135) = lcm of terms, each < corresponding prime power")
print()
print("But this doesn't immediately give us ord_n(135) < n!")
print()

print("-"*80)
print("CHECKING: Is ord_n(135) < n for small composites?")
print("-"*80)
print()

composites = [4, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 22, 24, 25, 26, 27, 28]

for n in composites:
    if gcd(n, 135) != 1:
        print(f"n={n:3d}: gcd(n,135) > 1, special case")
        continue

    order = mult_order(135, n)
    if order:
        less_than_n = order < n
        print(f"n={n:3d}: ord_n(135) = {order:4d}, < n? {less_than_n}")

print()
print("OBSERVATION: ord_n(135) < n for all tested composites!")
print()

print("-"*80)
print("CASE 1: n coprime to 135")
print("-"*80)
print()
print("If gcd(n, 135) = 1 and ord_n(135) < n, then by strong induction:")
print("  - Assume {1, 2, ..., n-1} ⊆ S")
print("  - Then ord_n(135) ∈ S (since ord_n(135) < n)")
print("  - Therefore n | (135^{ord_n(135)} - 1) | (2025^{ord_n(135)} - 15^{ord_n(135)})")
print("  - So n ∈ S")
print()

print("-"*80)
print("CASE 2: n NOT coprime to 135 (i.e., 3|n or 5|n)")
print("-"*80)
print()
print("Write n = 3^a * 5^b * m where gcd(m, 15) = 1")
print()
print("We have: 2025^k - 15^k = 3^k * 5^k * (3^{3k} * 5^k - 1)")
print()
print("For 3^a | (2025^k - 15^k), we need:")
print("  v_3(2025^k - 15^k) ≥ a")
print()
print("We showed earlier: v_3(2025^k - 15^k) = k + v_3(135^k - 1)")
print()
print("Wait, let me recalculate v_3(2025^k - 15^k) more carefully:")
print()

# Calculate v_3 for small k
print("v_3(2025^k - 15^k) for small k:")
for k in range(1, 11):
    val = 2025**k - 15**k
    v3 = 0
    temp = val
    while temp % 3 == 0:
        v3 += 1
        temp //= 3
    print(f"  k={k:2d}: v_3 = {v3:2d}")

print()
print("Pattern: v_3(2025^k - 15^k) = k")
print("This is because 2025^k - 15^k = 3^k * 5^k * (135^k - 1)")
print("and 135 = 3^3 * 5, so 135^k - 1 ≡ -1 (mod 3), giving v_3(135^k - 1) = 0")
print()
print("Similarly, let's check v_5:")

print("\nv_5(2025^k - 15^k) for small k:")
for k in range(1, 11):
    val = 2025**k - 15**k
    v5 = 0
    temp = val
    while temp % 5 == 0:
        v5 += 1
        temp //= 5
    print(f"  k={k:2d}: v_5 = {v5:2d}")

print()
print("Pattern: v_5(2025^k - 15^k) = k")
print()

print("CONCLUSION for Case 2:")
print("  For n = 3^a * 5^b * m (gcd(m,15)=1):")
print("  - We need v_3 ≥ a, so we need k ≥ a")
print("  - We need v_5 ≥ b, so we need k ≥ b")
print("  - We need m | (135^k - 1), so we need ord_m(135) | k")
print()
print("  By strong induction, if {1,...,n-1} ⊆ S, then:")
print("  - a < n, so a ∈ S")
print("  - b < n, so b ∈ S")
print("  - ord_m(135) < m ≤ n (if m > 1), so ord_m(135) ∈ S")
print()
print("  Taking k = lcm(a, b, ord_m(135)) < n (if we can show this!):")
print("  - k ∈ S by induction")
print("  - n | (2025^k - 15^k)")
print("  - So n ∈ S")
print()

print("="*80)
print("REMAINING ISSUE")
print("="*80)
print()
print("We need: lcm(a, b, ord_m(135)) < n = 3^a * 5^b * m")
print()
print("This is NOT always true! For example:")
print("  If n = 6 = 2 * 3, then a=1, b=0, m=2")
print("  ord_2(135) =", mult_order(135, 2))
print("  lcm(1, 1) = 1 < 6 ✓")
print()
print("  If n = 30 = 2 * 3 * 5, then a=1, b=1, m=2")
print("  ord_2(135) =", mult_order(135, 2))
print("  lcm(1, 1, 1) = 1 < 30 ✓")
print()

# More examples
print("More examples:")
for n in [12, 18, 20, 24, 36]:
    facts = factorize(n)
    a = facts.get(3, 0)
    b = facts.get(5, 0)
    m = n // (3**a * 5**b)
    if m == 1:
        ord_m = 1
    else:
        ord_m = mult_order(135, m) if gcd(135, m) == 1 else None

    if ord_m:
        L = lcm(a if a > 0 else 1, b if b > 0 else 1, ord_m)
        print(f"  n={n:3d} = 3^{a} * 5^{b} * {m}: lcm = {L:3d}, < n? {L < n}")

print()
print("="*80)
print("FINAL VERDICT")
print("="*80)
print()
print("The solution's composite argument CAN be made rigorous, but requires:")
print()
print("1. Proving ord_n(135) < n for all n coprime to 135")
print("2. Careful analysis of n with factors of 3 or 5")
print("3. Showing lcm bounds work out")
print()
print("The current solution SKETCHES this but lacks full rigor.")
print("It's INCOMPLETE but likely CORRECT in spirit.")
