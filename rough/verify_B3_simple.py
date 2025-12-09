#!/usr/bin/env python3
"""Simple verification of B3 key claims."""

from math import gcd

def factorize(n):
    """Return prime factorization as dict."""
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

def mult_order(a, p):
    """Multiplicative order of a mod p."""
    if gcd(a, p) != 1:
        return None
    order, current = 1, a % p
    while current != 1:
        current = (current * a) % p
        order += 1
        if order > p:
            return None
    return order

# Test 1: Factorization
print("Test 1: Factorization")
print(f"2025 = {factorize(2025)}")
print(f"15 = {factorize(15)}")
print(f"135 = {factorize(135)}")
for n in [1, 2, 3]:
    lhs = 2025**n - 15**n
    rhs = 15**n * (135**n - 1)
    print(f"n={n}: match = {lhs == rhs}")

# Test 2: Initial elements
print("\nTest 2: Initial elements")
val = 2025 - 15
print(f"2025 - 15 = {val} = {factorize(val)}")

# Test 3: Orders
print("\nTest 3: Multiplicative orders")
primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
for p in primes:
    if gcd(135, p) == 1:
        o = mult_order(135, p)
        print(f"p={p:3d}: ord={o:3d}, ord<p: {o<p}, ord|(p-1): {(p-1)%o==0}")

# Test 4: Key issue - do composites appear?
print("\nTest 4: Critical issue - composite coverage")
print("We can prove all primes are in S (downward dependency via ord_p(135) < p)")
print("But for composites, the solution just ASSERTS they appear.")
print("\nThe solution says:")
print("  'n appears as a divisor of 2025^k - 15^k for some k in S'")
print("This is NOT PROVEN in the solution!")
print("\nFor example, take n = 4 = 2^2:")
print("  - We have 2 in S")
print("  - Does 4 divide 2025^k - 15^k for some k in S?")

for k in [1, 2, 3, 4, 5]:
    val = pow(2025, k, 4) - pow(15, k, 4)
    divides = (val % 4 == 0)
    print(f"    k={k}: 4 | (2025^{k} - 15^{k})? {divides}")

print("\nNote: 2025 ≡ 1 (mod 4), 15 ≡ 3 (mod 4)")
print("So 2025^k - 15^k ≡ 1 - 3^k (mod 4)")
print("For k=1: 1-3 = -2 ≡ 2 (mod 4), not divisible by 4")
print("For k=2: 1-9 = -8 ≡ 0 (mod 4), divisible!")
print("\nSo 4 divides 2025^2 - 15^2.")
print("But do we have 2 in S to use this?")
print("Yes! We get 2 from n=1.")
print("\nSo the argument WORKS for 4, but it's not spelled out clearly.")

print("\n" + "="*80)
print("CRITICAL ANALYSIS")
print("="*80)
print("\nThe solution's composite argument is HAND-WAVY.")
print("It needs to prove: for any composite n, there exists k in S with n | (2025^k - 15^k)")
print("\nA RIGOROUS argument would:")
print("1. Use strong induction: assume {1,...,n-1} ⊆ S")
print("2. For composite n, write n = product of smaller numbers")
print("3. Show that having all smaller numbers in S implies n in S")
print("\nThe current solution sketches this but lacks rigor.")
print("\nVERDICT: INCOMPLETE - needs better composite argument")
