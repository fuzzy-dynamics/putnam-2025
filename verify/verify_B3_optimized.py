#!/usr/bin/env python3
"""
Optimized verification of Putnam 2025 B3 solution.
"""

from math import gcd

def factorize(n):
    """Return prime factorization as dict {p: exponent}."""
    factors = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors

def get_divisors_fast(n):
    """Return all positive divisors of n efficiently."""
    if n == 0:
        return set()
    if n == 1:
        return {1}

    divisors = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            divisors.append(i)
            if i != n // i:
                divisors.append(n // i)
        i += 1
    return set(divisors)

def multiplicative_order(a, p):
    """Find the multiplicative order of a modulo p."""
    if gcd(a, p) != 1:
        return None
    order = 1
    current = a % p
    while current != 1:
        current = (current * a) % p
        order += 1
        if order > p:
            return None
    return order

print("=" * 80)
print("VERIFICATION OF PUTNAM 2025 B3 SOLUTION")
print("=" * 80)
print()

# STEP 1: Verify factorization
print("STEP 1: Verify factorization 2025^n - 15^n = 15^n(135^n - 1)")
print("-" * 80)
print(f"2025 = {factorize(2025)}")
print(f"15 = {factorize(15)}")
print(f"135 = 2025/15 = {2025//15} = {factorize(135)}")

print("\nChecking for small n:")
for n in range(1, 6):
    lhs = 2025**n - 15**n
    rhs = 15**n * (135**n - 1)
    print(f"  n={n}: {lhs == rhs}")

print()

# STEP 2: Initial elements
print("STEP 2: Initial elements from n=1")
print("-" * 80)
val = 2025 - 15
print(f"2025 - 15 = {val} = {factorize(val)}")
divs = get_divisors_fast(val)
print(f"Divisors: {sorted(divs)}")
print(f"Contains 1,2,3,5,67: {all(x in divs for x in [1,2,3,5,67])}")
print()

# STEP 3: Multiplicative orders for small primes
print("STEP 3: Multiplicative order argument for primes")
print("-" * 80)
primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

print(f"{'p':<6} {'ord_p(135)':<12} {'< p?':<8} {'| (p-1)?'}")
print("-" * 50)
for p in primes:
    if gcd(135, p) != 1:
        print(f"{p:<6} {'N/A (gcd>1)':<12}")
        continue

    order = multiplicative_order(135, p)
    ord_less = order < p
    divides = (p - 1) % order == 0
    print(f"{p:<6} {order:<12} {str(ord_less):<8} {divides}")

print("\nKey: ord_p(135) < p for ALL primes, creating downward dependency.")
print()

# STEP 4: Simulate S construction (limited)
print("STEP 4: Simulate S construction (limited to n <= 50)")
print("-" * 80)

S = {1}

# Add divisors of small values
for n in range(1, 11):
    if n in S:
        val = 2025**n - 15**n
        divs = get_divisors_fast(val)
        S.update(d for d in divs if d <= 50)

print(f"After processing n in {{1,...,10}} ∩ S:")
print(f"|S ∩ [1,50]| = {len([x for x in S if x <= 50])}")

all_up_to_50 = set(range(1, 51))
missing = all_up_to_50 - S

if missing:
    print(f"Missing from [1,50]: {sorted(missing)}")
else:
    print("All integers in [1,50] are in S!")

print()

# STEP 5: Check specific problem with composite argument
print("STEP 5: Critical analysis of composite argument")
print("-" * 80)
print()
print("The solution claims:")
print('  "For composite n, we can show n appears as a divisor of 2025^k - 15^k')
print('   for some k in S"')
print()
print("KEY ISSUE: This is VAGUE. Let's check concretely.")
print()

# Check if composite numbers actually appear
print("For each composite n <= 30, can we find k in S such that n | (2025^k - 15^k)?")
print()

# We have S from above; let's check composites
composites = [n for n in range(1, 31) if n not in [2,3,5,7,11,13,17,19,23,29] and n > 1]

print(f"{'n':<6} {'Factorization':<20} {'In S?':<10} {'Found for k='}")
print("-" * 60)

for n in composites[:15]:
    in_S = n in S

    # Try to find k in S (up to 10) such that n divides 2025^k - 15^k
    found_k = None
    for k in [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]:
        if k in S:
            val = pow(2025, k, n) - pow(15, k, n)
            if val % n == 0:
                found_k = k
                break

    factors_str = str(factorize(n))
    print(f"{n:<6} {factors_str:<20} {str(in_S):<10} {found_k if found_k else 'NOT FOUND'}")

print()
print("=" * 80)
print("CRITICAL QUESTION:")
print("=" * 80)
print()
print("The solution's argument for composites (Step 3, Case 2) is NOT RIGOROUS.")
print()
print("It says: 'n appears as a divisor of 2025^k - 15^k for some k in S'")
print("But it doesn't PROVE this claim!")
print()
print("The argument needs to show:")
print("  For ANY composite n, there exists k in S such that n | (2025^k - 15^k)")
print()
print("Without this, the proof is INCOMPLETE.")
print()

# Let's check the LTE argument mentioned
print("The solution mentions 'Lifting the Exponent Lemma' for prime powers.")
print("Let's verify this helps:")
print()

# For prime powers p^a
print("For prime power n = p^a:")
print("  - We have p in S (from prime argument)")
print("  - We need p^a in S")
print("  - By LTE: if p is odd and p | (2025-15), then v_p(2025^p^k - 15^p^k) = v_p(2025-15) + v_p(p) + ... ")
print("  - But LTE applies when base difference is divisible by p")
print()
print("Check: 2025 - 15 = 2010 = 2 * 3 * 5 * 67")
print("So LTE applies for p in {2, 3, 5, 67}")
print()
print("For other primes p, we have 2025 ≡ 15 (mod p) IFF p | 2010.")
print("For p not dividing 2010, LTE doesn't directly apply!")
print()

# Check 135 mod various primes
print("135 mod small primes:")
for p in [7, 11, 13, 17, 19, 23]:
    print(f"  135 mod {p} = {135 % p}")

print()
print("=" * 80)
print("CONCLUSION")
print("=" * 80)
print()
print("FACTORIZATION: ✓ Correct")
print("INITIAL ELEMENTS: ✓ Correct (1,2,3,5,67 in S)")
print("PRIME ARGUMENT: ✓ Sound (ord_p(135) < p creates downward dependency)")
print()
print("COMPOSITE ARGUMENT: ✗ INCOMPLETE")
print()
print("The solution ASSERTS that composites appear but doesn't PROVE it.")
print("The claim 'n appears as a divisor of 2025^k - 15^k for some k in S'")
print("needs rigorous justification, which is missing.")
print()
print("VERDICT: The solution is INCOMPLETE as written.")
print("The answer may still be YES, but the proof needs more work on composites.")
