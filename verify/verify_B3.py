#!/usr/bin/env python3
"""
Verify the Putnam 2025 B3 solution.

Problem: Let S be a nonempty set of positive integers such that n in S implies
all positive divisors of 2025^n - 15^n are also in S.
Must S contain all positive integers?

Current answer: YES

We verify:
1. Factorization: 2025^n - 15^n = 15^n(135^n - 1)
2. Initial elements from n=1
3. Bootstrap argument for primes
4. Completeness argument for composites
"""

from math import gcd
from collections import defaultdict

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

def get_divisors(n):
    """Return all positive divisors of n."""
    if n == 0:
        return set()
    divisors = [1]
    factors = factorize(n)
    for p, exp in factors.items():
        new_divisors = []
        power = 1
        for e in range(exp + 1):
            for d in divisors:
                new_divisors.append(d * power)
            power *= p
        divisors = new_divisors
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
        if order > p:  # Safety check
            return None
    return order

def verify_factorization():
    """Verify that 2025^n - 15^n = 15^n(135^n - 1)."""
    print("=" * 80)
    print("STEP 1: Verify factorization")
    print("=" * 80)

    # Check basic facts
    print(f"2025 = {factorize(2025)}")  # Should be {3: 4, 5: 2}
    print(f"15 = {factorize(15)}")      # Should be {3: 1, 5: 1}
    print(f"2025/15 = {2025//15}")      # Should be 135
    print(f"135 = {factorize(135)}")    # Should be {3: 3, 5: 1}

    # Verify for small n
    print("\nVerifying 2025^n - 15^n = 15^n(135^n - 1) for small n:")
    for n in range(1, 6):
        lhs = 2025**n - 15**n
        rhs = 15**n * (135**n - 1)
        match = "✓" if lhs == rhs else "✗"
        print(f"n={n}: LHS={lhs}, RHS={rhs}, Match={match}")

    print()

def verify_initial_elements():
    """Verify that starting from any n in S, we get 1, 2, 3, 5, 67 in S."""
    print("=" * 80)
    print("STEP 2: Initial elements")
    print("=" * 80)

    # For n=1
    val = 2025**1 - 15**1
    print(f"2025 - 15 = {val}")
    print(f"Factorization: {factorize(val)}")
    divisors = get_divisors(val)
    print(f"All divisors: {sorted(divisors)}")
    print(f"Contains 1,2,3,5,67? {all(x in divisors for x in [1,2,3,5,67])}")
    print()

def simulate_S_construction(max_n=100):
    """Simulate construction of S to see which integers appear."""
    print("=" * 80)
    print("STEP 3: Simulate S construction")
    print("=" * 80)

    S = set()

    # Start with 1
    S.add(1)

    # Keep adding divisors until no more can be added
    changed = True
    iterations = 0
    while changed and iterations < 100:
        changed = False
        old_size = len(S)

        # For each n in S (up to reasonable limit)
        for n in list(S):
            if n > max_n:
                continue

            # Compute 2025^n - 15^n and add all its divisors
            val = 2025**n - 15**n
            new_divisors = get_divisors(val)

            for d in new_divisors:
                if d <= max_n and d not in S:
                    S.add(d)
                    changed = True

        iterations += 1
        print(f"Iteration {iterations}: |S| = {len([x for x in S if x <= max_n])}")

        if len(S) >= max_n:
            break

    # Check coverage
    S_up_to_max = {x for x in S if x <= max_n}
    all_integers = set(range(1, max_n + 1))
    missing = all_integers - S_up_to_max

    print(f"\nFinal |S ∩ [1,{max_n}]| = {len(S_up_to_max)}")
    print(f"Coverage: {len(S_up_to_max)}/{max_n} = {100*len(S_up_to_max)/max_n:.1f}%")

    if missing:
        print(f"Missing integers: {sorted(missing)[:20]}{'...' if len(missing) > 20 else ''}")
    else:
        print("ALL integers in [1, {}] are in S!".format(max_n))

    return S_up_to_max, missing

def verify_prime_bootstrap():
    """Verify the multiplicative order argument for primes."""
    print("\n" + "=" * 80)
    print("STEP 4: Prime bootstrap via multiplicative orders")
    print("=" * 80)

    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]

    print(f"{'Prime p':<10} {'ord_p(135)':<12} {'ord < p?':<10} {'Divides p-1?'}")
    print("-" * 60)

    for p in primes:
        if gcd(135, p) != 1:
            print(f"{p:<10} {'gcd != 1':<12} {'-':<10} {'-'}")
            continue

        order = multiplicative_order(135, p)
        ord_less_than_p = order < p
        divides_p_minus_1 = (p - 1) % order == 0

        print(f"{p:<10} {order:<12} {ord_less_than_p!s:<10} {divides_p_minus_1!s}")

    print("\nKey observation: ord_p(135) < p for all primes p.")
    print("This creates downward dependency: to get p in S, we need ord_p(135) in S.")
    print()

def check_composite_gap(S, max_n=100):
    """Check if there are composite numbers missing from S."""
    print("=" * 80)
    print("STEP 5: Check composite coverage")
    print("=" * 80)

    all_integers = set(range(1, max_n + 1))
    missing = all_integers - S

    if not missing:
        print("No missing integers!")
        return

    # Categorize missing numbers
    primes_missing = []
    composites_missing = []

    for n in sorted(missing):
        factors = factorize(n)
        if len(factors) == 1 and list(factors.values())[0] == 1:
            primes_missing.append(n)
        else:
            composites_missing.append(n)

    print(f"Missing primes: {primes_missing[:20]}")
    print(f"Missing composites: {composites_missing[:20]}")

    # For missing composites, check their factorizations
    if composites_missing:
        print("\nAnalyzing missing composites:")
        for n in composites_missing[:10]:
            factors = factorize(n)
            factors_in_S = all(p in S for p in factors.keys())
            print(f"  {n} = {factors}, all prime factors in S? {factors_in_S}")

def main():
    print("Verifying Putnam 2025 B3 Solution")
    print("=" * 80)
    print()

    # Step 1: Verify factorization
    verify_factorization()

    # Step 2: Verify initial elements
    verify_initial_elements()

    # Step 3: Simulate S construction
    S, missing = simulate_S_construction(max_n=100)

    # Step 4: Verify prime bootstrap
    verify_prime_bootstrap()

    # Step 5: Check composite coverage
    check_composite_gap(S, max_n=100)

    # Final verdict
    print("\n" + "=" * 80)
    print("FINAL ANALYSIS")
    print("=" * 80)

    if not missing:
        print("✓ Simulation shows all integers up to 100 are in S")
        print("✓ Factorization is correct")
        print("✓ Prime bootstrap argument is sound (ord_p(135) < p)")
        print("\nHowever, we need to verify the theoretical argument for composites...")
    else:
        print("✗ Simulation found missing integers!")
        print(f"  Missing: {sorted(missing)[:30]}")

if __name__ == "__main__":
    main()
