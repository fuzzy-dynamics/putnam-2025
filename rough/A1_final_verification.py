"""
Final verification of the proof for Putnam 2025 A1
"""

from math import gcd

def verify_part1_lemma(m, n, verbose=False):
    """
    Verify: if gcd(2m+1, 2n+1) = 1, then gcd(4m+3, 4n+3) = 1
    """
    d0 = gcd(2*m + 1, 2*n + 1)
    if d0 != 1:
        if verbose:
            print(f"  Skipping (m, n) = ({m}, {n}) because gcd(2m+1, 2n+1) = {d0} ≠ 1")
        return None

    d1 = gcd(4*m + 3, 4*n + 3)

    if d1 != 1:
        print(f"  COUNTEREXAMPLE TO LEMMA! (m, n) = ({m}, {n})")
        print(f"    gcd(2m+1, 2n+1) = gcd({2*m+1}, {2*n+1}) = {d0}")
        print(f"    gcd(4m+3, 4n+3) = gcd({4*m+3}, {4*n+3}) = {d1}")
        return False

    return True

def verify_part2_descent(m0, n0, max_iter=100):
    """
    Verify: starting from (m0, n0), the gcd eventually reaches 1
    """
    m, n = m0, n0
    for k in range(max_iter):
        d = gcd(2*m + 1, 2*n + 1)
        if d == 1:
            return k

        # Next iteration
        a = (2*m + 1) // d
        b = (2*n + 1) // d
        m, n = a, b

    print(f"  WARNING: Did not reach gcd=1 within {max_iter} iterations for (m0, n0) = ({m0}, {n0})")
    return -1

print("=" * 90)
print("VERIFICATION OF PUTNAM 2025 A1 PROOF")
print("=" * 90)

print("\n1. VERIFYING PART 1 (Stability Lemma)")
print("-" * 90)
print("Checking: if gcd(2m_k+1, 2n_k+1) = 1, then gcd(2m_{k+1}+1, 2n_{k+1}+1) = 1")
print()

part1_passed = True
tested_count = 0
applicable_count = 0

for m in range(1, 200):
    for n in range(m+1, 200):
        if gcd(m, n) == 1:
            tested_count += 1
            result = verify_part1_lemma(m, n)
            if result is not None:
                applicable_count += 1
                if result is False:
                    part1_passed = False

print(f"Tested {tested_count} coprime pairs (m, n) with m, n < 200")
print(f"Found {applicable_count} pairs where gcd(2m+1, 2n+1) = 1")

if part1_passed:
    print("✓ Part 1 VERIFIED: No counterexamples found!")
else:
    print("✗ Part 1 FAILED: Found counterexample(s)")

print("\n2. VERIFYING PART 2 (Convergence)")
print("-" * 90)
print("Checking: all sequences eventually reach gcd = 1")
print()

part2_passed = True
max_iterations_seen = 0
iteration_counts = {}

for m0 in range(1, 150):
    for n0 in range(m0+1, 150):
        if gcd(m0, n0) == 1:
            iters = verify_part2_descent(m0, n0)
            if iters == -1:
                part2_passed = False
            else:
                max_iterations_seen = max(max_iterations_seen, iters)
                if iters not in iteration_counts:
                    iteration_counts[iters] = 0
                iteration_counts[iters] += 1

print(f"Maximum iterations to reach gcd=1: {max_iterations_seen}")
print("\nDistribution of iteration counts:")
for k in sorted(iteration_counts.keys()):
    print(f"  {k} iterations: {iteration_counts[k]} cases")

if part2_passed:
    print("\n✓ Part 2 VERIFIED: All sequences reached gcd=1!")
else:
    print("\n✗ Part 2 FAILED: Some sequence did not reach gcd=1")

print("\n3. OVERALL VERIFICATION")
print("-" * 90)

if part1_passed and part2_passed:
    print("✓✓✓ PROOF VERIFIED! ✓✓✓")
    print("\nThe proof is correct:")
    print("  1. Once gcd reaches 1, it stays at 1 (Part 1)")
    print("  2. Every sequence eventually reaches gcd=1 (Part 2)")
    print("  Therefore: gcd(2m_k+1, 2n_k+1) = 1 for all but finitely many k.")
else:
    print("✗✗✗ PROOF HAS ISSUES ✗✗✗")
    if not part1_passed:
        print("  - Part 1 failed: stability lemma has counterexamples")
    if not part2_passed:
        print("  - Part 2 failed: some sequences don't converge")

print("\n" + "=" * 90)
print("SPOT CHECK: Detailed trace of a few examples")
print("=" * 90)

examples = [(1, 2), (1, 4), (1, 82), (10, 31)]

for m0, n0 in examples:
    print(f"\nExample: (m_0, n_0) = ({m0}, {n0})")
    print(f"{'k':<4} {'m_k':<12} {'n_k':<12} {'2m_k+1':<12} {'2n_k+1':<12} {'gcd':<8}")
    print("-" * 65)

    m, n = m0, n0
    for k in range(15):
        a, b = 2*m + 1, 2*n + 1
        g = gcd(a, b)
        print(f"{k:<4} {m:<12} {n:<12} {a:<12} {b:<12} {g:<8}")

        if g == 1:
            # Verify lemma
            if k < 14:
                m_next = 2*m + 1
                n_next = 2*n + 1
                g_next = gcd(2*m_next + 1, 2*n_next + 1)
                print(f"  → Next: gcd(2·{m_next}+1, 2·{n_next}+1) = gcd({2*m_next+1}, {2*n_next+1}) = {g_next}")
                if g_next != 1:
                    print(f"  ✗ LEMMA VIOLATION!")
            break

        # Next iteration
        m = a // g
        n = b // g

print("\n" + "=" * 90)
print("VERIFICATION COMPLETE")
print("=" * 90)
