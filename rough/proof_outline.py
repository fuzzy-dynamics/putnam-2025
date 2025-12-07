#!/usr/bin/env python3
"""
Proof strategy for Putnam 2025 A5.

CLAIM: The sequences s that maximize f(s) are exactly the two alternating sequences:
  s1 = (+, -, +, -, +, ...) of length n-1
  s2 = (-, +, -, +, -, ...) of length n-1

PROOF STRATEGY:

We'll use a "run" argument. Define a run in s as a maximal consecutive block
of identical signs.

Key observations:
1. An alternating sequence has exactly n-1 runs (all of length 1)
2. Any other sequence has fewer than n-1 runs (some runs have length ≥ 2)

We'll show that having more runs (i.e., shorter runs) allows MORE permutations.

The intuition:
- A run of k consecutive +'s means we need k consecutive strict ascents in positions i to i+k
- This is more restrictive than k individual alternating positions
- Similarly for runs of -'s

Let me formalize this with a key lemma about permutation counting.
"""

from itertools import permutations

def verify_key_lemma(n):
    """
    Verify that breaking up runs increases the count.

    Compare:
    - s1 = (+, +) vs s2 = (+, -)  (for n=3)
    - s3 = (-, -) vs s4 = (-, +)  (for n=3)
    """
    print(f"\n{'='*70}")
    print(f"Verifying run-breaking increases count (n={n})")
    print(f"{'='*70}")

    def compute_f(n, s):
        count = 0
        for perm in permutations(range(1, n+1)):
            valid = True
            for i in range(n-1):
                diff = perm[i+1] - perm[i]
                if s[i] * diff <= 0:
                    valid = False
                    break
            if valid:
                count += 1
        return count

    def seq_to_str(s):
        return ','.join(['+' if x == 1 else '-' for x in s])

    # Test various comparisons
    if n == 3:
        comparisons = [
            ((1, 1), (1, -1), "Breaking (+,+) into (+,-)"),
            ((1, 1), (-1, 1), "Changing (+,+) to (-,+)"),
            ((-1, -1), (-1, 1), "Breaking (-,-) into (-,+)"),
            ((-1, -1), (1, -1), "Changing (-,-) to (+,-)"),
        ]

        for s1, s2, desc in comparisons:
            f1 = compute_f(n, s1)
            f2 = compute_f(n, s2)
            print(f"\n{desc}:")
            print(f"  {seq_to_str(s1)}: f(s) = {f1}")
            print(f"  {seq_to_str(s2)}: f(s) = {f2}")
            if f2 > f1:
                print(f"  ✓ Breaking/alternating INCREASES count ({f1} → {f2})")
            elif f2 == f1:
                print(f"  = Counts are EQUAL")
            else:
                print(f"  ✗ Breaking DECREASES count ({f1} → {f2})")

    if n == 4:
        comparisons = [
            ((1, 1, 1), (1, -1, 1), "Breaking middle of (+,+,+)"),
            ((1, 1, -1), (1, -1, 1), "Making (+,+,-) fully alternating"),
            ((-1, -1, -1), (-1, 1, -1), "Breaking middle of (-,-,-)"),
        ]

        for s1, s2, desc in comparisons:
            f1 = compute_f(n, s1)
            f2 = compute_f(n, s2)
            print(f"\n{desc}:")
            print(f"  {seq_to_str(s1)}: f(s) = {f1}")
            print(f"  {seq_to_str(s2)}: f(s) = {f2}")
            if f2 > f1:
                print(f"  ✓ Making more alternating INCREASES count ({f1} → {f2})")
            elif f2 == f1:
                print(f"  = Counts are EQUAL")
            else:
                print(f"  ✗ Making more alternating DECREASES count ({f1} → {f2})")


def main():
    """Run verification."""
    for n in [3, 4, 5]:
        verify_key_lemma(n)

    print(f"\n\n{'='*70}")
    print("PROOF OUTLINE:")
    print(f"{'='*70}")
    print("""
The claim is that alternating sequences maximize f(s).

Strategy: Use an exchange/optimization argument.

Given any sequence s that is not alternating, we can increase f(s) by making
it "more alternating" (breaking up runs of length ≥ 2).

This suggests a greedy/local optimality property: sequences with maximum
number of runs (i.e., all runs of length 1) are optimal.

Since a sequence of length n-1 has at most n-1 runs, and this maximum is
achieved exactly by the two alternating sequences, these must be the maximizers.

However, we need to prove that breaking up runs always increases (or at least
doesn't decrease) the count. This requires a more careful argument...

Alternative approach: Use generating functions or bijective arguments.
The connection to Eulerian numbers suggests there might be a deeper
combinatorial structure we can exploit.
""")

if __name__ == "__main__":
    main()
