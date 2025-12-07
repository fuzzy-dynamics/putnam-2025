#!/usr/bin/env python3
"""
Verify connection to Eulerian numbers.

Eulerian number A(n,k) = number of permutations of {1,...,n} with exactly k descents.

A descent in a permutation (a_1,...,a_n) is a position i where a_i > a_{i+1}.

For our problem:
- If s has d descents (positions where s_i = -1), then f(s) counts permutations
  with descents exactly at those positions.
- The alternating sequences have the maximum "spread" of descents.
"""

from itertools import permutations, product

def count_descents(perm):
    """Count number of descents in a permutation."""
    descents = 0
    for i in range(len(perm) - 1):
        if perm[i] > perm[i+1]:
            descents += 1
    return descents

def eulerian_number(n, k):
    """Compute A(n,k) = number of permutations of {1,...,n} with exactly k descents."""
    count = 0
    for perm in permutations(range(1, n+1)):
        if count_descents(perm) == k:
            count += 1
    return count

def analyze_eulerian(n):
    """Compute all Eulerian numbers for given n."""
    print(f"\n{'='*60}")
    print(f"Eulerian numbers for n = {n}")
    print(f"{'='*60}")

    print(f"\nA(n,k) for n={n}:")
    print(f"k    A({n},k)")
    print(f"{'-'*20}")

    max_val = 0
    max_k = []

    for k in range(n):
        val = eulerian_number(n, k)
        print(f"{k}    {val}")
        if val > max_val:
            max_val = val
            max_k = [k]
        elif val == max_val:
            max_k.append(k)

    print(f"\nMaximum Eulerian number: A({n},{max_k[0]}) = {max_val}")
    print(f"Achieved at k = {max_k}")

    # Check if maximum is at k = floor((n-1)/2)
    optimal_k = (n - 1) // 2
    print(f"\nfloor((n-1)/2) = {optimal_k}")
    if optimal_k in max_k:
        print(f"✓ Maximum IS achieved at k = floor((n-1)/2)")
    else:
        print(f"✗ Maximum is NOT achieved at k = floor((n-1)/2)")

    return max_val, max_k

def verify_alternating_correspondence(n):
    """
    Verify that alternating sequences correspond to having
    floor((n-1)/2) descents.
    """
    print(f"\n{'='*60}")
    print(f"Alternating sequences for n = {n}")
    print(f"{'='*60}")

    # Generate alternating sequences
    alt1 = tuple([1 if i % 2 == 0 else -1 for i in range(n-1)])
    alt2 = tuple([-1 if i % 2 == 0 else 1 for i in range(n-1)])

    print(f"\nAlternating sequence 1: {','.join(['+' if x == 1 else '-' for x in alt1])}")
    print(f"Alternating sequence 2: {','.join(['+' if x == 1 else '-' for x in alt2])}")

    # Count descents in each
    desc1 = sum(1 for x in alt1 if x == -1)
    desc2 = sum(1 for x in alt2 if x == -1)

    print(f"\nNumber of descents in alt1: {desc1}")
    print(f"Number of descents in alt2: {desc2}")
    print(f"floor((n-1)/2) = {(n-1)//2}")

    if desc1 == (n-1)//2 or desc2 == (n-1)//2:
        print(f"✓ At least one alternating sequence has floor((n-1)/2) descents")
    else:
        print(f"✗ Neither alternating sequence has floor((n-1)/2) descents")

    # But we need to be more careful: the number of descents in the PATTERN s
    # is not the same as descents in permutations satisfying s.
    # Let's think differently...

def main():
    """Run verification for n=2,3,4,5,6."""
    for n in [2, 3, 4, 5, 6]:
        analyze_eulerian(n)
        verify_alternating_correspondence(n)

    # Special analysis: Eulerian numbers are unimodal and symmetric
    print(f"\n{'='*60}")
    print("Key observations:")
    print(f"{'='*60}")
    print("""
1. Eulerian numbers A(n,k) are unimodal: they increase to a maximum then decrease
2. They are symmetric: A(n,k) = A(n,n-1-k)
3. Maximum occurs at k = floor((n-1)/2) and k = ceil((n-1)/2)
4. For n even: two maxima at k=(n-2)/2 and k=n/2
5. For n odd: single maximum at k=(n-1)/2

The question is: how does f(s) relate to Eulerian numbers?

For alternating sequences:
- (+,-,+,-,...): has floor((n-1)/2) positions with -1
- (-,+,-,+,...): has ceil((n-1)/2) positions with -1

But f(s) doesn't count permutations with k descents total - it counts
permutations where descents occur exactly at the positions specified by s.
""")

if __name__ == "__main__":
    main()
