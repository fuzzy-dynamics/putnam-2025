#!/usr/bin/env python3
"""
Deeper analysis: understand the exact relationship.

Key insight: f(s) does NOT equal an Eulerian number directly.
f(s) counts permutations with a specific PATTERN of ascents/descents.

Let's think about it differently using alternating permutations theory.
"""

from itertools import permutations, product

def compute_f(n, s):
    """Compute f(s) for a given n and sign sequence s."""
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

def sequence_to_string(s):
    """Convert sequence to string."""
    return ','.join(['+' if x == 1 else '-' for x in s])

def count_runs(s):
    """
    Count the number of "runs" in sequence s.
    A run is a maximal sequence of consecutive identical signs.

    Example: (+,+,-,-,+) has 3 runs: (++), (--), (+)
    """
    if not s:
        return 0
    runs = 1
    for i in range(len(s) - 1):
        if s[i] != s[i+1]:
            runs += 1
    return runs

def main():
    """Analyze the relationship between f(s) and sequence properties."""

    for n in [3, 4, 5, 6]:
        print(f"\n{'='*70}")
        print(f"n = {n}")
        print(f"{'='*70}")

        results = []
        for s in product([1, -1], repeat=n-1):
            f_s = compute_f(n, s)
            num_runs = count_runs(s)
            num_descents = sum(1 for x in s if x == -1)
            results.append((s, f_s, num_runs, num_descents))

        # Sort by f(s) descending
        results.sort(key=lambda x: x[1], reverse=True)

        max_f = results[0][1]

        print(f"\n{'Sequence':<20} {'f(s)':<8} {'Runs':<8} {'Descents':<10} {'Status'}")
        print(f"{'-'*70}")

        for s, f_s, runs, descents in results[:10]:  # Top 10
            marker = "MAX" if f_s == max_f else ""
            print(f"{sequence_to_string(s):<20} {f_s:<8} {runs:<8} {descents:<10} {marker}")

        # Analyze maximizers
        max_sequences = [r for r in results if r[1] == max_f]

        print(f"\n\nMaximizing sequences have:")
        runs_of_max = set(r[2] for r in max_sequences)
        desc_of_max = set(r[3] for r in max_sequences)

        print(f"  Number of runs: {runs_of_max}")
        print(f"  Number of descents: {desc_of_max}")

        # Check if all maximizers are alternating (n-1 runs)
        all_alternating = all(r[2] == n-1 for r in max_sequences)
        if all_alternating:
            print(f"  ✓ All maximizers have n-1 = {n-1} runs (fully alternating)")
        else:
            print(f"  ✗ Not all maximizers are fully alternating")

    # Key insight
    print(f"\n\n{'='*70}")
    print("KEY INSIGHT:")
    print(f"{'='*70}")
    print("""
The maximizing sequences are those with the MOST ALTERNATIONS.

For a sequence s of length n-1:
- A sequence has at most n-1 runs (when it alternates: +,-,+,- or -,+,-,+)
- There are exactly 2 fully alternating sequences:
  * Starting with +: (+,-,+,-,...)
  * Starting with -: (-,+,-,+,...)

These sequences maximize f(s) because they impose the LEAST restrictive
pattern on permutations. The intuition:

- A run of k consecutive +'s forces k consecutive ascents: a_i < a_{i+1} < ... < a_{i+k}
- A run of k consecutive -'s forces k consecutive descents: a_i > a_{i+1} > ... > a_{i+k}
- Longer runs are more restrictive
- Alternating sequences have runs of length 1, minimizing restrictions

This is related to the theory of up-down (alternating) permutations!
""")

if __name__ == "__main__":
    main()
