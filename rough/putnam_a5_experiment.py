#!/usr/bin/env python3
"""
Putnam 2025 A5: Experiment with sign sequences

For a sequence s=(s_1,...,s_{n-1}) where each s_i = ±1,
f(s) = number of permutations (a_1,...,a_n) of {1,...,n} such that
s_i(a_{i+1} - a_i) > 0 for all i.

s_i = +1 means a_{i+1} > a_i (ascent)
s_i = -1 means a_{i+1} < a_i (descent)
"""

from itertools import permutations, product

def compute_f(n, s):
    """
    Compute f(s) for a given n and sign sequence s.
    s is a tuple of +1 and -1 of length n-1.
    """
    count = 0
    for perm in permutations(range(1, n+1)):
        valid = True
        for i in range(n-1):
            diff = perm[i+1] - perm[i]
            if s[i] * diff <= 0:  # s_i * (a_{i+1} - a_i) must be > 0
                valid = False
                break
        if valid:
            count += 1
    return count

def sequence_to_string(s):
    """Convert sequence like (1, -1, 1) to string like '+,-,+'"""
    return ','.join(['+' if x == 1 else '-' for x in s])

def analyze_n(n):
    """Analyze all possible sequences for a given n."""
    print(f"\n{'='*60}")
    print(f"n = {n}")
    print(f"{'='*60}")

    # Generate all possible sign sequences of length n-1
    results = {}
    for s in product([1, -1], repeat=n-1):
        f_s = compute_f(n, s)
        results[s] = f_s

    # Find maximum value
    max_f = max(results.values())

    # Print all sequences and their f(s) values
    print(f"\nAll sequences and their f(s) values:")
    print(f"{'Sequence':<20} f(s)")
    print(f"{'-'*30}")

    for s in sorted(results.keys(), key=lambda x: results[x], reverse=True):
        marker = " <-- MAX" if results[s] == max_f else ""
        print(f"{sequence_to_string(s):<20} {results[s]}{marker}")

    # Print maximizing sequences
    max_sequences = [s for s, f in results.items() if f == max_f]
    print(f"\nMaximum f(s) = {max_f}")
    print(f"Number of maximizing sequences: {len(max_sequences)}")
    print(f"\nMaximizing sequences:")
    for s in max_sequences:
        print(f"  {sequence_to_string(s)}")

    return results, max_f, max_sequences

def check_alternating_pattern(max_sequences, n):
    """Check if maximizing sequences are alternating."""
    print(f"\n{'='*60}")
    print("Pattern Analysis")
    print(f"{'='*60}")

    alternating = []
    for s in max_sequences:
        # Check if it's alternating (either +,-,+,- or -,+,-,+)
        is_alternating = all(s[i] != s[i+1] for i in range(len(s)-1))
        if is_alternating:
            alternating.append(s)

    if alternating:
        print(f"\nAlternating sequences among maximizers: {len(alternating)}/{len(max_sequences)}")
        for s in alternating:
            print(f"  {sequence_to_string(s)}")
    else:
        print("\nNo alternating sequences found among maximizers.")

    # Check other patterns
    print("\nChecking other patterns:")

    # Check if constant sequences are maximizers
    constant_plus = tuple([1] * (n-1))
    constant_minus = tuple([-1] * (n-1))

    if constant_plus in max_sequences:
        print(f"  All ascending (+,+,...,+) IS a maximizer")
    else:
        print(f"  All ascending (+,+,...,+) is NOT a maximizer")

    if constant_minus in max_sequences:
        print(f"  All descending (-,-,...,-) IS a maximizer")
    else:
        print(f"  All descending (-,-,...,-) is NOT a maximizer")

def main():
    """Run experiments for n=2,3,4,5."""
    for n in [2, 3, 4, 5]:
        results, max_f, max_sequences = analyze_n(n)
        check_alternating_pattern(max_sequences, n)

        # Show some example permutations for maximizing sequences
        if n <= 4:
            print(f"\nExample permutations for some maximizing sequences (n={n}):")
            for s in max_sequences[:2]:  # Show first 2 maximizing sequences
                print(f"\n  Sequence {sequence_to_string(s)}:")
                count = 0
                for perm in permutations(range(1, n+1)):
                    valid = True
                    for i in range(n-1):
                        diff = perm[i+1] - perm[i]
                        if s[i] * diff <= 0:
                            valid = False
                            break
                    if valid:
                        print(f"    {perm}")
                        count += 1
                        if count >= 5:  # Show max 5 examples
                            if compute_f(n, s) > 5:
                                print(f"    ... ({compute_f(n, s) - 5} more)")
                            break

if __name__ == "__main__":
    main()
