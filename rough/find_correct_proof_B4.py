#!/usr/bin/env python3
"""
Find the correct proof for S <= (n+2)N/3.

The current proof approach (weighted average of depths) doesn't work.
Let's find what actually makes the bound hold.

Key observation: S <= sum_depths, but sum_depths can violate (n+2)N/3.
So we need to show S is even smaller than sum_depths in certain cases.
"""

import numpy as np
from verify_B4 import generate_all_valid_matrices, compute_S_N, compute_depth_distribution

def detailed_analysis(A: np.ndarray):
    """Analyze relationship between S, sum_depths, and N"""
    n = len(A)
    S, N = compute_S_N(A)

    sum_depths = 0
    sum_values = 0

    entries = []  # (i, j, depth, value)

    for i in range(n):
        for j in range(n):
            depth = (i+1) + (j+1) - n
            if depth > 0 and A[i][j] > 0:
                sum_depths += depth
                sum_values += A[i][j]
                entries.append((i+1, j+1, depth, A[i][j]))

    return {
        'S': S,
        'N': N,
        'sum_depths': sum_depths,
        'entries': entries,
        'matrix': A
    }

def find_pattern():
    """Find patterns in valid matrices"""
    print("="*60)
    print("Pattern Analysis for n=2,3")
    print("="*60)

    for n in [2, 3]:
        print(f"\n{'='*60}")
        print(f"n = {n}")
        print(f"{'='*60}")

        matrices = generate_all_valid_matrices(n)

        # Group by S/N ratio
        ratio_groups = {}

        for A in matrices:
            S, N = compute_S_N(A)
            if N > 0:
                ratio = round(S / N, 6)
                if ratio not in ratio_groups:
                    ratio_groups[ratio] = []
                ratio_groups[ratio].append(A)

        # Show examples from each ratio group
        sorted_ratios = sorted(ratio_groups.keys(), reverse=True)

        print(f"\nFound {len(sorted_ratios)} distinct S/N ratios:")
        for ratio in sorted_ratios[:10]:  # top 10
            count = len(ratio_groups[ratio])
            print(f"  S/N = {ratio:.6f}: {count} matrices")

            # Show one example
            if ratio >= (n+2)/3 - 0.01:  # near the bound
                A = ratio_groups[ratio][0]
                info = detailed_analysis(A)
                print(f"    Example:")
                print(f"    Matrix:\n{np.array2string(A, prefix='    ')}")
                print(f"    S={info['S']}, N={info['N']}, sum_depths={info['sum_depths']}")
                print(f"    Entries: {info['entries']}")

def check_alternative_bound():
    """
    Check if there's a tighter relationship.

    Hypothesis: Maybe we need to sum over all positions, not just nonzero ones?
    Or maybe there's a constraint on the sum based on the path structure?
    """
    print("\n" + "="*60)
    print("Alternative Bound Analysis")
    print("="*60)

    for n in [2, 3]:
        print(f"\nn = {n}:")
        matrices = generate_all_valid_matrices(n)

        # For each matrix, compute various quantities
        max_ratio = 0
        tight_example = None

        for A in matrices:
            S, N = compute_S_N(A)

            if N > 0:
                ratio = S / N

                if ratio > max_ratio:
                    max_ratio = ratio
                    tight_example = A

        print(f"Maximum S/N = {max_ratio:.6f}")
        print(f"Bound (n+2)/3 = {(n+2)/3:.6f}")

        if tight_example is not None:
            print(f"\nMatrix achieving maximum S/N:")
            print(tight_example)

            # Analyze paths from boundary to each nonzero entry
            print(f"\nPath analysis:")
            for i in range(n):
                for j in range(n):
                    if tight_example[i][j] > 0:
                        depth = (i+1) + (j+1) - n
                        value = tight_example[i][j]
                        print(f"  ({i+1},{j+1}): depth={depth}, value={value}")

                        # Check: value = depth?
                        if value == depth:
                            print(f"    -> value equals depth!")
                        else:
                            print(f"    -> value < depth (gap = {depth - value})")

def compute_total_sum_over_region(n: int):
    """
    Compute the sum over ALL positions in the nonzero region for the tight matrix.
    This is the maximum possible S.
    """
    # Tight matrix: a_{i,j} = i+j-n for all i+j > n
    total = 0
    count = 0

    for i in range(1, n+1):
        for j in range(1, n+1):
            if i + j > n:
                depth = i + j - n
                total += depth
                count += 1

    avg = total / count
    print(f"\nn={n}: Total sum if all entries = depth: {total}")
    print(f"  Number of positions: {count}")
    print(f"  Average: {avg:.6f}")
    print(f"  This equals (n+2)/3 * count = {(n+2)/3 * count:.6f}")
    print(f"  So max(S) = (n+2)/3 * max(N) when N = {count}")

def main():
    find_pattern()
    check_alternative_bound()

    print("\n" + "="*60)
    print("Computing Maximum S")
    print("="*60)

    for n in [2, 3, 4, 5]:
        compute_total_sum_over_region(n)

if __name__ == "__main__":
    main()
