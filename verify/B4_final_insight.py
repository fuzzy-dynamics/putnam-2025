#!/usr/bin/env python3
"""
Final insight: Find the correct proof structure.

HYPOTHESIS:
The bound S <= (n+2)N/3 holds because of the MONOTONICITY constraints.

Key observation: If we want large values, we need them at large depths.
But large depths are "far" from the boundary, so there are fewer positions.

Let's verify: Can we get S > (n+2)N/3 by concentrating high values
at specific depths?
"""

import numpy as np
from verify_B4 import generate_all_valid_matrices, compute_S_N, compute_depth_distribution

def analyze_greedy_strategies(n: int):
    """
    Try different greedy strategies to maximize S/N:

    Strategy 1: Fill all positions at depth 1, then depth 2, etc.
    Strategy 2: Fill only high-depth positions with high values
    Strategy 3: Fill a "diagonal" pattern
    etc.

    Compare against the actual maximum.
    """
    print(f"\n{'='*60}")
    print(f"Greedy Strategy Analysis (n={n})")
    print(f"{'='*60}")

    # Find all valid matrices
    matrices = generate_all_valid_matrices(n)

    # Find maximum S for each N
    max_S_by_N = {}
    for A in matrices:
        S, N = compute_S_N(A)
        if N > 0:
            if N not in max_S_by_N:
                max_S_by_N[N] = (S, A.copy())
            else:
                if S > max_S_by_N[N][0]:
                    max_S_by_N[N] = (S, A.copy())

    # Analyze which matrices achieve maximum S for each N
    print(f"\nMaximum S matrices for each N:")

    for N in sorted(max_S_by_N.keys()):
        S, A = max_S_by_N[N]
        print(f"\nN={N}, max(S)={S}, S/N={S/N:.3f}:")
        print(A)

        # Compute depth distribution
        depth_dist = compute_depth_distribution(A)
        print(f"Depth distribution: {depth_dist}")

        # Check if all entries have value = depth
        all_saturated = True
        for i in range(n):
            for j in range(n):
                depth = (i+1) + (j+1) - n
                if depth > 0 and A[i][j] > 0:
                    if A[i][j] != depth:
                        all_saturated = False
                        break

        if all_saturated:
            print("All nonzero entries saturate the depth bound!")

def check_partial_filling_patterns(n: int):
    """
    For matrices with N < max, which patterns give the highest S?

    Hypothesis: To maximize S for a given N, we should:
    1. Fill positions starting from low depths (to satisfy monotonicity)
    2. Make all values equal to their depth
    """
    print(f"\n{'='*60}")
    print(f"Partial Filling Patterns (n={n})")
    print(f"{'='*60}")

    matrices = generate_all_valid_matrices(n)

    # For each N, find all matrices achieving maximum S
    max_S_matrices = {}

    for A in matrices:
        S, N = compute_S_N(A)
        if N > 0:
            if N not in max_S_matrices:
                max_S_matrices[N] = []
            max_S_matrices[N].append((S, A.copy()))

    # For each N, find maximum S and all matrices achieving it
    for N in sorted(max_S_matrices.keys()):
        max_S = max(S for S, _ in max_S_matrices[N])
        optimal_matrices = [A for S, A in max_S_matrices[N] if S == max_S]

        print(f"\nN={N}: max(S)={max_S}, {len(optimal_matrices)} optimal matrices")

        # Check if all optimal matrices have the same property
        if len(optimal_matrices) <= 3:
            for i, A in enumerate(optimal_matrices):
                print(f"  Optimal matrix {i+1}:")
                print(f"{np.array2string(A, prefix='  ')}")

                # Check pattern
                depth_dist = compute_depth_distribution(A)
                print(f"  Depth distribution: {depth_dist}")

def verify_key_lemma(n: int):
    """
    Verify the key lemma that might make the proof work.

    CONJECTURE: For any valid matrix with N nonzero entries,
    if we sum the depths of all nonzero entries, we get:
        sum_{a_{i,j} > 0} (i+j-n) >= ... (some bound involving N)

    Or maybe: The "deficit" (depth - value) satisfies some property?
    """
    print(f"\n{'='*60}")
    print(f"Key Lemma Verification (n={n})")
    print(f"{'='*60}")

    matrices = generate_all_valid_matrices(n)

    # For each matrix, compute:
    # - S = sum of values
    # - D = sum of depths for nonzero entries
    # - N = number of nonzero entries

    print(f"\n{'S':>4} {'N':>4} {'D':>4} {'S/N':>7} {'D/N':>7} {'(D-S)':>7} {'bound':>7} {'S-bound':>7}")
    print("-" * 80)

    for A in matrices:
        S, N = compute_S_N(A)

        if N == 0:
            continue

        # Compute sum of depths
        D = 0
        for i in range(n):
            for j in range(n):
                depth = (i+1) + (j+1) - n
                if depth > 0 and A[i][j] > 0:
                    D += depth

        bound = (n + 2) * N / 3
        S_ratio = S / N
        D_ratio = D / N

        print(f"{S:4d} {N:4d} {D:4d} {S_ratio:7.3f} {D_ratio:7.3f} {D-S:7d} {bound:7.3f} {S-bound:7.3f}")

    # Check: Is there a relationship between D and N?
    print(f"\n" + "="*60)
    print("Checking if D has a bound in terms of N...")

    max_D_by_N = {}
    for A in matrices:
        S, N = compute_S_N(A)
        if N == 0:
            continue

        D = 0
        for i in range(n):
            for j in range(n):
                depth = (i+1) + (j+1) - n
                if depth > 0 and A[i][j] > 0:
                    D += depth

        if N not in max_D_by_N:
            max_D_by_N[N] = D
        else:
            max_D_by_N[N] = max(max_D_by_N[N], D)

    print(f"\n{'N':>4} {'max(D)':>7} {'(n+2)N/3':>10} {'D exceeds bound?':>20}")
    for N in sorted(max_D_by_N.keys()):
        D = max_D_by_N[N]
        bound = (n + 2) * N / 3
        exceeds = "YES" if D > bound + 0.01 else "NO"
        print(f"{N:4d} {D:7d} {bound:10.3f} {exceeds:>20}")

def main():
    for n in [2, 3]:
        analyze_greedy_strategies(n)
        check_partial_filling_patterns(n)
        verify_key_lemma(n)

if __name__ == "__main__":
    main()
