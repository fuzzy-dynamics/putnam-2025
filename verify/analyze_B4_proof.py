#!/usr/bin/env python3
"""
Analyze why S <= (n+2)N/3 holds.

The Support Lemma is false, but the bound is correct.
Let's find the real reason.
"""

import numpy as np
from verify_B4 import generate_all_valid_matrices, compute_S_N, compute_depth_distribution

def analyze_matrix(A: np.ndarray, verbose=True):
    """Analyze a single matrix in detail"""
    n = len(A)
    S, N = compute_S_N(A)
    depth_dist = compute_depth_distribution(A)

    if verbose:
        print(f"\nMatrix:")
        print(A)
        print(f"S = {S}, N = {N}")
        if N > 0:
            print(f"S/N = {S/N:.6f}, bound = {(n+2)/3:.6f}")
        print(f"Depth distribution N_ell: {depth_dist}")

    # Compute sum of depths for nonzero entries
    sum_depths = 0
    for i in range(n):
        for j in range(n):
            depth = (i+1) + (j+1) - n
            if depth > 0 and A[i][j] > 0:
                sum_depths += depth

    if verbose and N > 0:
        print(f"Sum of depths for nonzero entries: {sum_depths}")
        print(f"Average depth of nonzero entries: {sum_depths/N:.6f}")
        print(f"S / sum_depths = {S / sum_depths:.6f}" if sum_depths > 0 else "S / sum_depths = N/A")

    # Check: S <= sum_depths (since a_{i,j} <= depth)
    if S > sum_depths:
        print("*** ERROR: S > sum_depths (violates Lemma 1)")

    # Check: sum_depths <= (n+2)/3 * N
    if N > 0:
        if sum_depths > (n+2)/3 * N + 1e-9:
            print(f"*** sum_depths = {sum_depths} > {(n+2)/3 * N:.6f} = (n+2)N/3")
            print("*** This would violate the weighted average bound!")

    return S, N, sum_depths, depth_dist

def check_weighted_average_property(n: int):
    """
    Check if: sum_{ell=1}^n ell * N_ell <= (n+2)/3 * sum_{ell=1}^n N_ell
    for all valid matrices.

    This is the KEY inequality that the proof needs to establish.
    """
    print(f"\n{'='*60}")
    print(f"Weighted Average Property for n={n}")
    print(f"{'='*60}")

    matrices = generate_all_valid_matrices(n)

    violations = []
    max_weighted_avg = 0
    max_matrix = None

    for A in matrices:
        S, N, sum_depths, depth_dist = analyze_matrix(A, verbose=False)

        if N > 0:
            weighted_avg = sum_depths / N
            if weighted_avg > max_weighted_avg:
                max_weighted_avg = weighted_avg
                max_matrix = A.copy()

            if sum_depths > (n+2)/3 * N + 1e-9:
                violations.append((A.copy(), sum_depths, N, weighted_avg))

    print(f"Maximum weighted average depth: {max_weighted_avg:.6f}")
    print(f"Theoretical bound (n+2)/3: {(n+2)/3:.6f}")

    if max_matrix is not None:
        print(f"\nMatrix achieving maximum weighted average:")
        analyze_matrix(max_matrix, verbose=True)

    if violations:
        print(f"\n*** WEIGHTED AVERAGE BOUND VIOLATED ***")
        for A, sum_depths, N, avg in violations[:3]:
            print(f"\nCounterexample:")
            analyze_matrix(A, verbose=True)
    else:
        print(f"\n✓ Weighted average bound holds for all {len(matrices)} valid matrices")

    return len(violations) == 0

def find_support_structure(A: np.ndarray):
    """
    For each nonzero entry, trace back to see which lower-depth entries support it.
    """
    n = len(A)
    print(f"\nSupport structure analysis:")
    print(A)

    for i in range(n):
        for j in range(n):
            if A[i][j] > 0:
                depth = (i+1) + (j+1) - n
                print(f"\nPosition ({i+1},{j+1}), depth={depth}, value={A[i][j]}")

                # Find predecessors
                predecessors = []
                if i > 0:
                    pred_depth = i + (j+1) - n
                    predecessors.append((i, j-1, pred_depth, "up", A[i-1][j] if i > 0 else None))
                if j > 0:
                    pred_depth = (i+1) + j - n
                    predecessors.append((i-1, j, pred_depth, "left", A[i][j-1] if j > 0 else None))

                for pi, pj, pd, direction, pval in predecessors:
                    if pi >= 0 and pj >= 0:
                        print(f"  Predecessor {direction}: ({pi+1},{pj+1}), depth={pd}, value={pval}")

def main():
    # Check weighted average property
    for n in [2, 3]:
        check_weighted_average_property(n)

    # Analyze specific matrices to understand support structure
    print(f"\n{'='*60}")
    print("Support Structure Examples")
    print(f"{'='*60}")

    # Example: tight matrix for n=3
    A_tight = np.array([[0, 0, 1],
                        [0, 1, 2],
                        [1, 2, 3]])
    print("\nTight matrix (achieves equality):")
    find_support_structure(A_tight)

    # Example: sparse matrix
    A_sparse = np.array([[0, 0, 0],
                         [0, 0, 1],
                         [0, 1, 2]])
    print("\n\nSparse matrix:")
    find_support_structure(A_sparse)

if __name__ == "__main__":
    main()
