#!/usr/bin/env python3
"""
Verify the CORRECT proof for S <= (n+2)N/3.

The key insight is NOT about weighted averages of depths for nonzero entries.
Instead, we need to show that S is maximized when we use a specific structure.

CORRECT APPROACH:
-----------------
We'll use a POTENTIAL FUNCTION argument.

Define the potential: Phi = sum_{i,j: i+j>n} a_{i,j}

We want to show: Phi <= (n+2)/3 * N

where N = number of positions with a_{i,j} > 0.

Key lemma: For any valid matrix, we can compute S by summing contributions
from "layers" of the matrix.
"""

import numpy as np
from verify_B4 import generate_all_valid_matrices, compute_S_N, compute_depth_distribution

def compute_contribution_by_depth(A: np.ndarray):
    """
    Compute the contribution to S from each depth layer.

    For depth ell, sum the values of all entries at that depth.
    """
    n = len(A)
    contributions = {}

    for i in range(n):
        for j in range(n):
            depth = (i+1) + (j+1) - n
            if depth > 0 and A[i][j] > 0:
                if depth not in contributions:
                    contributions[depth] = 0
                contributions[depth] += A[i][j]

    return contributions

def verify_convexity_argument(n: int):
    """
    Verify that S/N is maximized when all positions are filled with value=depth.

    This suggests the bound comes from the fact that:
    - Maximum S occurs when N is maximal AND all values = depth
    - For any subset of positions, filling them with value=depth gives S/N <= (n+2)/3
    """
    print(f"\n{'='*60}")
    print(f"Convexity Argument for n={n}")
    print(f"{'='*60}")

    matrices = generate_all_valid_matrices(n)

    # Find max S for each value of N
    max_S_for_N = {}

    for A in matrices:
        S, N = compute_S_N(A)

        if N not in max_S_for_N:
            max_S_for_N[N] = (S, A.copy())
        else:
            if S > max_S_for_N[N][0]:
                max_S_for_N[N] = (S, A.copy())

    print(f"\nMaximum S for each N:")
    for N in sorted(max_S_for_N.keys()):
        if N > 0:
            S, A = max_S_for_N[N]
            ratio = S / N
            bound = (n + 2) / 3
            print(f"  N={N}: max(S)={S}, S/N={ratio:.6f}, bound={bound:.6f}, " +
                  f"slack={(bound - ratio):.6f}")

            # Check if tight
            if abs(ratio - bound) < 1e-9:
                print(f"    -> TIGHT!")
                print(f"    Matrix:\n{np.array2string(A, prefix='    ')}")

    # Check if the bound S <= (n+2)N/3 holds for all N
    all_satisfy = True
    for N in max_S_for_N:
        if N > 0:
            S, _ = max_S_for_N[N]
            if S > (n + 2) * N / 3 + 1e-9:
                all_satisfy = False
                print(f"\n*** N={N}: max(S)={S} > {(n+2)*N/3:.6f} ***")

    if all_satisfy:
        print(f"\n✓ For all N, max(S) <= (n+2)N/3")

def check_necessary_condition_for_large_S(n: int):
    """
    Check: What properties must a matrix have to achieve large S/N?

    Hypothesis: To get S/N close to (n+2)/3, we need many low-depth entries.
    """
    print(f"\n{'='*60}")
    print(f"Necessary Conditions for Large S/N (n={n})")
    print(f"{'='*60}")

    matrices = generate_all_valid_matrices(n)

    # Group by S/N
    high_ratio = []
    low_ratio = []

    bound = (n + 2) / 3

    for A in matrices:
        S, N = compute_S_N(A)
        if N > 0:
            ratio = S / N
            if ratio >= bound - 0.01:  # close to bound
                high_ratio.append((A.copy(), S, N, ratio))
            elif ratio <= bound * 0.7:  # significantly below
                low_ratio.append((A.copy(), S, N, ratio))

    print(f"\nHigh ratio matrices (S/N >= {bound-0.01:.3f}): {len(high_ratio)}")
    for i, (A, S, N, ratio) in enumerate(high_ratio[:3]):
        print(f"\n  Example {i+1}: S/N = {ratio:.6f}")
        print(f"  Matrix:\n{np.array2string(A, prefix='  ')}")
        depth_dist = compute_depth_distribution(A)
        print(f"  Depth distribution: {depth_dist}")

        # Check: What fraction of nonzero region is filled?
        total_positions_in_region = n * (n + 1) // 2
        fill_rate = N / total_positions_in_region
        print(f"  Fill rate: {N}/{total_positions_in_region} = {fill_rate:.3f}")

    print(f"\nLow ratio matrices (S/N <= {bound*0.7:.3f}): {len(low_ratio)}")
    for i, (A, S, N, ratio) in enumerate(low_ratio[:3]):
        print(f"\n  Example {i+1}: S/N = {ratio:.6f}")
        print(f"  Matrix:\n{np.array2string(A, prefix='  ')}")
        depth_dist = compute_depth_distribution(A)
        print(f"  Depth distribution: {depth_dist}")

        total_positions_in_region = n * (n + 1) // 2
        fill_rate = N / total_positions_in_region
        print(f"  Fill rate: {N}/{total_positions_in_region} = {fill_rate:.3f}")

def main():
    for n in [2, 3]:
        verify_convexity_argument(n)
        check_necessary_condition_for_large_S(n)

if __name__ == "__main__":
    main()
