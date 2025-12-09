#!/usr/bin/env python3
"""
Verification script for Putnam 2025 B4 solution.

Enumerates all valid matrices for small n and checks:
1. Whether S <= (n+2)N/3 holds for all valid matrices
2. Whether the Support Lemma is correct
3. What the actual maximum ratio S/N is
"""

from itertools import product
import numpy as np
from typing import List, Tuple

def is_valid_matrix(A: np.ndarray) -> bool:
    """
    Check if matrix A satisfies all conditions:
    (a) a_{i,j} = 0 when i+j <= n
    (b) a_{i+1,j} in {a_{i,j}, a_{i,j}+1}
    (c) a_{i,j+1} in {a_{i,j}, a_{i,j}+1}

    Uses 0-indexing: A[i][j] corresponds to position (i+1, j+1)
    """
    n = len(A)

    # Check condition (a): zero region
    for i in range(n):
        for j in range(n):
            if (i+1) + (j+1) <= n:
                if A[i][j] != 0:
                    return False

    # Check conditions (b) and (c): monotonicity
    for i in range(n):
        for j in range(n):
            # Check down (b): a_{i+1,j} in {a_{i,j}, a_{i,j}+1}
            if i + 1 < n:
                if A[i+1][j] not in [A[i][j], A[i][j] + 1]:
                    return False

            # Check right (c): a_{i,j+1} in {a_{i,j}, a_{i,j}+1}
            if j + 1 < n:
                if A[i][j+1] not in [A[i][j], A[i][j] + 1]:
                    return False

    return True

def generate_all_valid_matrices(n: int, max_value: int = None) -> List[np.ndarray]:
    """
    Generate all valid matrices for given n.
    Uses depth bound: a_{i,j} <= i+j-n
    """
    if max_value is None:
        max_value = n  # depth bound ensures a_{i,j} <= n

    # Only need to consider nonzero region: i+j > n
    nonzero_positions = []
    for i in range(n):
        for j in range(n):
            if (i+1) + (j+1) > n:
                nonzero_positions.append((i, j))

    num_positions = len(nonzero_positions)

    valid_matrices = []

    # Try all possible value assignments (0 to max_value for each position)
    total_configs = (max_value + 1) ** num_positions
    print(f"Checking {total_configs} configurations for n={n}...")

    for values in product(range(max_value + 1), repeat=num_positions):
        A = np.zeros((n, n), dtype=int)
        for idx, (i, j) in enumerate(nonzero_positions):
            A[i][j] = values[idx]

        if is_valid_matrix(A):
            valid_matrices.append(A.copy())

    return valid_matrices

def compute_S_N(A: np.ndarray) -> Tuple[int, int]:
    """Compute S (sum of entries) and N (number of nonzero entries)"""
    n = len(A)
    S = 0
    N = 0

    for i in range(n):
        for j in range(n):
            if A[i][j] > 0:
                S += A[i][j]
                N += 1

    return S, N

def compute_depth_distribution(A: np.ndarray) -> dict:
    """Compute N_ell for each depth ell"""
    n = len(A)
    N_ell = {}

    for i in range(n):
        for j in range(n):
            depth = (i+1) + (j+1) - n
            if depth > 0 and A[i][j] > 0:
                N_ell[depth] = N_ell.get(depth, 0) + 1

    return N_ell

def check_support_lemma(A: np.ndarray) -> bool:
    """
    Check if Support Lemma holds:
    If there are k nonzero entries at depth ell >= 2,
    then there are at least ceil(k/2) nonzero entries at depth ell-1
    """
    n = len(A)
    depth_dist = compute_depth_distribution(A)

    for ell in range(2, n+1):
        if ell in depth_dist:
            k = depth_dist[ell]
            required = (k + 1) // 2  # ceil(k/2)
            actual = depth_dist.get(ell - 1, 0)
            if actual < required:
                return False

    return True

def verify_bound(n: int):
    """Verify the bound S <= (n+2)N/3 for all valid matrices"""
    print(f"\n{'='*60}")
    print(f"Verifying n = {n}")
    print(f"{'='*60}")

    matrices = generate_all_valid_matrices(n)
    print(f"Found {len(matrices)} valid matrices\n")

    violations = []
    max_ratio = 0
    max_ratio_matrix = None
    support_lemma_violations = []

    for A in matrices:
        S, N = compute_S_N(A)

        if N > 0:
            ratio = S / N
            bound = (n + 2) / 3

            if ratio > max_ratio:
                max_ratio = ratio
                max_ratio_matrix = A.copy()

            if S > (n + 2) * N / 3 + 1e-9:  # small epsilon for floating point
                violations.append((A.copy(), S, N, ratio))

            # Check Support Lemma
            if not check_support_lemma(A):
                support_lemma_violations.append(A.copy())

    # Report results
    print(f"Maximum ratio S/N: {max_ratio:.6f}")
    print(f"Theoretical bound (n+2)/3: {(n+2)/3:.6f}")

    if max_ratio_matrix is not None:
        print(f"\nMatrix achieving maximum ratio:")
        print(max_ratio_matrix)
        S, N = compute_S_N(max_ratio_matrix)
        print(f"S = {S}, N = {N}, S/N = {S/N:.6f}")
        print(f"Depth distribution:", compute_depth_distribution(max_ratio_matrix))

    if violations:
        print(f"\n*** BOUND VIOLATED: {len(violations)} counterexamples found! ***")
        for i, (A, S, N, ratio) in enumerate(violations[:5]):  # show first 5
            print(f"\nCounterexample {i+1}:")
            print(A)
            print(f"S = {S}, N = {N}, S/N = {ratio:.6f} > {(n+2)/3:.6f}")
    else:
        print(f"\n✓ Bound S <= (n+2)N/3 holds for all {len(matrices)} valid matrices")

    if support_lemma_violations:
        print(f"\n*** SUPPORT LEMMA VIOLATED: {len(support_lemma_violations)} counterexamples found! ***")
        for i, A in enumerate(support_lemma_violations[:5]):
            print(f"\nSupport Lemma Counterexample {i+1}:")
            print(A)
            print(f"Depth distribution:", compute_depth_distribution(A))
    else:
        print(f"\n✓ Support Lemma holds for all valid matrices")

    return len(violations) == 0, len(support_lemma_violations) == 0

def main():
    print("Putnam 2025 B4 Verification")
    print("="*60)

    # Test for n=2 and n=3
    bound_holds = True
    support_holds = True

    for n in [2, 3]:
        b, s = verify_bound(n)
        bound_holds = bound_holds and b
        support_holds = support_holds and s

    print(f"\n{'='*60}")
    print("FINAL VERDICT")
    print(f"{'='*60}")

    if bound_holds:
        print("✓ Main bound S <= (n+2)N/3 holds for n=2,3")
    else:
        print("✗ Main bound VIOLATED for some n")

    if support_holds:
        print("✓ Support Lemma holds for n=2,3")
    else:
        print("✗ Support Lemma VIOLATED for some n")

    # Additional analysis: check if bound is tight
    print("\n" + "="*60)
    print("TIGHTNESS ANALYSIS")
    print("="*60)

    for n in [2, 3]:
        matrices = generate_all_valid_matrices(n)
        max_ratio = 0
        tight_matrix = None

        for A in matrices:
            S, N = compute_S_N(A)
            if N > 0:
                ratio = S / N
                if ratio > max_ratio:
                    max_ratio = ratio
                    tight_matrix = A.copy()

        print(f"\nn={n}: max(S/N) = {max_ratio:.6f}, bound = {(n+2)/3:.6f}")
        if abs(max_ratio - (n+2)/3) < 1e-9:
            print(f"  → Bound is TIGHT (equality achieved)")
            print(f"  Matrix achieving equality:")
            print(tight_matrix)
        else:
            print(f"  → Bound is NOT tight (gap = {(n+2)/3 - max_ratio:.6f})")

if __name__ == "__main__":
    main()
