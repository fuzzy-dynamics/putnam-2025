#!/usr/bin/env python3
"""
Numerical optimization to find minimum dimension k for cycle graph C_n matrices.

For cycle graph C_n with vertices 0, 1, ..., n-1:
- A_i and A_j commute iff |i-j| = 1 (mod n)
- We search for minimum k such that k×k matrices exist with this pattern
"""

import numpy as np
from scipy.optimize import minimize
import itertools

def cycle_should_commute(i, j, n):
    """Check if vertices i and j are adjacent in cycle C_n"""
    diff = abs(i - j)
    return diff == 1 or diff == n - 1

def commutator_norm(A, B):
    """Compute ||AB - BA||_F^2 (Frobenius norm squared)"""
    comm = A @ B - B @ A
    return np.sum(comm ** 2)

def objective_function(params, n, k):
    """
    Objective function for optimization.

    params: flattened array of n matrices (each k×k)
    n: number of vertices in cycle
    k: dimension of matrices

    Returns: loss (sum of commutator norms for adjacent pairs + penalty for non-adjacent pairs)
    """
    # Reshape params into n matrices of size k×k
    matrices = []
    for i in range(n):
        start = i * k * k
        end = start + k * k
        M = params[start:end].reshape(k, k)
        matrices.append(M)

    loss = 0.0

    # For each pair of matrices
    for i in range(n):
        for j in range(i + 1, n):
            comm_norm = commutator_norm(matrices[i], matrices[j])

            if cycle_should_commute(i, j, n):
                # These should commute: minimize commutator
                loss += comm_norm
            else:
                # These should NOT commute: penalize if they do commute
                # Use negative exponential to encourage non-commutativity
                loss += 0.1 / (comm_norm + 1e-6)

    # Add regularization to prevent trivial zero matrices
    for M in matrices:
        norm = np.sum(M ** 2)
        # Penalize if norm is too small (want non-trivial matrices)
        if norm < 0.1:
            loss += 100 * (0.1 - norm) ** 2

    return loss

def check_solution(matrices, n, k, threshold=1e-3):
    """
    Check if matrices satisfy the commutativity pattern.

    Returns: (is_valid, max_error_commute, min_error_non_commute)
    """
    max_error_should_commute = 0.0
    min_error_should_not_commute = float('inf')

    for i in range(n):
        for j in range(i + 1, n):
            comm_norm = commutator_norm(matrices[i], matrices[j])

            if cycle_should_commute(i, j, n):
                max_error_should_commute = max(max_error_should_commute, comm_norm)
            else:
                min_error_should_not_commute = min(min_error_should_not_commute, comm_norm)

    is_valid = (max_error_should_commute < threshold and
                min_error_should_not_commute > threshold)

    return is_valid, max_error_should_commute, min_error_should_not_commute

def find_cycle_matrices(n, k, max_attempts=20, max_iter=10000, verbose=False):
    """
    Find k×k matrices with C_n commutativity pattern.

    Args:
        n: number of vertices in cycle
        k: dimension of matrices
        max_attempts: number of random initializations to try
        max_iter: maximum iterations for each optimization
        verbose: print detailed information

    Returns:
        matrices if found, None otherwise
    """
    best_loss = float('inf')
    best_matrices = None
    best_errors = None

    for attempt in range(max_attempts):
        # Random initialization
        np.random.seed(attempt * 1000 + n * 100 + k)
        params0 = np.random.randn(n * k * k) * 0.5

        # Optimize
        result = minimize(
            objective_function,
            params0,
            args=(n, k),
            method='L-BFGS-B',
            options={'maxiter': max_iter, 'disp': False}
        )

        # Extract matrices
        matrices = []
        for i in range(n):
            start = i * k * k
            end = start + k * k
            M = result.x[start:end].reshape(k, k)
            matrices.append(M)

        # Check solution
        is_valid, max_err_comm, min_err_non = check_solution(matrices, n, k)

        if result.fun < best_loss:
            best_loss = result.fun
            best_matrices = matrices
            best_errors = (max_err_comm, min_err_non)

        if verbose:
            print(f"  Attempt {attempt+1}: loss={result.fun:.6f}, "
                  f"max_err_comm={max_err_comm:.6f}, min_err_non={min_err_non:.6f}, "
                  f"valid={is_valid}")

        if is_valid:
            if verbose:
                print(f"  SUCCESS at attempt {attempt+1}!")
            return matrices, max_err_comm, min_err_non

    if verbose and best_matrices is not None:
        print(f"  Best result: loss={best_loss:.6f}, "
              f"max_err_comm={best_errors[0]:.6f}, min_err_non={best_errors[1]:.6f}")

    return None

def search_minimum_dimension(n, max_k=15, verbose=True):
    """
    Search for minimum k for cycle C_n.
    """
    if verbose:
        print(f"\n{'='*60}")
        print(f"Searching for minimum dimension k for cycle C_{n}")
        print(f"{'='*60}")

    for k in range(2, max_k + 1):
        if verbose:
            print(f"\nTrying k = {k}...")

        result = find_cycle_matrices(n, k, max_attempts=30, max_iter=15000, verbose=verbose)

        if result is not None:
            matrices, max_err_comm, min_err_non = result

            if verbose:
                print(f"\n*** FOUND: C_{n} works with k = {k} ***")
                print(f"Max commutator error (should commute): {max_err_comm:.2e}")
                print(f"Min commutator error (should not commute): {min_err_non:.2e}")
                print(f"\nMatrices:")
                for i, M in enumerate(matrices):
                    print(f"\nA_{i} =")
                    print(M)

            return k, matrices, max_err_comm, min_err_non

    if verbose:
        print(f"\nNo valid construction found for k up to {max_k}")

    return None

def verify_construction(matrices, n, verbose=True):
    """Verify that a construction satisfies the commutativity pattern"""
    k = matrices[0].shape[0]

    if verbose:
        print(f"\nVerifying C_{n} construction with k={k}:")
        print(f"{'='*60}")

    all_good = True

    for i in range(n):
        for j in range(i + 1, n):
            comm = matrices[i] @ matrices[j] - matrices[j] @ matrices[i]
            comm_norm = np.sum(comm ** 2) ** 0.5

            should_commute = cycle_should_commute(i, j, n)

            if should_commute:
                status = "PASS" if comm_norm < 1e-2 else "FAIL"
                if comm_norm >= 1e-2:
                    all_good = False
                if verbose:
                    print(f"A_{i} and A_{j} should COMMUTE:     ||[A_{i},A_{j}]|| = {comm_norm:.2e} [{status}]")
            else:
                status = "PASS" if comm_norm > 1e-2 else "FAIL"
                if comm_norm <= 1e-2:
                    all_good = False
                if verbose:
                    print(f"A_{i} and A_{j} should NOT commute: ||[A_{i},A_{j}]|| = {comm_norm:.2e} [{status}]")

    if verbose:
        print(f"{'='*60}")
        print(f"Overall: {'PASS' if all_good else 'FAIL'}")

    return all_good

def main():
    """Main search routine"""
    print("="*70)
    print("NUMERICAL SEARCH FOR MINIMUM DIMENSION k FOR CYCLE GRAPHS")
    print("="*70)

    results = {}

    for n in [4, 5, 6, 7, 8]:
        result = search_minimum_dimension(n, max_k=15, verbose=True)

        if result is not None:
            k, matrices, max_err_comm, min_err_non = result
            results[n] = k

            # Verify
            verify_construction(matrices, n, verbose=True)
        else:
            results[n] = None
            print(f"\n!!! Could not find valid construction for C_{n} !!!")

    # Summary
    print("\n" + "="*70)
    print("SUMMARY OF RESULTS")
    print("="*70)
    print("\nMinimum dimension k for each cycle:")
    print("-" * 40)
    for n in sorted(results.keys()):
        if results[n] is not None:
            print(f"C_{n}: k = {results[n]}")
        else:
            print(f"C_{n}: NOT FOUND")

    # Look for patterns
    print("\n" + "="*70)
    print("PATTERN ANALYSIS")
    print("="*70)

    valid_results = [(n, k) for n, k in results.items() if k is not None]

    if len(valid_results) >= 3:
        print("\nComparing k to various functions of n:")
        print("-" * 60)
        print(f"{'n':<6} {'k':<6} {'sqrt(n)':<12} {'n/2':<10} {'ceil(n/2)':<12} {'floor(n/2)':<12}")
        print("-" * 60)

        for n, k in sorted(valid_results):
            sqrt_n = n ** 0.5
            n_half = n / 2
            ceil_half = (n + 1) // 2
            floor_half = n // 2

            print(f"{n:<6} {k:<6} {sqrt_n:<12.2f} {n_half:<10.1f} {ceil_half:<12} {floor_half:<12}")

        # Check if k = ceil(n/2)
        print("\n" + "-" * 60)
        pattern_ceil = all(k == (n + 1) // 2 for n, k in valid_results)
        pattern_floor = all(k == n // 2 for n, k in valid_results)

        if pattern_ceil:
            print("PATTERN FOUND: k = ceil(n/2)")
        elif pattern_floor:
            print("PATTERN FOUND: k = floor(n/2)")
        else:
            print("Checking other patterns...")

            # Check linear relationship
            if len(valid_results) >= 2:
                ns = np.array([n for n, k in valid_results])
                ks = np.array([k for n, k in valid_results])

                # Fit k = a*n + b
                A = np.column_stack([ns, np.ones(len(ns))])
                coeffs, residuals, rank, s = np.linalg.lstsq(A, ks, rcond=None)
                a, b = coeffs

                print(f"\nLinear fit: k ≈ {a:.3f}*n + {b:.3f}")

                if residuals.size > 0:
                    print(f"Residual: {residuals[0]:.6f}")

if __name__ == "__main__":
    main()
