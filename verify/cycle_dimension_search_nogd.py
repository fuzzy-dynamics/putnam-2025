#!/usr/bin/env python3
"""
Numerical optimization to find minimum dimension k for cycle graph C_n matrices.
Uses pure numpy gradient descent (no scipy).

For cycle graph C_n with vertices 0, 1, ..., n-1:
- A_i and A_j commute iff |i-j| = 1 (mod n)
- We search for minimum k such that k×k matrices exist with this pattern
"""

import numpy as np

def cycle_should_commute(i, j, n):
    """Check if vertices i and j are adjacent in cycle C_n"""
    diff = abs(i - j)
    return diff == 1 or diff == n - 1

def commutator_norm(A, B):
    """Compute ||AB - BA||_F^2 (Frobenius norm squared)"""
    comm = A @ B - B @ A
    return np.sum(comm ** 2)

def objective_and_gradient(matrices, n, k):
    """
    Compute objective function and gradients.

    Returns: (loss, gradients)
    """
    loss = 0.0
    gradients = [np.zeros((k, k)) for _ in range(n)]

    # For each pair of matrices
    for i in range(n):
        for j in range(i + 1, n):
            A, B = matrices[i], matrices[j]
            comm = A @ B - B @ A
            comm_norm_sq = np.sum(comm ** 2)

            if cycle_should_commute(i, j, n):
                # These should commute: minimize ||[A,B]||^2
                loss += comm_norm_sq

                # Gradient of ||AB - BA||^2 w.r.t. A:
                # d/dA ||AB - BA||^2 = 2(AB - BA)(B^T) - 2B^T(AB - BA)^T
                grad_A = 2 * (comm @ B.T - B.T @ comm.T)
                gradients[i] += grad_A

                # Gradient w.r.t. B:
                # d/dB ||AB - BA||^2 = 2A^T(AB - BA) - 2(AB - BA)^T A^T
                grad_B = 2 * (A.T @ comm - comm.T @ A.T)
                gradients[j] += grad_B

            else:
                # These should NOT commute: penalize if comm_norm is small
                # Use loss += alpha / (comm_norm_sq + eps)
                eps = 1e-6
                alpha = 0.1
                denom = comm_norm_sq + eps
                loss += alpha / denom

                # Gradient: d/dA [alpha / (||[A,B]||^2 + eps)]
                # = -alpha / (||[A,B]||^2 + eps)^2 * d/dA ||[A,B]||^2
                factor = -alpha / (denom ** 2)
                grad_A_comm = 2 * (comm @ B.T - B.T @ comm.T)
                gradients[i] += factor * grad_A_comm

                grad_B_comm = 2 * (A.T @ comm - comm.T @ A.T)
                gradients[j] += factor * grad_B_comm

    # Regularization: encourage non-trivial matrices
    for i, M in enumerate(matrices):
        norm_sq = np.sum(M ** 2)
        if norm_sq < 0.1:
            penalty = 100 * (0.1 - norm_sq) ** 2
            loss += penalty
            # Gradient: 200 * (0.1 - norm_sq) * (-2M) = -400 * (0.1 - norm_sq) * M
            gradients[i] += -400 * (0.1 - norm_sq) * M
        else:
            # Small L2 regularization to prevent unbounded growth
            loss += 0.001 * norm_sq
            gradients[i] += 0.002 * M

    return loss, gradients

def gradient_descent(n, k, max_iter=10000, lr=0.01, seed=0, verbose=False):
    """
    Run gradient descent to find matrices.

    Returns: (matrices, final_loss)
    """
    np.random.seed(seed)
    matrices = [np.random.randn(k, k) * 0.5 for _ in range(n)]

    best_loss = float('inf')
    best_matrices = [M.copy() for M in matrices]
    patience = 500
    no_improve = 0

    for iter in range(max_iter):
        loss, grads = objective_and_gradient(matrices, n, k)

        # Update matrices
        for i in range(n):
            matrices[i] -= lr * grads[i]

        # Track best
        if loss < best_loss:
            best_loss = loss
            best_matrices = [M.copy() for M in matrices]
            no_improve = 0
        else:
            no_improve += 1

        # Early stopping
        if no_improve > patience:
            if verbose:
                print(f"    Early stop at iter {iter}, loss={best_loss:.6f}")
            break

        # Adaptive learning rate
        if iter > 0 and iter % 1000 == 0:
            lr *= 0.9

        if verbose and iter % 1000 == 0:
            print(f"    Iter {iter}: loss={loss:.6f}")

    return best_matrices, best_loss

def check_solution(matrices, n, k, threshold=1e-3):
    """
    Check if matrices satisfy the commutativity pattern.

    Returns: (is_valid, max_error_commute, min_error_non_commute)
    """
    max_error_should_commute = 0.0
    min_error_should_not_commute = float('inf')

    for i in range(n):
        for j in range(i + 1, n):
            comm_norm = commutator_norm(matrices[i], matrices[j]) ** 0.5

            if cycle_should_commute(i, j, n):
                max_error_should_commute = max(max_error_should_commute, comm_norm)
            else:
                min_error_should_not_commute = min(min_error_should_not_commute, comm_norm)

    is_valid = (max_error_should_commute < threshold and
                min_error_should_not_commute > threshold)

    return is_valid, max_error_should_commute, min_error_should_not_commute

def find_cycle_matrices(n, k, max_attempts=30, max_iter=10000, verbose=False):
    """
    Find k×k matrices with C_n commutativity pattern.

    Returns: (matrices, max_err_comm, min_err_non) if found, None otherwise
    """
    best_loss = float('inf')
    best_matrices = None
    best_errors = None

    learning_rates = [0.01, 0.005, 0.02, 0.001]

    for attempt in range(max_attempts):
        lr = learning_rates[attempt % len(learning_rates)]

        if verbose and attempt % 5 == 0:
            print(f"  Attempt {attempt+1}/{max_attempts} (lr={lr})...", end="")

        matrices, loss = gradient_descent(n, k, max_iter=max_iter, lr=lr,
                                          seed=attempt * 1000 + n * 100 + k,
                                          verbose=False)

        # Check solution
        is_valid, max_err_comm, min_err_non = check_solution(matrices, n, k)

        if loss < best_loss:
            best_loss = loss
            best_matrices = matrices
            best_errors = (max_err_comm, min_err_non)

        if verbose and attempt % 5 == 0:
            print(f" loss={loss:.6f}, max_err={max_err_comm:.4f}, min_err={min_err_non:.4f}, valid={is_valid}")

        if is_valid:
            if verbose:
                print(f"  SUCCESS at attempt {attempt+1}!")
            return matrices, max_err_comm, min_err_non

    if verbose and best_matrices is not None:
        print(f"  Best: loss={best_loss:.6f}, max_err={best_errors[0]:.4f}, min_err={best_errors[1]:.4f}")

    return None

def search_minimum_dimension(n, max_k=12, verbose=True):
    """Search for minimum k for cycle C_n."""
    if verbose:
        print(f"\n{'='*70}")
        print(f"Searching for minimum dimension k for cycle C_{n}")
        print(f"{'='*70}")

    for k in range(2, max_k + 1):
        if verbose:
            print(f"\nTrying k = {k}...")

        result = find_cycle_matrices(n, k, max_attempts=40, max_iter=15000, verbose=verbose)

        if result is not None:
            matrices, max_err_comm, min_err_non = result

            if verbose:
                print(f"\n*** FOUND: C_{n} works with k = {k} ***")
                print(f"Max commutator error (should commute): {max_err_comm:.2e}")
                print(f"Min commutator error (should not commute): {min_err_non:.2e}")

            return k, matrices

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
                    print(f"A_{i}, A_{j} should COMMUTE:     ||[A_{i},A_{j}]|| = {comm_norm:.3e} [{status}]")
            else:
                status = "PASS" if comm_norm > 1e-2 else "FAIL"
                if comm_norm <= 1e-2:
                    all_good = False
                if verbose:
                    print(f"A_{i}, A_{j} should NOT commute: ||[A_{i},A_{j}]|| = {comm_norm:.3e} [{status}]")

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
        result = search_minimum_dimension(n, max_k=12, verbose=True)

        if result is not None:
            k, matrices = result
            results[n] = k

            # Verify
            verify_construction(matrices, n, verbose=False)
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
        print("-" * 70)
        print(f"{'n':<6} {'k':<6} {'sqrt(n)':<12} {'n/2':<10} {'ceil(n/2)':<12} {'floor(n/2)':<12}")
        print("-" * 70)

        for n, k in sorted(valid_results):
            sqrt_n = n ** 0.5
            n_half = n / 2
            ceil_half = (n + 1) // 2
            floor_half = n // 2

            print(f"{n:<6} {k:<6} {sqrt_n:<12.2f} {n_half:<10.1f} {ceil_half:<12} {floor_half:<12}")

        # Check if k = ceil(n/2)
        print("\n" + "-" * 70)
        pattern_ceil = all(k == (n + 1) // 2 for n, k in valid_results)
        pattern_floor = all(k == n // 2 for n, k in valid_results)

        if pattern_ceil:
            print("*** PATTERN FOUND: k = ceil(n/2) ***")
        elif pattern_floor:
            print("*** PATTERN FOUND: k = floor(n/2) ***")
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
