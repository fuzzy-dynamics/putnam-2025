#!/usr/bin/env python3
"""
Quick numerical test for small cycle graphs.
Simplified version with fewer iterations for faster results.
"""

import numpy as np

def cycle_should_commute(i, j, n):
    """Check if vertices i and j are adjacent in cycle C_n"""
    diff = abs(i - j)
    return diff == 1 or diff == n - 1

def commutator_norm(A, B):
    """Compute ||AB - BA||_F (Frobenius norm)"""
    comm = A @ B - B @ A
    return np.sum(comm ** 2) ** 0.5

def objective_and_gradient(matrices, n, k):
    """Compute objective function and gradients."""
    loss = 0.0
    gradients = [np.zeros((k, k)) for _ in range(n)]

    for i in range(n):
        for j in range(i + 1, n):
            A, B = matrices[i], matrices[j]
            comm = A @ B - B @ A
            comm_norm_sq = np.sum(comm ** 2)

            if cycle_should_commute(i, j, n):
                loss += comm_norm_sq
                grad_A = 2 * (comm @ B.T - B.T @ comm.T)
                gradients[i] += grad_A
                grad_B = 2 * (A.T @ comm - comm.T @ A.T)
                gradients[j] += grad_B
            else:
                eps = 1e-6
                alpha = 0.1
                denom = comm_norm_sq + eps
                loss += alpha / denom
                factor = -alpha / (denom ** 2)
                grad_A_comm = 2 * (comm @ B.T - B.T @ comm.T)
                gradients[i] += factor * grad_A_comm
                grad_B_comm = 2 * (A.T @ comm - comm.T @ A.T)
                gradients[j] += factor * grad_B_comm

    # Regularization
    for i, M in enumerate(matrices):
        norm_sq = np.sum(M ** 2)
        if norm_sq < 0.1:
            loss += 100 * (0.1 - norm_sq) ** 2
            gradients[i] += -400 * (0.1 - norm_sq) * M
        else:
            loss += 0.001 * norm_sq
            gradients[i] += 0.002 * M

    return loss, gradients

def gradient_descent(n, k, max_iter=5000, lr=0.01, seed=0):
    """Run gradient descent to find matrices."""
    np.random.seed(seed)
    matrices = [np.random.randn(k, k) * 0.5 for _ in range(n)]

    best_loss = float('inf')
    best_matrices = [M.copy() for M in matrices]
    patience = 300
    no_improve = 0

    for iter in range(max_iter):
        loss, grads = objective_and_gradient(matrices, n, k)

        for i in range(n):
            matrices[i] -= lr * grads[i]

        if loss < best_loss:
            best_loss = loss
            best_matrices = [M.copy() for M in matrices]
            no_improve = 0
        else:
            no_improve += 1

        if no_improve > patience:
            break

        if iter > 0 and iter % 1000 == 0:
            lr *= 0.9

    return best_matrices, best_loss

def check_solution(matrices, n, threshold=1e-3):
    """Check if matrices satisfy the commutativity pattern."""
    max_err_comm = 0.0
    min_err_non = float('inf')

    for i in range(n):
        for j in range(i + 1, n):
            comm_norm = commutator_norm(matrices[i], matrices[j])

            if cycle_should_commute(i, j, n):
                max_err_comm = max(max_err_comm, comm_norm)
            else:
                min_err_non = min(min_err_non, comm_norm)

    is_valid = (max_err_comm < threshold and min_err_non > threshold)
    return is_valid, max_err_comm, min_err_non

def find_cycle_matrices(n, k, max_attempts=20):
    """Find k×k matrices with C_n commutativity pattern."""
    best_loss = float('inf')
    best_result = None

    learning_rates = [0.01, 0.005, 0.02]

    for attempt in range(max_attempts):
        lr = learning_rates[attempt % len(learning_rates)]
        matrices, loss = gradient_descent(n, k, max_iter=5000, lr=lr,
                                          seed=attempt * 1000 + n * 100 + k)

        is_valid, max_err, min_err = check_solution(matrices, n)

        if loss < best_loss:
            best_loss = loss
            best_result = (matrices, max_err, min_err, is_valid)

        if is_valid:
            return matrices, max_err, min_err

    if best_result:
        return best_result[0], best_result[1], best_result[2]

    return None

def main():
    print("="*70)
    print("QUICK NUMERICAL TEST FOR CYCLE GRAPHS")
    print("="*70)

    results = {}

    for n in [4, 5, 6, 7, 8]:
        print(f"\n{'='*70}")
        print(f"Testing C_{n}")
        print(f"{'='*70}")

        for k in range(2, 10):
            print(f"  k={k}: ", end="", flush=True)

            result = find_cycle_matrices(n, k, max_attempts=25)

            if result is not None:
                matrices, max_err, min_err = result
                is_valid, _, _ = check_solution(matrices, n)

                if is_valid:
                    print(f"SUCCESS! max_err={max_err:.3e}, min_err={min_err:.3e}")
                    results[n] = k

                    # Show one verification
                    print(f"\n  Verification for C_{n} with k={k}:")
                    for i in range(n):
                        for j in range(i + 1, n):
                            comm_norm = commutator_norm(matrices[i], matrices[j])
                            should_comm = cycle_should_commute(i, j, n)
                            status = "✓" if (should_comm and comm_norm < 1e-3) or (not should_comm and comm_norm > 1e-3) else "✗"
                            comm_str = "COMM" if should_comm else "NON"
                            print(f"    [{status}] A_{i}, A_{j}: {comm_str}, ||[A_{i},A_{j}]||={comm_norm:.3e}")
                    break
                else:
                    print(f"close (max_err={max_err:.3e}, min_err={min_err:.3e})")
            else:
                print("failed")

        if n not in results:
            print(f"  No valid construction found for C_{n}")

    # Summary
    print("\n" + "="*70)
    print("SUMMARY")
    print("="*70)

    valid_results = [(n, k) for n, k in sorted(results.items())]

    if valid_results:
        print("\nMinimum dimension k:")
        print("-" * 40)
        for n, k in valid_results:
            print(f"  C_{n}: k = {k}")

        print("\n" + "="*70)
        print("PATTERN ANALYSIS")
        print("="*70)

        print("\nComparison:")
        print(f"{'n':<6} {'k':<6} {'sqrt(n)':<12} {'n/2':<10} {'ceil(n/2)':<12}")
        print("-" * 50)

        for n, k in valid_results:
            sqrt_n = n ** 0.5
            n_half = n / 2
            ceil_half = (n + 1) // 2

            print(f"{n:<6} {k:<6} {sqrt_n:<12.2f} {n_half:<10.1f} {ceil_half:<12}")

        pattern_ceil = all(k == (n + 1) // 2 for n, k in valid_results)

        print("\n" + "-" * 50)
        if pattern_ceil:
            print("PATTERN: k = ceil(n/2) = (n+1)//2")
        else:
            print("Pattern unclear, need more data")

if __name__ == "__main__":
    main()
