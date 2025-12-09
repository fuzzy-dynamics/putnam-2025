#!/usr/bin/env python3
"""
Numerical search for ACTUAL minimum k using random matrix optimization.

Use much simpler approach: just try random matrices and optimize.
"""

import numpy as np
import time

def cycle_commute(i, j, n):
    """Should i and j commute in cycle C_n?"""
    diff = abs(i - j)
    return diff == 0 or diff == 1 or diff == n - 1

def test_random_matrices(n, k, num_trials=10, num_iters=500):
    """
    Generate random k x k matrices and try to optimize them.
    Returns best score achieved.
    """
    print(f"Testing n={n}, k={k}...")

    best_score = -float('inf')

    for trial in range(num_trials):
        # Random initialization
        matrices = [np.random.randn(k, k) for _ in range(n)]

        # Simple gradient descent
        lr = 0.01

        for it in range(num_iters):
            # Compute gradients
            grads = [np.zeros((k, k)) for _ in range(n)]

            for i in range(n):
                for j in range(n):
                    if i == j:
                        continue

                    should_commute = cycle_commute(i, j, n)
                    comm = matrices[i] @ matrices[j] - matrices[j] @ matrices[i]

                    if should_commute:
                        # Minimize ||[A_i, A_j]||^2
                        # Gradient: 2[A_i,A_j]A_j^T - 2A_j[A_i,A_j]^T
                        grads[i] += 2 * (comm @ matrices[j].T - matrices[j] @ comm.T)
                    else:
                        # Maximize ||[A_i, A_j]||^2 (minimize negative)
                        comm_norm = np.linalg.norm(comm)
                        if comm_norm < 0.1:  # Only push if too small
                            grads[i] -= 2 * (comm @ matrices[j].T - matrices[j] @ comm.T)

            # Update
            for i in range(n):
                matrices[i] -= lr * grads[i]

            if it % 100 == 0:
                lr *= 0.8  # Decay learning rate

        # Evaluate final score
        score = 0
        max_should_commute = 0
        min_should_not = float('inf')

        for i in range(n):
            for j in range(i + 1, n):
                comm_norm = np.linalg.norm(matrices[i] @ matrices[j] - matrices[j] @ matrices[i])

                if cycle_commute(i, j, n):
                    score -= comm_norm  # Want this small
                    max_should_commute = max(max_should_commute, comm_norm)
                else:
                    score += min(comm_norm, 0.5)  # Want this large
                    min_should_not = min(min_should_not, comm_norm)

        best_score = max(best_score, score)

        if trial == 0 or score > best_score * 0.9:
            print(f"  Trial {trial}: score={score:.2f}, "
                  f"max_commute={max_should_commute:.4f}, "
                  f"min_non_commute={min_should_not:.4f}")

    # Success if max_should_commute < 0.01 and min_should_not > 0.05
    max_should_commute = 0
    min_should_not = float('inf')
    for i in range(n):
        for j in range(i + 1, n):
            comm_norm = np.linalg.norm(matrices[i] @ matrices[j] - matrices[j] @ matrices[i])
            if cycle_commute(i, j, n):
                max_should_commute = max(max_should_commute, comm_norm)
            else:
                min_should_not = min(min_should_not, comm_norm)

    success = max_should_commute < 0.01 and min_should_not > 0.05

    print(f"  Best score: {best_score:.2f}")
    print(f"  Success: {success}\n")

    return success, best_score

# Quick tests on small n
print("="*60)
print("NUMERICAL SEARCH FOR MINIMUM k")
print("="*60)

test_cases = [
    (5, [2, 3, 4]),
    (6, [2, 3, 4]),
    (7, [2, 3, 4]),
    (8, [2, 3, 4]),
    (9, [3, 4, 5]),
    (10, [3, 4, 5]),
    (12, [3, 4, 5]),
    (15, [3, 4, 5]),
    (16, [4, 5, 6]),
    (20, [4, 5, 6]),
    (25, [5, 6, 7]),
]

results = []
for n, k_values in test_cases:
    print(f"\nTesting n={n}:")
    min_k = None
    for k in k_values:
        success, score = test_random_matrices(n, k, num_trials=5, num_iters=300)
        if success:
            min_k = k
            break

    results.append((n, min_k))
    print(f">>> n={n}: minimum k = {min_k}")

# Summary
print("\n" + "="*60)
print("RESULTS")
print("="*60)
print(f"{'n':>6} | {'sqrt(n)':>8} | {'min_k':>6} | {'k/sqrt(n)':>10}")
print("-" * 60)

for n, min_k in results:
    sqrt_n = np.sqrt(n)
    if min_k:
        ratio = min_k / sqrt_n
        print(f"{n:6d} | {sqrt_n:8.2f} | {min_k:6d} | {ratio:10.3f}")
    else:
        print(f"{n:6d} | {sqrt_n:8.2f} | {'?':>6} | {'?':>10}")

print("\nNote: This is a heuristic search. True minimum may be lower.")
print("Need more sophisticated optimization or algebraic construction.")
