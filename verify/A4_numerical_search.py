#!/usr/bin/env python3
"""
Numerical search for minimum k as a function of n for Putnam 2025 A4.

For cycle C_n, we need k x k real matrices A_1, ..., A_n such that:
A_i and A_j commute iff |i-j| ∈ {0, 1, n-1} (adjacent in cycle)

We test various k values for different n to determine the growth pattern.
"""

import numpy as np
from typing import List, Tuple, Optional
import time

class CycleCommutatorSolver:
    """Find matrices for the cycle commutativity pattern."""

    def __init__(self, n: int, k: int, seed: int = 42):
        self.n = n  # Number of matrices (cycle size)
        self.k = k  # Matrix dimension
        self.seed = seed
        np.random.seed(seed)

    def is_adjacent(self, i: int, j: int) -> bool:
        """Check if i and j are adjacent in cycle C_n."""
        diff = abs(i - j)
        return diff == 1 or diff == self.n - 1

    def commutator_norm(self, A: np.ndarray, B: np.ndarray) -> float:
        """Compute ||AB - BA||_F (Frobenius norm of commutator)."""
        return np.linalg.norm(A @ B - B @ A, 'fro')

    def objective(self, matrices: List[np.ndarray]) -> Tuple[float, dict]:
        """
        Compute objective function and diagnostics.

        Returns:
            total_error: sum of violations
            diagnostics: dict with breakdown
        """
        should_commute_error = 0.0
        should_not_commute_error = 0.0

        should_commute_count = 0
        should_not_commute_count = 0

        should_commute_violations = []
        should_not_commute_violations = []

        for i in range(self.n):
            for j in range(i + 1, self.n):
                comm_norm = self.commutator_norm(matrices[i], matrices[j])

                if self.is_adjacent(i, j):
                    # Should commute
                    should_commute_error += comm_norm
                    should_commute_count += 1
                    if comm_norm > 1e-3:
                        should_commute_violations.append((i, j, comm_norm))
                else:
                    # Should NOT commute - we want large commutator
                    # Penalize if commutator is small
                    penalty = max(0, 0.1 - comm_norm)  # Penalize if < 0.1
                    should_not_commute_error += penalty
                    should_not_commute_count += 1
                    if comm_norm < 0.05:
                        should_not_commute_violations.append((i, j, comm_norm))

        diagnostics = {
            'should_commute_error': should_commute_error,
            'should_not_commute_error': should_not_commute_error,
            'should_commute_count': should_commute_count,
            'should_not_commute_count': should_not_commute_count,
            'should_commute_violations': should_commute_violations[:10],
            'should_not_commute_violations': should_not_commute_violations[:10],
        }

        # Total error: heavily weight both types of violations
        total_error = should_commute_error + 10.0 * should_not_commute_error

        return total_error, diagnostics

    def initialize_matrices(self, method: str = 'orthogonal') -> List[np.ndarray]:
        """Initialize matrices using different strategies."""
        matrices = []

        if method == 'orthogonal':
            # Start with random orthogonal matrices
            for _ in range(self.n):
                A = np.random.randn(self.k, self.k)
                Q, R = np.linalg.qr(A)
                matrices.append(Q)

        elif method == 'symmetric':
            # Random symmetric matrices
            for _ in range(self.n):
                A = np.random.randn(self.k, self.k)
                matrices.append((A + A.T) / 2)

        elif method == 'structured':
            # Use structured initialization based on cycle position
            for i in range(self.n):
                angle = 2 * np.pi * i / self.n
                # Mix rotation-like and diagonal structures
                A = np.zeros((self.k, self.k))
                for j in range(min(2, self.k - 1)):
                    # Create small rotation blocks
                    theta = angle + j * np.pi / 4
                    if j * 2 + 1 < self.k:
                        A[j*2, j*2] = np.cos(theta)
                        A[j*2, j*2+1] = -np.sin(theta)
                        A[j*2+1, j*2] = np.sin(theta)
                        A[j*2+1, j*2+1] = np.cos(theta)
                # Fill diagonal
                for j in range(4, self.k):
                    A[j, j] = np.cos(angle * (j + 1))
                matrices.append(A)
        else:
            # Random
            for _ in range(self.n):
                matrices.append(np.random.randn(self.k, self.k))

        return matrices

    def gradient_step(self, matrices: List[np.ndarray], lr: float = 0.01) -> List[np.ndarray]:
        """Perform one gradient descent step."""
        gradients = [np.zeros((self.k, self.k)) for _ in range(self.n)]

        for i in range(self.n):
            for j in range(self.n):
                if i == j:
                    continue

                A_i = matrices[i]
                A_j = matrices[j]
                comm = A_i @ A_j - A_j @ A_i

                if self.is_adjacent(i, j):
                    # Should commute: minimize ||[A_i, A_j]||^2
                    # grad_{A_i} ||[A_i,A_j]||^2 = 2[A_i,A_j]A_j^T - 2A_j[A_i,A_j]^T
                    gradients[i] += 2 * (comm @ A_j.T - A_j @ comm.T)
                else:
                    # Should NOT commute: maximize ||[A_i, A_j]||^2 (or penalize if too small)
                    comm_norm = np.linalg.norm(comm, 'fro')
                    if comm_norm < 0.1:
                        # Gradient to increase commutator norm
                        gradients[i] -= 20 * (comm @ A_j.T - A_j @ comm.T)

        # Update with gradient descent
        new_matrices = []
        for i in range(self.n):
            new_matrices.append(matrices[i] - lr * gradients[i])

        return new_matrices

    def optimize(self, max_iters: int = 1000, lr: float = 0.001,
                 init_method: str = 'orthogonal', verbose: bool = True) -> Tuple[List[np.ndarray], float]:
        """Run optimization to find matrices."""
        matrices = self.initialize_matrices(init_method)

        best_matrices = matrices
        best_error = float('inf')

        for iter_num in range(max_iters):
            error, diagnostics = self.objective(matrices)

            if error < best_error:
                best_error = error
                best_matrices = [A.copy() for A in matrices]

            if verbose and (iter_num % 100 == 0 or iter_num < 10):
                print(f"Iter {iter_num}: error={error:.6f}, "
                      f"commute_err={diagnostics['should_commute_error']:.6f}, "
                      f"non_commute_err={diagnostics['should_not_commute_error']:.6f}")

            # Check convergence
            if error < 1e-6:
                if verbose:
                    print(f"Converged at iteration {iter_num}")
                break

            # Gradient step
            matrices = self.gradient_step(matrices, lr)

            # Adaptive learning rate
            if iter_num > 0 and iter_num % 200 == 0:
                lr *= 0.5

        return best_matrices, best_error

    def verify_solution(self, matrices: List[np.ndarray], threshold: float = 1e-2) -> Tuple[bool, dict]:
        """Verify if matrices satisfy the commutativity pattern."""
        error, diagnostics = self.objective(matrices)

        # Check if all should-commute pairs actually commute
        max_should_commute = 0.0
        for i in range(self.n):
            for j in range(i + 1, self.n):
                if self.is_adjacent(i, j):
                    comm_norm = self.commutator_norm(matrices[i], matrices[j])
                    max_should_commute = max(max_should_commute, comm_norm)

        # Check if all should-not-commute pairs actually don't commute
        min_should_not_commute = float('inf')
        for i in range(self.n):
            for j in range(i + 1, self.n):
                if not self.is_adjacent(i, j):
                    comm_norm = self.commutator_norm(matrices[i], matrices[j])
                    min_should_not_commute = min(min_should_not_commute, comm_norm)

        success = (max_should_commute < threshold and min_should_not_commute > threshold / 2)

        result = {
            'success': success,
            'max_should_commute': max_should_commute,
            'min_should_not_commute': min_should_not_commute,
            'total_error': error,
            **diagnostics
        }

        return success, result


def test_single_config(n: int, k: int, max_iters: int = 500, num_trials: int = 3) -> Tuple[bool, dict]:
    """Test if k works for cycle C_n with multiple random initializations."""
    print(f"\n{'='*60}")
    print(f"Testing n={n}, k={k}")
    print(f"{'='*60}")

    best_result = None
    best_success = False

    for trial in range(num_trials):
        print(f"\n--- Trial {trial + 1}/{num_trials} ---")
        solver = CycleCommutatorSolver(n, k, seed=42 + trial)

        # Try different initialization methods
        for init_method in ['structured', 'orthogonal']:
            print(f"\nInitialization: {init_method}")
            matrices, error = solver.optimize(max_iters=max_iters, lr=0.001,
                                             init_method=init_method, verbose=False)
            success, result = solver.verify_solution(matrices)

            print(f"Final error: {error:.6f}")
            print(f"Max commute error: {result['max_should_commute']:.6f}")
            print(f"Min non-commute: {result['min_should_not_commute']:.6f}")
            print(f"Success: {success}")

            if success or (best_result is None) or (error < best_result['total_error']):
                best_result = result
                best_success = success

            if success:
                print(f"✓ SUCCESS: k={k} works for n={n}")
                return True, result

    if best_success:
        print(f"✓ SUCCESS: k={k} works for n={n}")
    else:
        print(f"✗ FAILED: k={k} does not work for n={n} (best error: {best_result['total_error']:.6f})")

    return best_success, best_result


def find_minimum_k(n: int, k_values: List[int], max_iters: int = 500) -> Optional[int]:
    """Binary search to find minimum k that works for cycle C_n."""
    print(f"\n{'#'*60}")
    print(f"# Finding minimum k for n={n}")
    print(f"{'#'*60}")

    results = {}

    for k in sorted(k_values):
        if k < int(np.sqrt(n)) - 2:
            # Skip values that are too small based on theoretical lower bound
            print(f"\nSkipping k={k} (below theoretical lower bound ~√n = {np.sqrt(n):.1f})")
            continue

        success, result = test_single_config(n, k, max_iters=max_iters, num_trials=2)
        results[k] = (success, result)

        if success:
            print(f"\n>>> Found minimum k={k} for n={n}")
            return k

    print(f"\n>>> No k in {k_values} works for n={n}")
    return None


def main():
    """Systematic search for minimum k across different n values."""
    print("="*70)
    print("PUTNAM 2025 A4 - NUMERICAL SEARCH FOR MINIMUM k")
    print("="*70)

    # Test configurations
    test_cases = [
        (25, [4, 5, 6, 7]),
        (49, [6, 7, 8, 9]),
        (64, [7, 8, 9, 10]),
        (81, [8, 9, 10, 11]),
        (100, [9, 10, 11, 12, 15]),
        (121, [10, 11, 12, 13]),
        (144, [11, 12, 13, 14]),
        (169, [12, 13, 14, 15]),
        (196, [13, 14, 15, 16]),
        (225, [14, 15, 16, 17]),
    ]

    results_table = []

    for n, k_values in test_cases:
        min_k = find_minimum_k(n, k_values, max_iters=300)
        results_table.append((n, min_k))

    # Print summary
    print("\n" + "="*70)
    print("SUMMARY: Minimum k for each n")
    print("="*70)
    print(f"{'n':>6} | {'√n':>8} | {'min_k':>6} | {'k/√n':>8}")
    print("-" * 70)

    for n, min_k in results_table:
        sqrt_n = np.sqrt(n)
        if min_k is not None:
            ratio = min_k / sqrt_n
            print(f"{n:6d} | {sqrt_n:8.2f} | {min_k:6d} | {ratio:8.3f}")
        else:
            print(f"{n:6d} | {sqrt_n:8.2f} | {'None':>6} | {'N/A':>8}")

    # Extrapolate to n=2025
    print("\n" + "="*70)
    print("EXTRAPOLATION TO n=2025")
    print("="*70)

    # Filter successful results
    successful = [(n, k) for n, k in results_table if k is not None]

    if successful:
        # Check if k ≈ √n pattern holds
        print(f"\n√2025 = {np.sqrt(2025)}")
        print(f"Prediction: k = {int(np.sqrt(2025))}")

        # Check if it's exactly √n for perfect squares
        perfect_squares = [(n, k) for n, k in successful if int(np.sqrt(n))**2 == n]
        if perfect_squares:
            print(f"\nPerfect squares found:")
            for n, k in perfect_squares:
                print(f"  n={n}, k={k}, √n={int(np.sqrt(n))}, k==√n: {k == int(np.sqrt(n))}")


if __name__ == "__main__":
    # Quick test first
    print("Quick verification test: n=25, k=5")
    success, result = test_single_config(25, 5, max_iters=200, num_trials=1)

    if success:
        print("\n✓ Quick test passed, proceeding with full search...\n")
        time.sleep(2)
        main()
    else:
        print("\n⚠ Quick test showed difficulty - may need more iterations or different approach")
        print("Proceeding anyway with smaller test set...\n")

        # Smaller test set
        test_cases = [
            (16, [4, 5]),
            (25, [5, 6]),
            (36, [6, 7]),
            (49, [7, 8]),
            (64, [8, 9]),
        ]

        results_table = []
        for n, k_values in test_cases:
            min_k = find_minimum_k(n, k_values, max_iters=500)
            results_table.append((n, min_k))

        print("\n" + "="*70)
        print("SUMMARY")
        print("="*70)
        print(f"{'n':>6} | {'√n':>8} | {'min_k':>6}")
        print("-" * 70)
        for n, min_k in results_table:
            sqrt_n = np.sqrt(n)
            print(f"{n:6d} | {sqrt_n:8.2f} | {min_k if min_k else 'None':>6}")
