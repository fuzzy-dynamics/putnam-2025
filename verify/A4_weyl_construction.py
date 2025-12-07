#!/usr/bin/env python3
"""
Test the Weyl matrix construction for Putnam 2025 A4.

Based on the theoretical solution, we use Weyl matrices (shift and clock)
to construct matrices with the correct commutativity pattern.
"""

import numpy as np
from typing import List, Tuple

def create_shift_matrix(k: int) -> np.ndarray:
    """Create k x k cyclic shift matrix X."""
    X = np.zeros((k, k), dtype=complex)
    for i in range(k):
        X[i, (i + 1) % k] = 1
    return X

def create_clock_matrix(k: int) -> np.ndarray:
    """Create k x k clock matrix Z with phases."""
    omega = np.exp(2j * np.pi / k)
    Z = np.diag([omega**j for j in range(k)])
    return Z

def verify_weyl_relation(X: np.ndarray, Z: np.ndarray, k: int) -> bool:
    """Verify that XZ = ω ZX where ω = e^(2πi/k)."""
    omega = np.exp(2j * np.pi / k)
    XZ = X @ Z
    ZX_scaled = omega * Z @ X

    error = np.linalg.norm(XZ - ZX_scaled, 'fro')
    print(f"Weyl relation error: {error:.6e}")
    return error < 1e-10

def create_cycle_matrices_weyl(n: int, k: int) -> List[np.ndarray]:
    """
    Create n matrices using Weyl construction.

    For n matrices and dimension k, we use:
    A_i = X^a Z^b where (a,b) is derived from index i.

    The key is that for n = k^2, we can use a k x k grid indexing.
    """
    if k * k != n:
        print(f"Warning: n={n} is not k^2={k**2}. Using modular indexing.")

    X = create_shift_matrix(k)
    Z = create_clock_matrix(k)

    # Verify Weyl relation
    verify_weyl_relation(X, Z, k)

    matrices = []
    for i in range(n):
        # Map i to (a, b) coordinates
        a = i // k
        b = i % k

        # A_i = X^a Z^b
        # Compute powers efficiently
        X_power_a = np.linalg.matrix_power(X, a % k)
        Z_power_b = np.linalg.matrix_power(Z, b % k)

        A_i = X_power_a @ Z_power_b
        matrices.append(A_i)

    return matrices

def check_commutativity_pattern(matrices: List[np.ndarray], n: int, threshold: float = 1e-6) -> dict:
    """Check if matrices satisfy the cycle commutativity pattern."""

    def is_adjacent(i: int, j: int) -> bool:
        diff = abs(i - j)
        return diff == 1 or diff == n - 1

    def commutator_norm(A: np.ndarray, B: np.ndarray) -> float:
        return np.linalg.norm(A @ B - B @ A, 'fro')

    results = {
        'should_commute': [],
        'should_not_commute': [],
        'violations_commute': [],
        'violations_not_commute': [],
    }

    max_should_commute = 0.0
    min_should_not_commute = float('inf')

    for i in range(n):
        for j in range(i + 1, n):
            comm_norm = commutator_norm(matrices[i], matrices[j])

            if is_adjacent(i, j):
                results['should_commute'].append((i, j, comm_norm))
                max_should_commute = max(max_should_commute, comm_norm)
                if comm_norm > threshold:
                    results['violations_commute'].append((i, j, comm_norm))
            else:
                results['should_not_commute'].append((i, j, comm_norm))
                min_should_not_commute = min(min_should_not_commute, comm_norm)
                if comm_norm < threshold:
                    results['violations_not_commute'].append((i, j, comm_norm))

    results['max_should_commute'] = max_should_commute
    results['min_should_not_commute'] = min_should_not_commute
    results['success'] = (max_should_commute < threshold and min_should_not_commute > threshold)

    return results

def test_weyl_construction(n: int, k: int):
    """Test if Weyl construction with dimension k works for cycle C_n."""
    print(f"\n{'='*70}")
    print(f"Testing Weyl construction: n={n}, k={k}")
    print(f"{'='*70}")

    matrices = create_cycle_matrices_weyl(n, k)

    print(f"\nCreated {len(matrices)} matrices of dimension {k}x{k}")

    # Check pattern
    results = check_commutativity_pattern(matrices, n)

    print(f"\nResults:")
    print(f"  Pairs that should commute: {len(results['should_commute'])}")
    print(f"  Pairs that should NOT commute: {len(results['should_not_commute'])}")
    print(f"  Max commutator (should commute): {results['max_should_commute']:.6e}")
    print(f"  Min commutator (should NOT commute): {results['min_should_not_commute']:.6e}")

    if results['violations_commute']:
        print(f"\n  ⚠ Violations (should commute but don't): {len(results['violations_commute'])}")
        for i, j, norm in results['violations_commute'][:5]:
            print(f"    ({i}, {j}): {norm:.6e}")

    if results['violations_not_commute']:
        print(f"\n  ⚠ Violations (should NOT commute but do): {len(results['violations_not_commute'])}")
        for i, j, norm in results['violations_not_commute'][:5]:
            print(f"    ({i}, {j}): {norm:.6e}")

    if results['success']:
        print(f"\n✓ SUCCESS: Weyl construction with k={k} works for n={n}")
    else:
        print(f"\n✗ FAILED: Weyl construction with k={k} does not work for n={n}")

    return results['success']

def analyze_commutation_weyl(n: int, k: int):
    """
    Analyze the commutation structure of Weyl matrices.

    For A_i = X^a Z^b and A_j = X^c Z^d:
    [A_i, A_j] = X^a Z^b X^c Z^d - X^c Z^d X^a Z^b

    Using XZ = ω ZX where ω = e^(2πi/k):
    X^a Z^b = ω^(ab) Z^b X^a (needs careful calculation)
    """
    print(f"\n{'='*70}")
    print(f"Analyzing Weyl commutation structure: n={n}, k={k}")
    print(f"{'='*70}")

    omega = np.exp(2j * np.pi / k)

    def index_to_coords(i):
        return i // k, i % k

    def is_adjacent(i: int, j: int) -> bool:
        diff = abs(i - j)
        return diff == 1 or diff == n - 1

    # Analyze a few pairs
    test_pairs = [
        (0, 1),  # Adjacent (should commute)
        (0, n-1),  # Adjacent via wraparound (should commute)
        (0, 2),  # Not adjacent (should NOT commute)
        (0, k),  # Not adjacent (should NOT commute)
    ]

    print("\nAnalyzing specific pairs:")
    for i, j in test_pairs:
        if i >= n or j >= n:
            continue

        a, b = index_to_coords(i)
        c, d = index_to_coords(j)

        adjacent = is_adjacent(i, j)

        # Key: X^a Z^b X^c Z^d = ω^(bc) X^(a+c) Z^(b+d)
        # And: X^c Z^d X^a Z^b = ω^(ad) X^(a+c) Z^(b+d)
        # They commute iff bc ≡ ad (mod k)

        bc_mod = (b * c) % k
        ad_mod = (a * d) % k

        commute_condition = (bc_mod == ad_mod)

        print(f"\n  Pair ({i}, {j}): a={a}, b={b}, c={c}, d={d}")
        print(f"    Adjacent in cycle: {adjacent}")
        print(f"    bc mod k = {bc_mod}, ad mod k = {ad_mod}")
        print(f"    Weyl commutation: {commute_condition}")
        print(f"    Match: {'✓' if adjacent == commute_condition else '✗'}")

def main():
    print("="*70)
    print("PUTNAM 2025 A4 - WEYL MATRIX CONSTRUCTION TEST")
    print("="*70)

    # Test perfect squares where n = k^2
    perfect_square_tests = [
        (4, 2),
        (9, 3),
        (16, 4),
        (25, 5),
        (36, 6),
        (49, 7),
        (64, 8),
        (81, 9),
        (100, 10),
        (121, 11),
        (144, 12),
        (169, 13),
        (196, 14),
        (225, 15),
    ]

    print("\nTesting perfect squares (n = k^2):")
    print("-" * 70)

    results = []
    for n, k in perfect_square_tests:
        success = test_weyl_construction(n, k)
        results.append((n, k, success))

    # Analyze why it might not work
    print("\n" + "="*70)
    print("DETAILED ANALYSIS: Why Weyl construction may not match cycle")
    print("="*70)

    analyze_commutation_weyl(25, 5)
    analyze_commutation_weyl(49, 7)

    # Summary
    print("\n" + "="*70)
    print("SUMMARY")
    print("="*70)
    print(f"{'n':>6} | {'k':>6} | {'k^2':>6} | {'Success':>8}")
    print("-" * 70)
    for n, k, success in results:
        print(f"{n:6d} | {k:6d} | {k*k:6d} | {'✓' if success else '✗':>8}")

    # Test n=2025 with k=45
    print("\n" + "="*70)
    print("FINAL TEST: n=2025, k=45")
    print("="*70)
    test_weyl_construction(2025, 45)

if __name__ == "__main__":
    main()
