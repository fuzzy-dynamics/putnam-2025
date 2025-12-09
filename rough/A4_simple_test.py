#!/usr/bin/env python3
"""
Simple numerical test for A4: Does k = sqrt(n) work for perfect squares?
"""

import numpy as np

def create_shift_matrix(k):
    """Cyclic shift matrix."""
    X = np.zeros((k, k), dtype=complex)
    for i in range(k):
        X[i, (i + 1) % k] = 1
    return X

def create_clock_matrix(k):
    """Clock matrix with phases."""
    omega = np.exp(2j * np.pi / k)
    return np.diag([omega**j for j in range(k)])

def test_config(n, k):
    """Test if dimension k works for n matrices."""
    print(f"\nTesting n={n}, k={k} (sqrt(n)={np.sqrt(n):.1f})")

    # Create Weyl matrices
    X = create_shift_matrix(k)
    Z = create_clock_matrix(k)

    # Verify Weyl relation: XZ = ω ZX
    omega = np.exp(2j * np.pi / k)
    weyl_error = np.linalg.norm(X @ Z - omega * Z @ X)
    print(f"  Weyl relation error: {weyl_error:.2e}")

    # Create matrices A_i = X^a Z^b
    matrices = []
    for i in range(n):
        a = i // k
        b = i % k
        A_i = np.linalg.matrix_power(X, a) @ np.linalg.matrix_power(Z, b)
        matrices.append(A_i)

    # Check commutativity pattern
    def is_adjacent(i, j):
        diff = abs(i - j)
        return diff == 1 or diff == n - 1

    violations_commute = 0
    violations_not_commute = 0
    max_should_commute = 0.0
    min_should_not_commute = float('inf')

    for i in range(n):
        for j in range(i + 1, n):
            comm = matrices[i] @ matrices[j] - matrices[j] @ matrices[i]
            comm_norm = np.linalg.norm(comm)

            if is_adjacent(i, j):
                max_should_commute = max(max_should_commute, comm_norm)
                if comm_norm > 1e-6:
                    violations_commute += 1
            else:
                min_should_not_commute = min(min_should_not_commute, comm_norm)
                if comm_norm < 1e-6:
                    violations_not_commute += 1

    print(f"  Max error (should commute): {max_should_commute:.2e}")
    print(f"  Min value (should NOT commute): {min_should_not_commute:.2e}")
    print(f"  Violations (should commute): {violations_commute}")
    print(f"  Violations (should NOT commute): {violations_not_commute}")

    success = (violations_commute == 0 and violations_not_commute == 0)
    print(f"  Result: {'SUCCESS' if success else 'FAILED'}")

    return success

# Test perfect squares
print("="*60)
print("Testing k = sqrt(n) for perfect squares")
print("="*60)

results = []
for n in [4, 9, 16, 25, 36, 49, 64, 81, 100, 121, 144, 169, 196, 225]:
    k = int(np.sqrt(n))
    success = test_config(n, k)
    results.append((n, k, success))

# Test n=2025, k=45
print("\n" + "="*60)
print("FINAL TEST: n=2025, k=45")
print("="*60)
success_2025 = test_config(2025, 45)

# Summary
print("\n" + "="*60)
print("SUMMARY")
print("="*60)
print(f"{'n':>6} | {'k':>6} | {'Success':>8}")
print("-" * 60)
for n, k, success in results:
    print(f"{n:6d} | {k:6d} | {'YES' if success else 'NO':>8}")

print(f"\nn=2025, k=45: {'SUCCESS' if success_2025 else 'FAILED'}")
