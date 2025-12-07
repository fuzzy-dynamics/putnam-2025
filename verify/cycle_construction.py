#!/usr/bin/env python3
"""
Construct matrices for cycle graphs using theoretical approach.

For cycle C_n, we can try several constructions:
1. Circulant-like constructions
2. Block diagonal with rotations
3. Shift matrices with polynomial structure
"""

import numpy as np

def cycle_should_commute(i, j, n):
    """Check if vertices i and j are adjacent in cycle C_n"""
    diff = abs(i - j)
    return diff == 1 or diff == n - 1

def commutator_norm(A, B):
    """Compute ||AB - BA||_F (Frobenius norm)"""
    comm = A @ B - B @ A
    return np.linalg.norm(comm, 'fro')

def verify_cycle_construction(matrices, n, name=""):
    """Verify if matrices form a valid C_n construction"""
    print(f"\nVerifying {name} for C_{n}:")
    print("=" * 60)

    k = matrices[0].shape[0]
    all_good = True

    for i in range(n):
        for j in range(i + 1, n):
            comm_norm = commutator_norm(matrices[i], matrices[j])
            should_comm = cycle_should_commute(i, j, n)

            if should_comm:
                status = "PASS" if comm_norm < 1e-8 else "FAIL"
                if comm_norm >= 1e-8:
                    all_good = False
                print(f"  A_{i}, A_{j} should COMMUTE:     ||[A_{i},A_{j}]|| = {comm_norm:.3e} [{status}]")
            else:
                status = "PASS" if comm_norm > 1e-8 else "FAIL"
                if comm_norm <= 1e-8:
                    all_good = False
                print(f"  A_{i}, A_{j} should NOT commute: ||[A_{i},A_{j}]|| = {comm_norm:.3e} [{status}]")

    print("=" * 60)
    print(f"Result: {'VALID' if all_good else 'INVALID'}")
    print(f"Dimension k = {k}")

    return all_good

def construct_cycle_shift_method(n):
    """
    Construction using shift matrices.

    For C_n, use k = ceil(n/2).
    Idea: A_i is a "position" matrix that encodes vertex i's location.
    """
    k = (n + 1) // 2  # ceil(n/2)

    # Create matrices where A_i and A_{i+1} commute
    matrices = []

    # Try polynomial construction
    # A_i = sum_{j=0}^{k-1} a_{i,j} * S^j where S is shift matrix
    S = np.zeros((k, k))
    for i in range(k - 1):
        S[i, i + 1] = 1
    S[k - 1, 0] = 1  # Cyclic shift

    for i in range(n):
        # Create matrix for vertex i
        # Use angle theta_i = 2*pi*i/n
        theta = 2 * np.pi * i / n

        # Construct using Fourier-like basis
        A = np.zeros((k, k), dtype=complex)

        for m in range(min(k, (n + 1) // 2)):
            omega = np.exp(2j * np.pi * m / k)
            coeff = np.exp(1j * m * theta)

            # Add component
            for p in range(k):
                A[p, p] += coeff * (omega ** p)

        # Make it real by taking appropriate combination
        A = np.real(A)

        matrices.append(A)

    return matrices, k

def construct_cycle_diagonal_method(n):
    """
    Diagonal method: Use k = n/2 for even n.

    For each vertex i, create a diagonal matrix with specific pattern.
    """
    if n % 2 != 0:
        return None, None

    k = n // 2
    matrices = []

    for i in range(n):
        # Create diagonal matrix
        theta = 2 * np.pi * i / n
        A = np.zeros((k, k))

        for j in range(k):
            # Use cos and sin patterns
            A[j, j] = np.cos(theta + j * np.pi / k)

        matrices.append(A)

    return matrices, k

def construct_cycle_block_method(n):
    """
    Block construction for specific cases.
    """
    if n == 4:
        # For C_4, try k=2
        # A_0, A_1, A_2, A_3 where A_i and A_{i+1 mod 4} commute
        # Use Pauli-like matrices
        I = np.eye(2)
        X = np.array([[0, 1], [1, 0]])
        Y = np.array([[0, -1j], [1j, 0]])
        Z = np.array([[1, 0], [0, -1]])

        # Try: A_0 = X, A_1 = I, A_2 = X, A_3 = I (no, this won't work)
        # Better: use rotation matrices

        angles = [0, np.pi/4, np.pi/2, 3*np.pi/4]
        matrices = []

        for theta in angles:
            R = np.array([[np.cos(theta), -np.sin(theta)],
                         [np.sin(theta), np.cos(theta)]])
            matrices.append(R)

        return matrices, 2

    elif n == 5:
        # For C_5, try k=3
        angles = [2*np.pi*i/5 for i in range(5)]
        matrices = []

        for theta in angles:
            # 3x3 rotation-like matrix
            A = np.array([
                [np.cos(theta), -np.sin(theta), 0],
                [np.sin(theta), np.cos(theta), 0],
                [0, 0, 1]
            ])
            matrices.append(A)

        return matrices, 3

    elif n == 6:
        # For C_6, try k=3
        angles = [2*np.pi*i/6 for i in range(6)]
        matrices = []

        for theta in angles:
            A = np.array([
                [np.cos(theta), -np.sin(theta), 0],
                [np.sin(theta), np.cos(theta), 0],
                [0, 0, np.cos(2*theta)]
            ])
            matrices.append(A)

        return matrices, 3

    elif n == 7:
        # For C_7, try k=4
        angles = [2*np.pi*i/7 for i in range(7)]
        matrices = []

        for theta in angles:
            A = np.array([
                [np.cos(theta), -np.sin(theta), 0, 0],
                [np.sin(theta), np.cos(theta), 0, 0],
                [0, 0, np.cos(2*theta), -np.sin(2*theta)],
                [0, 0, np.sin(2*theta), np.cos(2*theta)]
            ])
            matrices.append(A)

        return matrices, 4

    elif n == 8:
        # For C_8, try k=4
        angles = [2*np.pi*i/8 for i in range(8)]
        matrices = []

        for theta in angles:
            A = np.array([
                [np.cos(theta), -np.sin(theta), 0, 0],
                [np.sin(theta), np.cos(theta), 0, 0],
                [0, 0, np.cos(2*theta), -np.sin(2*theta)],
                [0, 0, np.sin(2*theta), np.cos(2*theta)]
            ])
            matrices.append(A)

        return matrices, 4

    return None, None

def test_all_constructions():
    """Test various constructions"""
    print("=" * 70)
    print("TESTING MATRIX CONSTRUCTIONS FOR CYCLE GRAPHS")
    print("=" * 70)

    results = {}

    for n in [4, 5, 6, 7, 8]:
        print(f"\n{'#' * 70}")
        print(f"# C_{n}")
        print(f"{'#' * 70}")

        found = False

        # Try block method
        matrices, k = construct_cycle_block_method(n)
        if matrices is not None:
            is_valid = verify_cycle_construction(matrices, n, f"Block method (k={k})")
            if is_valid:
                results[n] = k
                found = True

        if not found:
            # Try shift method
            matrices, k = construct_cycle_shift_method(n)
            if matrices is not None:
                is_valid = verify_cycle_construction(matrices, n, f"Shift method (k={k})")
                if is_valid:
                    results[n] = k
                    found = True

        if not found:
            # Try diagonal method
            matrices, k = construct_cycle_diagonal_method(n)
            if matrices is not None:
                is_valid = verify_cycle_construction(matrices, n, f"Diagonal method (k={k})")
                if is_valid:
                    results[n] = k
                    found = True

        if not found:
            print(f"\nNo valid construction found for C_{n}")

    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)

    if results:
        print("\nMinimum dimension k found:")
        print("-" * 40)
        for n in sorted(results.keys()):
            print(f"  C_{n}: k = {results[n]}")

        print("\n" + "=" * 70)
        print("PATTERN ANALYSIS")
        print("=" * 70)

        print("\nComparison:")
        print(f"{'n':<6} {'k':<6} {'ceil(n/2)':<12} {'floor(n/2)':<12}")
        print("-" * 40)

        for n in sorted(results.keys()):
            k = results[n]
            ceil_half = (n + 1) // 2
            floor_half = n // 2

            print(f"{n:<6} {k:<6} {ceil_half:<12} {floor_half:<12}")

        pattern_ceil = all(results[n] == (n + 1) // 2 for n in results.keys())
        pattern_floor = all(results[n] == n // 2 for n in results.keys())

        print("\n" + "-" * 40)
        if pattern_ceil:
            print("PATTERN: k = ceil(n/2) = (n+1)//2")
        elif pattern_floor:
            print("PATTERN: k = floor(n/2) = n//2")
        else:
            print("Mixed pattern")

if __name__ == "__main__":
    test_all_constructions()
