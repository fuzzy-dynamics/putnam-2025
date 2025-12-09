#!/usr/bin/env python3
"""
Test the Weyl construction claim for Putnam 2025 A4.

The solution claims k=45 using Weyl matrices with phase corrections.
Let's verify if this actually works.
"""

import numpy as np


def construct_weyl_matrices(n, k, verbose=True):
    """
    Construct matrices using Weyl construction.

    Args:
        n: number of matrices (e.g., 2025)
        k: dimension (e.g., 45 = sqrt(2025))

    Returns:
        List of n k×k matrices
    """
    if verbose:
        print(f"Constructing {n} matrices of dimension {k}×{k}")

    # Create Weyl generators
    omega = np.exp(2j * np.pi / k)

    # Shift matrix X
    X = np.zeros((k, k), dtype=complex)
    for j in range(k):
        X[j, (j+1) % k] = 1

    # Clock matrix Z
    Z = np.diag([omega**j for j in range(k)])

    if verbose:
        print(f"omega = exp(2πi/{k}) = {omega}")
        # Verify Weyl relation
        XZ = X @ Z
        ZX = Z @ X
        weyl_ok = np.allclose(XZ, omega * ZX)
        print(f"Weyl relation XZ = omega*ZX: {weyl_ok}")

    # Create A_i matrices
    matrices = []
    zeta = np.exp(2j * np.pi / n)

    for i in range(1, n+1):
        # Decompose i-1 = k*a + b
        idx = i - 1
        a = idx // k
        b = idx % k

        # Phase function - try several options
        # Option 1: f(a,b) = 0
        phase = 0

        # A_i = zeta^phase * X^a * Z^b
        X_power = np.linalg.matrix_power(X, a)
        Z_power = np.linalg.matrix_power(Z, b)
        A_i = (zeta ** phase) * X_power @ Z_power

        matrices.append(A_i)

    return matrices


def verify_commutativity(matrices, n, verbose=True, tol=1e-10):
    """
    Verify the cycle commutativity pattern.

    A_i and A_j should commute iff |i-j| in {0, 1, n-1}.
    """
    errors = []
    commute_pairs = 0
    non_commute_pairs = 0

    # Check a sample of pairs
    sample_size = min(100, n)
    indices_to_check = list(range(sample_size))

    if verbose:
        print(f"\nChecking commutativity for sample of {sample_size} indices...")

    for i in indices_to_check:
        for j in range(i+1, min(n, i+sample_size)):
            # Should they commute?
            diff = abs(i - j)
            diff_cyclic = min(diff, n - diff)
            should_commute = (diff_cyclic in [0, 1])

            # Do they commute?
            comm = matrices[i] @ matrices[j] - matrices[j] @ matrices[i]
            comm_norm = np.linalg.norm(comm, 'fro')
            does_commute = (comm_norm < tol)

            if should_commute:
                commute_pairs += 1
                if not does_commute:
                    errors.append((i+1, j+1, diff_cyclic, 'should commute', comm_norm))
            else:
                non_commute_pairs += 1
                if does_commute:
                    errors.append((i+1, j+1, diff_cyclic, 'should NOT commute', comm_norm))

    if verbose:
        print(f"  Checked {commute_pairs} pairs that should commute")
        print(f"  Checked {non_commute_pairs} pairs that should NOT commute")
        print(f"  Errors: {len(errors)}")

        if len(errors) > 0:
            print(f"\n  First {min(10, len(errors))} errors:")
            for err in errors[:10]:
                print(f"    A_{err[0]}, A_{err[1]}: diff={err[2]}, {err[3]}, ||comm||={err[4]:.2e}")

    return len(errors) == 0, errors


def analyze_weyl_commutativity_condition(n, k):
    """
    Analyze when Weyl matrices commute.

    For A_i = X^a Z^b and A_j = X^c Z^d,
    they commute iff bc ≡ ad (mod k).

    Check if this corresponds to |i-j| in {0,1,n-1}.
    """
    print(f"\nAnalyzing Weyl commutativity condition for n={n}, k={k}")
    print("="*70)

    # Check the commutativity pattern
    mismatches = []

    for i in range(n):
        for j in range(i+1, n):
            # Decompose
            a = i // k
            b = i % k
            c = j // k
            d = j % k

            # Weyl condition: commute if bc ≡ ad (mod k)
            weyl_commute = ((b * c) % k == (a * d) % k)

            # Cycle condition
            diff = abs(i - j)
            diff_cyclic = min(diff, n - diff)
            cycle_commute = (diff_cyclic == 1)

            if weyl_commute != cycle_commute:
                if len(mismatches) < 20:
                    mismatches.append((i+1, j+1, diff, a, b, c, d, weyl_commute, cycle_commute))

    print(f"\nMismatches between Weyl and cycle conditions: {len(mismatches)}")
    print(f"Total pairs checked: {n*(n-1)//2}")
    print(f"Percentage of mismatches: {100*len(mismatches)/(n*(n-1)//2):.2f}%")

    if len(mismatches) > 0:
        print(f"\nFirst {min(10, len(mismatches))} mismatches:")
        print("i    j    |i-j|  (a,b)  (c,d)  Weyl  Cycle")
        for m in mismatches[:10]:
            i, j, diff, a, b, c, d, w, c_comm = m
            print(f"{i:<4} {j:<4} {diff:<6} ({a},{b}) ({c},{d}) {str(w):<5} {str(c_comm):<5}")

    return len(mismatches) == 0


def test_small_cases():
    """Test Weyl construction for small n"""
    print("="*70)
    print("TESTING WEYL CONSTRUCTION FOR SMALL CASES")
    print("="*70)

    test_cases = [
        (9, 3),   # 9 = 3^2
        (16, 4),  # 16 = 4^2
        (25, 5),  # 25 = 5^2
    ]

    for n, k in test_cases:
        print(f"\n{'#'*70}")
        print(f"# n={n}, k={k} (n = k^2)")
        print(f"{'#'*70}")

        # Analyze commutativity condition
        pattern_matches = analyze_weyl_commutativity_condition(n, k)

        if not pattern_matches:
            print(f"\n*** Weyl condition does NOT match cycle condition for n={n}, k={k} ***")
        else:
            print(f"\n*** SUCCESS: Weyl matches cycle for n={n}, k={k} ***")

            # Construct and verify
            matrices = construct_weyl_matrices(n, k, verbose=False)
            success, errors = verify_commutativity(matrices, n, verbose=True)

            if success:
                print(f"\n*** VERIFIED: Weyl construction works for n={n}, k={k} ***")
            else:
                print(f"\n*** FAILED: Weyl construction has errors for n={n}, k={k} ***")


def test_putnam_2025_a4():
    """Test the specific Putnam problem"""
    n = 2025
    k = 45  # sqrt(2025)

    print("\n" + "="*70)
    print(f"PUTNAM 2025 A4: n={n}, k={k}")
    print("="*70)

    # Analyze commutativity condition
    pattern_matches = analyze_weyl_commutativity_condition(n, k)

    if not pattern_matches:
        print(f"\n{'!'*70}")
        print(f"CRITICAL FINDING:")
        print(f"The Weyl commutation condition bc ≡ ad (mod {k})")
        print(f"does NOT correspond to the cycle adjacency condition |i-j| in {{1, {n-1}}}!")
        print(f"{'!'*70}")
        print(f"\nTherefore, the claimed construction with k={k} is INCORRECT!")
    else:
        print(f"\nPattern matches! Constructing matrices...")
        # Would construct here, but it's expensive for n=2025


if __name__ == "__main__":
    # Test small cases first
    test_small_cases()

    # Test Putnam problem
    test_putnam_2025_a4()

    print("\n" + "="*70)
    print("CONCLUSION")
    print("="*70)
    print("""
The standard Weyl construction with k = sqrt(n) does NOT work for cycle graphs!

The Weyl commutation relation gives: A_i and A_j commute iff bc ≡ ad (mod k)
where i-1 = ka + b and j-1 = kc + d.

But this condition is NOT equivalent to |i-j| in {1, n-1} for cycle C_n.

Therefore, the solution's claim that k=45 works is UNVERIFIED and likely WRONG.

The actual minimum dimension likely follows a different pattern, possibly:
- k = ceil(n/2) from clique cover of the complement graph
- Or some other formula related to representation theory

A rigorous solution requires either:
1. An explicit construction that actually works
2. A proof that no such construction exists for k < some_value
3. Better understanding of the quantum chromatic number / orthogonal rank
""")
