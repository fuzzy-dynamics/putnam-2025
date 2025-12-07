#!/usr/bin/env python3
"""
Verify the Putnam 2025 A4 solution.

Problem: Find minimal k such that there exist k-by-k real matrices A_1,...,A_2025
with A_i A_j = A_j A_i iff |i-j| in {0, 1, 2024}.

Solution claims k = 45 = sqrt(2025).
"""

import numpy as np
from itertools import combinations

print("=" * 80)
print("VERIFICATION OF PUTNAM 2025 A4 SOLUTION")
print("=" * 80)

# ============================================================================
# PART 1: Verify the problem structure
# ============================================================================
print("\n1. PROBLEM STRUCTURE VERIFICATION")
print("-" * 80)

n = 2025
print(f"Number of matrices: n = {n}")
print(f"Is n a perfect square? {n} = {int(np.sqrt(n))}^2 = {int(np.sqrt(n))**2}")
print(f"sqrt(n) = {np.sqrt(n)}")
print(f"Factorization: 2025 = 3^4 * 5^2 = 81 * 25 = {81 * 25}")

# Verify the commutativity structure forms a cycle
print("\nCommutativity structure:")
print("- A_i commutes with A_j iff |i-j| in {0, 1, 2024}")
print("- For i=1: commutes with A_1, A_2, A_2025")
print("- For i=2: commutes with A_1, A_2, A_3")
print("- For i=2025: commutes with A_1, A_2024, A_2025")
print("- This forms a cycle graph C_2025")

# ============================================================================
# PART 2: Verify the lower bound argument
# ============================================================================
print("\n2. LOWER BOUND VERIFICATION")
print("-" * 80)

# Check the independent set
k_claimed = 45
indices = [1 + 45*j for j in range(45)]
print(f"\nIndependent set of size {k_claimed}:")
print(f"Indices: {indices[:5]} ... {indices[-3:]}")

# Verify they don't commute pairwise
print("\nVerifying pairwise non-commutativity:")
all_non_commuting = True
for i, idx1 in enumerate(indices[:10]):  # Check first 10 for brevity
    for idx2 in indices[i+1:i+5]:  # Check next few
        diff = abs(idx1 - idx2)
        # In cycle, also check wraparound
        diff_cycle = min(diff, n - diff)
        commutes = diff_cycle in [0, 1, 2024]
        if commutes:
            print(f"  ERROR: A_{idx1} and A_{idx2} should NOT commute but |{idx1}-{idx2}| = {diff}")
            all_non_commuting = False

if all_non_commuting:
    print(f"  Confirmed: All sampled pairs in independent set do NOT commute")

print(f"\nClaim: {k_claimed} pairwise non-commuting matrices require dimension >= {k_claimed}")
print("This is based on 'orthogonal rank of C_2025'")

# ============================================================================
# PART 3: Verify the upper bound - Weyl matrix construction
# ============================================================================
print("\n3. UPPER BOUND VERIFICATION - WEYL MATRIX CONSTRUCTION")
print("-" * 80)

# We'll test with a smaller case first: n=9, k=3
# Then verify the algebra for n=2025, k=45

def test_weyl_construction_small():
    """Test with n=9, k=3 (since 9 = 3^2)"""
    print("\n3a. SMALL TEST CASE: n=9, k=3")
    print("-" * 40)

    n_small = 9
    k_small = 3

    # Create shift matrix X (3x3)
    X = np.zeros((k_small, k_small), dtype=complex)
    for j in range(k_small):
        X[j, (j+1) % k_small] = 1

    # Create clock matrix Z (3x3)
    omega = np.exp(2j * np.pi / k_small)
    Z = np.diag([omega**j for j in range(k_small)])

    print(f"X (shift matrix):\n{X}")
    print(f"\nZ (clock matrix, omega = e^(2πi/{k_small})):\n{Z}")

    # Verify Weyl relation: XZ = omega * ZX
    XZ = X @ Z
    ZX = Z @ X
    weyl_holds = np.allclose(XZ, omega * ZX)
    print(f"\nWeyl relation XZ = omega * ZX: {weyl_holds}")
    if not weyl_holds:
        print(f"  ERROR: Weyl relation fails!")
        print(f"  XZ =\n{XZ}")
        print(f"  omega*ZX =\n{omega * ZX}")

    # Create the A_i matrices
    A_matrices = []
    zeta = np.exp(2j * np.pi / n_small)

    for i in range(1, n_small + 1):
        # i-1 = k_small * a + b
        idx = i - 1
        a = idx // k_small
        b = idx % k_small

        # A_i = zeta^f(a,b) * X^a * Z^b
        # For simplicity, set f(a,b) = 0
        X_power = np.linalg.matrix_power(X, a)
        Z_power = np.linalg.matrix_power(Z, b)
        A_i = X_power @ Z_power
        A_matrices.append(A_i)

    # Check commutativity
    print(f"\nChecking commutativity for n={n_small}:")
    print("A_i and A_j should commute iff |i-j| in {0, 1, 8}")

    errors = []
    for i in range(n_small):
        for j in range(i+1, n_small):
            # Actual indices are i+1, j+1
            idx_i = i + 1
            idx_j = j + 1
            diff = abs(idx_i - idx_j)
            diff_cycle = min(diff, n_small - diff)
            should_commute = diff_cycle in [0, 1, n_small - 1]

            comm = A_matrices[i] @ A_matrices[j] - A_matrices[j] @ A_matrices[i]
            does_commute = np.allclose(comm, 0)

            if should_commute != does_commute:
                errors.append((idx_i, idx_j, diff, should_commute, does_commute))

    if errors:
        print(f"\n  ERROR: Found {len(errors)} mismatches!")
        for idx_i, idx_j, diff, should, does in errors[:10]:
            print(f"    A_{idx_i}, A_{idx_j}: |i-j|={diff}, should_commute={should}, does_commute={does}")
    else:
        print(f"  SUCCESS: All commutativity conditions correct!")

    return len(errors) == 0

test_weyl_construction_small()

# ============================================================================
# PART 4: Theoretical analysis of the construction
# ============================================================================
print("\n\n4. THEORETICAL ANALYSIS OF WEYL CONSTRUCTION")
print("-" * 80)

print("\nFor n=2025, k=45:")
print("Each index i in {1,...,2025} maps to (a,b) via i-1 = 45a + b")
print("where a,b in {0,1,...,44}")
print("\nA_i = zeta^f(a,b) * X^a * Z^b")
print("\nCommutator check:")
print("  A_i A_j = zeta^(f1+f2) * omega^(b*c) * X^(a+c) * Z^(b+d)")
print("  A_j A_i = zeta^(f1+f2) * omega^(a*d) * X^(a+c) * Z^(b+d)")
print("\nThey commute iff omega^(bc) = omega^(ad), i.e., bc ≡ ad (mod 45)")

print("\n\nCRITICAL QUESTION: Does bc ≡ ad (mod 45) correspond to |i-j| in {0,1,2024}?")

# Let's check this algebraically
print("\nLet i-1 = 45a + b and j-1 = 45c + d")
print("Then |i-j| = |45(a-c) + (b-d)|")
print("\nCase 1: |i-j| = 1")
print("  This means 45(a-c) + (b-d) = ±1")
print("  If a=c: then b-d = ±1 (neighbors in b)")
print("  If a≠c: then 45(a-c) + (b-d) = ±1 requires specific (a,b,c,d)")

print("\nCase 2: |i-j| = 2024 = 2025 - 1")
print("  This means 45(a-c) + (b-d) = ±2024 (mod 2025)")
print("  Since 2024 ≡ -1 (mod 2025), this is the wraparound case")

print("\n" + "!" * 80)
print("CRITICAL ISSUE IDENTIFIED:")
print("!" * 80)
print("\nThe condition 'bc ≡ ad (mod 45)' is purely algebraic in (a,b,c,d).")
print("But the condition '|i-j| in {0,1,2024}' depends on the specific")
print("enumeration i-1 = 45a + b.")
print("\nThese two conditions are NOT obviously equivalent!")
print("The solution does NOT provide a proof that they match.")
print("\n" + "!" * 80)

# ============================================================================
# PART 5: Alternative construction check
# ============================================================================
print("\n5. CHECKING IF STANDARD WEYL CONSTRUCTION WORKS")
print("-" * 80)

def check_weyl_commutation_pattern():
    """
    Check what commutation pattern we actually get with standard Weyl construction
    for small cases.
    """
    print("\nTesting standard Weyl construction for n=9, k=3:")

    n = 9
    k = 3

    # For each pair (i,j), compute (a,b) and (c,d), then check if bc ≡ ad (mod k)
    commute_matrix = np.zeros((n, n), dtype=bool)

    for i in range(1, n+1):
        for j in range(1, n+1):
            a = (i-1) // k
            b = (i-1) % k
            c = (j-1) // k
            d = (j-1) % k

            # Standard Weyl: commute iff bc ≡ ad (mod k)
            commutes = (b * c) % k == (a * d) % k
            commute_matrix[i-1, j-1] = commutes

    print("\nCommutation matrix (1=commute, 0=don't):")
    print(commute_matrix.astype(int))

    # Check what the desired pattern is
    desired_matrix = np.zeros((n, n), dtype=bool)
    for i in range(1, n+1):
        for j in range(1, n+1):
            diff = abs(i - j)
            diff_cycle = min(diff, n - diff)
            desired_matrix[i-1, j-1] = diff_cycle in [0, 1]

    print("\nDesired commutation matrix:")
    print(desired_matrix.astype(int))

    print("\nDo they match?", np.array_equal(commute_matrix, desired_matrix))

    if not np.array_equal(commute_matrix, desired_matrix):
        print("\nMismatches:")
        for i in range(n):
            for j in range(n):
                if commute_matrix[i,j] != desired_matrix[i,j]:
                    print(f"  ({i+1},{j+1}): got {commute_matrix[i,j]}, want {desired_matrix[i,j]}")

check_weyl_commutation_pattern()

print("\n" + "=" * 80)
print("VERIFICATION SUMMARY")
print("=" * 80)

print("""
FINDINGS:

1. LOWER BOUND (k >= 45):
   - The independent set argument is CORRECT: we can find 45 matrices that
     pairwise don't commute.
   - HOWEVER, the "orthogonal rank of C_2025" justification is QUESTIONABLE.
     * The orthogonal rank is a concept from graph theory about orthogonal
       representations, not directly about matrix dimensions.
     * A more rigorous argument would use the fact that if we have m pairwise
       non-commuting k×k matrices over any field, then k >= ceiling(sqrt(2m-1)).
     * For m=45, this gives k >= ceiling(sqrt(89)) = 10, which is too weak!

   STATUS: LOWER BOUND ARGUMENT IS WEAK OR INCORRECT

2. UPPER BOUND (k <= 45):
   - The Weyl matrix construction is a STANDARD technique.
   - HOWEVER, the solution does NOT prove that the commutation condition
     "bc ≡ ad (mod 45)" corresponds to "|i-j| in {0,1,2024}".
   - Testing with n=9, k=3 shows the patterns DON'T match naively.
   - The phase function f(a,b) is mentioned but NOT specified!

   STATUS: UPPER BOUND CONSTRUCTION IS INCOMPLETE

3. OVERALL ASSESSMENT:
   - The answer k=45 is PLAUSIBLE (since 2025 = 45^2)
   - But the proof has MAJOR GAPS in both directions
   - A correct solution would need:
     * Rigorous lower bound (possibly using representation theory)
     * Explicit construction showing the commutation pattern works

VERDICT: NEEDS MAJOR REVISION

The solution has the right intuition and likely the right answer, but lacks
mathematical rigor in both the lower and upper bound arguments.
""")
