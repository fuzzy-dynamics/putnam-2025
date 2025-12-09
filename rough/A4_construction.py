"""
Explicit construction for Putnam 2025 A4.

Goal: Construct 2025 matrices of dimension k×k satisfying the cycle commutativity pattern.

Key insight: Use the chromatic coloring of the complement graph to guide construction.
"""

import numpy as np


def get_chromatic_coloring(n):
    """
    Get optimal chromatic coloring of complement of C_n.

    For C_n, vertices i and j are neighbors if |i-j| mod n = 1.
    In complement, vertices i and j are connected if |i-j| mod n not in {0, 1}.

    Chromatic number is ceil(n/2).
    Optimal coloring: pair up consecutive vertices.
    """
    colors = {}
    if n % 2 == 0:
        for i in range(n):
            colors[i] = i // 2
    else:
        for i in range(n):
            colors[i] = i // 2

    return colors


def construct_matrices_v1(n, k):
    """
    Construction attempt 1: Use different eigenbases for different regions.

    Idea: Partition the k dimensions among ceil(n/2) groups.
    Each pair of consecutive matrices shares some dimensions.

    For cycle C_n, we need:
    - A_i and A_{i+1} commute
    - A_i and A_j don't commute if |i-j| not in {0, 1, n-1}
    """

    chi = (n + 1) // 2  # chromatic number

    if k < chi:
        print(f"k={k} < chromatic number {chi}, impossible")
        return None

    print(f"Attempting construction with n={n}, k={k}, chi={chi}")

    # Key idea: Use shift matrices with specific structure
    # For each matrix A_i, create a matrix that:
    # 1. Commutes with A_{i-1} and A_{i+1}
    # 2. Doesn't commute with others

    # This is hard! Let's try a different approach.

    # Alternative: Use block diagonal structure
    # Divide k dimensions into chi blocks
    # Each pair (i, i+1) gets assigned to block b(i)

    colors = get_chromatic_coloring(n)

    # For now, construct using a simple pattern - will likely fail
    matrices = []

    for i in range(n):
        # Create a k×k matrix for A_i
        A = np.zeros((k, k))

        # Strategy: Use coordinates corresponding to the two color classes
        # that vertex i belongs to

        # Color class for (i-1, i)
        c_prev = colors[i-1] if i > 0 else colors[n-1]
        # Color class for (i, i+1)
        c_next = colors[i]

        # Put non-zero values in these coordinates
        if c_prev < k:
            A[c_prev, c_prev] = i + 1
        if c_next < k and c_next != c_prev:
            A[c_next, c_next] = i + 2

        matrices.append(A)

    # This construction is too naive and won't work!
    return matrices


def construct_matrices_v2_jordan_blocks(n, k):
    """
    Construction attempt 2: Use Jordan blocks to break simultaneous diagonalization.

    Key insight: If matrices have Jordan blocks with eigenvalue multiplicity,
    they can commute without being simultaneously diagonalizable in the usual sense.

    For n = 2025, we use k = 1013.
    """

    chi = (n + 1) // 2

    if k < chi:
        return None

    print(f"Jordan block construction: n={n}, k={k}")

    # Idea: Create matrices with specific Jordan block structure
    # that allows local commutativity but prevents global commutativity

    matrices = []

    # Get coloring
    colors = get_chromatic_coloring(n)

    for i in range(n):
        # Create matrix A_i
        A = np.zeros((k, k))

        # Use different eigenvalues for different regions
        # Matrix i has special structure in dimensions related to its color classes

        for j in range(k):
            # Diagonal entry
            A[j, j] = (i * 1.0) / (j + 1.0)

        # Add some off-diagonal structure based on coloring
        c_i = colors[i]
        if c_i < k - 1:
            A[c_i, c_i + 1] = 0.1 * i

        matrices.append(A)

    return matrices


def verify_commutativity_pattern(matrices, n):
    """
    Verify that the constructed matrices satisfy the cycle pattern.
    """

    num_correct = 0
    num_wrong = 0

    for i in range(n):
        for j in range(n):
            diff = min(abs(i - j), n - abs(i - j))
            should_commute = (diff == 0 or diff == 1)

            comm = matrices[i] @ matrices[j] - matrices[j] @ matrices[i]
            actually_commutes = np.allclose(comm, 0, atol=1e-10)

            if should_commute == actually_commutes:
                num_correct += 1
            else:
                num_wrong += 1
                if num_wrong <= 10:  # Print first few errors
                    print(f"Error at ({i},{j}): should_commute={should_commute}, actually={actually_commutes}, ||comm||={np.linalg.norm(comm):.6f}")

    total = n * n
    print(f"\nResults: {num_correct}/{total} correct ({100*num_correct/total:.1f}%)")
    print(f"Errors: {num_wrong}")

    return num_wrong == 0


def theoretical_construction_sketch(n):
    """
    Sketch of theoretical construction for general n.

    This doesn't construct actual matrices, but outlines the mathematical approach.
    """

    chi = (n + 1) // 2
    k = chi

    print(f"\n{'='*80}")
    print(f"THEORETICAL CONSTRUCTION SKETCH for n={n}")
    print(f"{'='*80}")

    print(f"\nMinimal dimension: k = {k}")
    print(f"\nConstruction strategy:")
    print(f"1. Use {k}-dimensional space R^{k}")
    print(f"2. Color vertices of C_{n} using {k} colors (chromatic coloring of complement)")
    print(f"3. Each color class corresponds to a 'coordinate region'")
    print(f"")
    print(f"For each matrix A_i:")
    print(f"  - A_i has special structure in coordinates c(i-1) and c(i)")
    print(f"    where c(j) is the color of edge (j, j+1)")
    print(f"  - A_i and A_(i+1) share color c(i), allowing them to commute")
    print(f"  - A_i and A_j for |i-j| > 1 have disjoint 'active coordinates', preventing commutativity")
    print(f"")
    print(f"Key challenge: Make the construction explicit and prove it works!")
    print(f"")
    print(f"Possible approaches:")
    print(f"  (a) Use shift/rotation matrices in appropriate subspaces")
    print(f"  (b) Use tensor product structure")
    print(f"  (c) Use nilpotent matrices with specific Jordan structure")
    print(f"")


if __name__ == "__main__":
    print("PUTNAM 2025 A4 - CONSTRUCTION ATTEMPTS")
    print("="*80)

    # Test small cases
    for n in [5, 7]:
        print(f"\n\nTesting n={n}:")
        print("-"*80)

        chi = (n + 1) // 2
        print(f"Chromatic number: {chi}")

        # Attempt construction
        k = chi
        matrices_v2 = construct_matrices_v2_jordan_blocks(n, k)

        if matrices_v2:
            print(f"\nVerifying v2 construction:")
            verify_commutativity_pattern(matrices_v2, n)

    # Theoretical sketch for n=2025
    theoretical_construction_sketch(2025)

    print("\n" + "="*80)
    print("CONCLUSION")
    print("="*80)
    print("""
The constructions attempted above are naive and don't work.
The actual construction requires more sophisticated linear algebra.

Key insight from theory:
- Lower bound: k >= ceil(n/2) from chromatic number
- Upper bound: Needs explicit construction (not yet achieved)

For Putnam 2025 A4 with n=2025:
- Strong conjecture: k = 1013
- But rigorous proof requires:
  1. Proof of lower bound k >= 1013
  2. Explicit construction showing k <= 1013

Alternative possibility: k = 45 if there's a clever construction using 2025 = 45^2
But this seems unlikely based on theory and numerical evidence.
""")
