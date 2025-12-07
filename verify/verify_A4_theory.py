#!/usr/bin/env python3
"""
Verify the theoretical claims about orthogonal rank and Lovasz theta for C_2025.

Based on research:
- Lovasz theta for odd cycle C_{2n+1}: theta(C_{2n+1}) = (2n+1)*cos(pi/(2n+1))/(1+cos(pi/(2n+1)))
- For large n, this is approximately n + 1/2
- The orthogonal representation dimension relates to the Lovasz theta function
"""

import numpy as np

print("=" * 80)
print("THEORETICAL VERIFICATION: ORTHOGONAL RANK OF C_2025")
print("=" * 80)

n = 2025
# C_2025 is an odd cycle with 2025 vertices, so it's C_{2n+1} with 2n+1 = 2025
# Therefore n = 1012

cycle_n = 1012  # Since 2025 = 2*1012 + 1

# Lovasz theta for odd cycle C_{2n+1}
def lovasz_theta_odd_cycle(n):
    """
    Compute Lovasz theta for C_{2n+1}
    theta(C_{2n+1}) = (2n+1)*cos(pi/(2n+1))/(1+cos(pi/(2n+1)))
    """
    vertices = 2*n + 1
    angle = np.pi / vertices
    numerator = vertices * np.cos(angle)
    denominator = 1 + np.cos(angle)
    return numerator / denominator

theta = lovasz_theta_odd_cycle(cycle_n)
print(f"\nFor C_2025 (which is C_{{2*1012+1}}):")
print(f"Lovasz theta function: theta(C_2025) = {theta:.6f}")
print(f"Asymptotic approximation: n + 1/2 = {cycle_n + 0.5}")
print(f"Difference: {abs(theta - (cycle_n + 0.5)):.6f}")

# The independence number (maximum independent set) of C_n is floor(n/2)
independence_number = n // 2
print(f"\nIndependence number alpha(C_2025) = floor(2025/2) = {independence_number}")

# The solution claims orthogonal rank is ceil(sqrt(2025)) = 45
claimed_rank = 45
print(f"\nClaimed orthogonal rank: {claimed_rank}")
print(f"sqrt(2025) = {np.sqrt(n)}")

print("\n" + "=" * 80)
print("CRITICAL ANALYSIS")
print("=" * 80)

print("""
The Lovasz theta function theta(G) provides bounds on various graph parameters,
including the independence number alpha(G):

    alpha(G) <= theta(G) <= chromatic_number(complement(G))

For orthogonal representations:
- The minimum dimension d for which a graph G has an orthogonal representation
  is related to the theta function, but the exact relationship is complex.
- For odd cycles C_{2n+1}, the minimum orthogonal representation dimension is n+1.
  (They cannot be represented in dimension n, but can be in dimension n+1)

For C_2025 = C_{2*1012+1}:
- Minimum orthogonal representation dimension = 1012 + 1 = 1013

HOWEVER, the problem asks about MATRIX representations with a specific
commutativity pattern, which is DIFFERENT from orthogonal representations!

The connection is:
- If matrices A_1,...,A_n satisfy: A_i A_j = A_j A_i iff i,j are adjacent in G
- This is sometimes called a "matrix representation" of the complement graph
- The minimum dimension k for such a representation is NOT the same as the
  orthogonal representation dimension!

For the complement of C_2025:
- Vertices: {1,2,...,2025}
- Edges: all pairs (i,j) where |i-j| NOT in {0,1,2024}
- This means i,j are adjacent in complement iff |i-j| in {2,3,...,2023}

The claim that k >= sqrt(2025) = 45 would need a different argument!
""")

print("\n" + "=" * 80)
print("ALTERNATIVE LOWER BOUND")
print("=" * 80)

print("""
A classical result (Schur's bound): If we have m pairwise non-commuting
k×k matrices over any field, then:

    k >= ceiling(sqrt(2m - 1))

The solution identifies 45 pairwise non-commuting matrices.
Using Schur's bound:

    k >= ceiling(sqrt(2*45 - 1)) = ceiling(sqrt(89)) = 10

This is much weaker than the claimed k >= 45!

HOWEVER, there's a stronger result for certain graph structures.
The key insight might be related to the clique cover number or chromatic number
of the complement graph.

For cycle graphs, there are special results. Let me compute the chromatic number
of the complement of C_2025.
""")

# Complement of C_n has a special structure
# For odd n, the complement can be edge-colored with specific properties

print(f"\nComplement of C_2025:")
print(f"- Has 2025 vertices")
print(f"- Two vertices i,j are adjacent iff |i-j| in {{2,3,...,2023}}")
print(f"- The complement is NOT a cycle - it's almost a complete graph!")
print(f"- Missing edges: only the 2025 edges from the original cycle")

# The clique number of complement of C_n for odd n
# This is a well-known problem

print(f"\nClique number omega(complement(C_2025)):")
print(f"The complement of C_{{2n+1}} has clique number n = {cycle_n}")
print(f"These are the vertices {{1, 3, 5, ..., 2023}} (all odd) or all even")
print(f"Such a clique has size {cycle_n}")

print(f"\nChromatic number chi(complement(C_2025)):")
print(f"For odd cycles, chi(complement(C_{{2n+1}})) = n+1 = {cycle_n + 1}")

print("\n" + "=" * 80)
print("CONNECTION TO MATRIX DIMENSION")
print("=" * 80)

print(f"""
A key result (possibly from representation theory):

For a graph G with chromatic number chi(G), if we want k×k matrices A_v for
each vertex v such that A_v A_w = A_w A_v iff v,w are adjacent in G,
then we need:

    k >= chi(G)

For the complement of C_2025:
    chi(complement(C_2025)) = {cycle_n + 1}

This gives a lower bound of k >= {cycle_n + 1}.

But the solution claims k = 45 = sqrt(2025).

Since {cycle_n + 1} >> 45, there's a serious problem!

UNLESS... the problem is asking about a DIFFERENT graph structure!
""")

print("\n" + "=" * 80)
print("RE-EXAMINING THE PROBLEM")
print("=" * 80)

print("""
Wait! Let me reconsider the graph structure.

The problem says: A_i A_j = A_j A_i iff |i-j| in {0, 1, 2024}

In a CYCLE of length 2025:
- Vertex 1 is adjacent to vertices 2 and 2025
- Vertex 2 is adjacent to vertices 1 and 3
- ...
- Vertex 2025 is adjacent to vertices 2024 and 1

So |i-j| = 1 gives "normal" neighbors
And |i-j| = 2024 = 2025-1 gives the "wraparound" (1 and 2025 are neighbors)

This is indeed the cycle graph C_2025.

But we want matrices that COMMUTE on this structure, not on the complement!

So we're looking for the "commutativity dimension" of the cycle C_2025 itself.

This is a completely different question!
""")

# Now the question makes more sense - we need the minimum k such that we can
# assign k×k matrices to each vertex of C_2025 where A_i and A_j commute iff
# they're adjacent in the cycle.

print(f"""
For cycle C_n, there's a construction using circulant-like structures.

The key observation: if 2025 = 45^2, we can use a 2D lattice structure.

Arrange the indices 1,...,2025 in a 45×45 grid:
    1    2    3  ...   45
   46   47   48  ...   90
   91   92   93  ...  135
   ...
 1981 1982 1983  ... 2025

In this arrangement:
- Consecutive numbers (differing by 1) are horizontal neighbors
- Numbers differing by 45 are vertical neighbors (might not apply here)
- Numbers 1 and 2025 differ by 2024 (wraparound in cycle)

The construction likely uses tensor products or similar structure to encode
this in 45×45 matrices.

But the solution doesn't provide the explicit construction details!
""")

print("\n" + "=" * 80)
print("CONCLUSION")
print("=" * 80)

print(f"""
The answer k = 45 = sqrt(2025) is PLAUSIBLE based on the perfect square structure.

HOWEVER:
1. The "orthogonal rank" argument for the lower bound is INCORRECT or MISAPPLIED
   - Orthogonal representations give dimension ~1013, not 45
   - Schur's bound gives only k >= 10, not k >= 45
   - Need a different argument (possibly from algebraic graph theory)

2. The Weyl matrix construction for the upper bound is INCOMPLETE
   - The solution doesn't prove the commutation pattern matches
   - Testing with small cases shows it DOESN'T work naively
   - The phase function f(a,b) is mentioned but not specified

VERDICT: The solution needs MAJOR REVISION with rigorous proofs for both bounds.

The answer might be correct, but the arguments are insufficient for a Putnam solution.
""")
