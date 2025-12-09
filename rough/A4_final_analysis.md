# Putnam 2025 A4 - Final Rigorous Analysis

## Problem Restatement

Find minimal k such that there exist k×k REAL matrices A_1,...,A_2025 with:
A_i A_j = A_j A_i if and only if |i-j| in {0, 1, 2024} (mod 2025).

## The Commutativity Graph

Define graph G with:
- Vertices: {1, 2, ..., 2025}
- Edges: (i,j) is an edge iff A_i and A_j commute

The condition states G = C_2025 (cycle graph).

## Key Insight: Clique Cover Number!

**Definition:** A clique cover of G is a collection of cliques whose union covers all vertices.
The clique cover number cc(G) is the minimum number of cliques needed.

**Fundamental Theorem:**
For any graph G: cc(G) = χ(G'), where G' is the complement and χ is chromatic number.

**For matrices:**
If matrices {A_i : i in S} all pairwise commute, they form a commutative family.
Such a family can be simultaneously "block-diagonalized" in some sense.

## Analysis for C_2025

For cycle C_2025:
- Maximum clique size = 2 (edges)
- Each clique can contain at most 2 vertices
- We need to cover 2025 vertices with cliques of size at most 2

Wait, this gives cc(C_2025) = ceil(2025/2) = 1013.

Let me verify this matches χ(complement):
- Complement of C_2025 has chromatic number ceil(2025/2) = 1013
- Therefore cc(C_2025) = 1013 ✓

## Connection to Matrix Dimension

**Key Claim:** If G is the commutativity graph of n matrices of dimension k×k, then k >= cc(G).

**Proof Sketch:**

1. Let S_1, S_2, ..., S_m be a clique cover of G (m = cc(G))
2. Each S_i is a set of pairwise commuting matrices
3. For a set of pairwise commuting matrices with generic eigenvalues:
   - They can be simultaneously block-diagonalized
   - The "active space" for S_i has dimension >= |S_i| in some sense

Actually, this argument is not quite right. Let me think more carefully...

## Better Argument Using Linear Independence

Consider the commutator space approach:

For k×k matrices, the space Mat_k(R) has dimension k^2.

If A and B don't commute, their commutator [A,B] = AB - BA is a nonzero constraint.

The complement graph G' has edges (i,j) when A_i and A_j DON'T commute.

We need to count how many "independent non-commutativity constraints" exist.

This is related to the chromatic number of G', but the exact relationship is subtle.

## Alternative: Direct Construction Approach

Let's try to construct explicitly for small cases and extrapolate.

### For C_3:
- A_1 commutes with A_2 and A_3
- A_2 commutes with A_1 and A_3
- A_3 commutes with A_1 and A_2
- All three commute! Triangle.
- Can use k=1 (scalars work)

### For C_4:
- A_1 commutes with A_2 and A_4
- A_2 commutes with A_1 and A_3
- A_3 commutes with A_2 and A_4
- A_4 commutes with A_3 and A_1
- Square cycle.
- Need A_1 and A_3 to NOT commute
- Need A_2 and A_4 to NOT commute
- cc(C_4) = 2, χ(complement) = 2
- Expected k = 2

Can we construct with k=2?
Try:
- A_1 = [[1, 0], [0, 0]]
- A_2 = [[1, 1], [0, 0]]  (should commute with A_1? No! These don't commute)

Hmm, construction is tricky.

Let me try:
- A_1 = [[1, 0], [0, -1]]  (diagonal)
- A_2 = [[0, 1], [1, 0]]    (off-diagonal)
- A_3 = [[-1, 0], [0, 1]]   (diagonal)
- A_4 = [[0, -1], [-1, 0]]  (off-diagonal)

Check:
- A_1 A_2 = [[0,1],[0,0]], A_2 A_1 = [[0,1],[0,0]] ✗ These commute! Bad.

The diagonal + off-diagonal doesn't work for cycle.

Let me try different approach:
- A_1 = [[1, 0], [0, 0]]
- A_2 = [[a, b], [b, 1-a]] (should commute with A_1)
  For commutativity: A_1 A_2 = [[a, b], [0, 0]], A_2 A_1 = [[a, 0], [b, 0]]
  Need b=0 and b=0, so A_2 = [[a, 0], [0, 1-a]] (diagonal)

If A_1, A_2 commute and both are diagonal in same basis, then A_3, A_4 must also be diagonal (by commutativity with A_2, A_1 respectively).
But then all 4 are diagonal in same basis, so all commute. Contradiction!

**This means k > 1 for C_4.** Let's try k=2 more carefully.

Actually, wait. I think the issue is that we need GENERIC matrices, not all diagonal.

## Key Realization: Use Companion Matrices or Rotation Matrices

For cycle structures, consider using rotation/shift structure.

For C_n with k = ceil(n/2):

Construction idea:
- Use k-dimensional space
- Each matrix A_i is a "local rotation" in a 2D subspace
- A_i acts on subspace S_i
- A_i and A_{i+1} share some overlap in their active subspaces
- A_i and A_j for |i-j| large have disjoint active subspaces

This is still vague, but the intuition is:
- k = ceil(n/2) gives us ceil(n/2) "2D rotation planes"
- Each vertex gets assigned to 2 planes (for its two edges in the cycle)
- This is exactly the clique cover / chromatic coloring structure!

## Conclusion (Still Tentative)

For C_2025:
- k = 1013 is highly likely the answer
- Based on: cc(C_2025) = χ(complement(C_2025)) = 1013

But we still need:
1. **Rigorous lower bound proof**: k >= 1013
2. **Explicit construction**: k <= 1013

The construction is the hard part!

## Alternative: k = 45 Analysis

Could k = 45 work using 2025 = 45 × 45 structure?

For this to work, we'd need some special tensor product or block structure.

But this seems incompatible with the clique cover bound of 1013.

Unless... there's a mistake in my clique cover analysis?

Let me double-check:
- C_2025 has edges (i, i+1) for i = 1..2025 (indices mod 2025)
- A clique in C_2025 is a set of pairwise-connected vertices
- Max clique size in C_2025 is 2 (just an edge)
- To cover 2025 vertices with cliques of size ≤ 2, need at least ceil(2025/2) = 1013 cliques
- So cc(C_2025) >= 1013

Can we achieve 1013? Yes - pair up consecutive vertices: {1,2}, {3,4}, ..., {2023,2024}, {2025}.
This gives 1013 cliques (1012 pairs + 1 singleton).

Wait, but {2025, 1} is also an edge! So we can do: {1,2}, {3,4}, ..., {2023,2024}, {2025}.
Hmm, vertex 2025 is only covered once, but it's adjacent to both 2024 and 1.

Actually, a clique cover doesn't need to use edges - just needs to cover vertices!
{1,2}, {3,4}, ..., {2025} is valid with 1013 cliques.

Or better: {1,2}, {3,4}, ..., {2023,2024}, {2025,1} - wait, this is 1013 cliques but {2025,1} covers 2025 and 1, but 1 is already in {1,2}.

OK, clique cover allows overlap. So:
- {1,2}, {3,4}, ..., {2023,2024}, {2025} is 1013 cliques (1012 pairs + 1 singleton)

Or:
- Since n=2025 is odd, we can't pair everyone
- Optimal is 1013 cliques

## FINAL ANSWER CONJECTURE

**k = 1013**

Based on clique cover number = chromatic number of complement = 1013.

The 45 hypothesis seems to be a red herring based on 2025 = 45^2, but doesn't have mathematical support.
