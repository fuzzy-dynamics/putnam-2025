# Putnam 2025 A4 - Numerical Investigation Findings

## Problem Summary

Find the smallest dimension k such that there exist k x k real matrices A_1, ..., A_2025 where:
- A_i and A_j commute iff |i-j| ∈ {0, 1, 2024}
- This defines a cycle graph C_2025 commutativity pattern

## Claimed Solution

The solution claims k = 45 = sqrt(2025), based on:
1. Lower bound: orthogonal rank of C_2025 = ceil(sqrt(2025)) = 45
2. Upper bound: Weyl matrix construction with k = 45

## Critical Findings

### 1. Weyl Construction Does NOT Work (VERIFIED)

The simple Weyl construction A_i = X^a Z^b with:
- X = k x k shift matrix
- Z = k x k clock matrix
- i = ak + b (grid indexing for n = k^2)

**DOES NOT** produce the cycle commutativity pattern!

Tested: n = 4, 9, 16, 25, 36, ..., 225, 2025
Result: ALL FAILED - the Weyl commutation condition bc ≡ ad (mod k) does NOT match cycle adjacency

Example for n=4, k=2:
- Pair (0,2): cycle=NOT adjacent, weyl=commute → MISMATCH
- Pair (1,2): cycle=adjacent, weyl=NOT commute → MISMATCH

### 2. Orthogonal Rank Argument Needs Verification

The solution claims orthogonal rank(C_n) = ceil(sqrt(n)) for perfect squares.

**Orthogonal rank definition** (from literature search):
- An orthogonal representation of graph G assigns vectors v_i to vertices
- Vertices i,j are ADJACENT iff v_i ⊥ v_j
- Orthogonal rank = minimum dimension needed

**BUT:** The commutativity pattern is the COMPLEMENT of adjacency!
- In C_n: vertices are adjacent if |i-j| ∈ {1, n-1}
- For matrices: A_i, A_j should commute if adjacent
- In orthogonal representation: adjacent → orthogonal
- These are DIFFERENT concepts!

The connection between:
- Orthogonal rank of graph G
- Minimum matrix dimension for commutativity pattern of G

is NOT trivial and requires justification.

### 3. Independent Set Argument is Flawed

The solution claims: "45 matrices form independent set → must be pairwise non-commuting → k ≥ 45"

**Problem:** This doesn't prove k ≥ 45!
- Having many pairwise non-commuting matrices doesn't directly constrain dimension
- Example: 2x2 Pauli matrices {σ_x, σ_y, σ_z} are pairwise non-commuting
- You can have n/2 pairwise non-commuting matrices without requiring k = n/2

The correct argument must use:
- Representation theory of algebras
- Spectral properties
- Or explicit construction showing k < 45 is impossible

### 4. Numerical Optimization Failed

Gradient descent optimization to find matrices:
- Attempted for small n (5-25) with various k values
- All attempts failed to converge to valid solution
- Numerical instability suggests the problem is highly constrained

## What the Theoretical Solution Should Contain

1. **Correct Construction:**
   - Not simple Weyl matrices A_i = X^a Z^b
   - Possibly phase-modified: A_i = ζ^f(a,b) X^a Z^b with carefully chosen f
   - Or a completely different construction

2. **Rigorous Lower Bound:**
   - NOT just "independent set → pairwise non-commuting"
   - Need algebraic or representation-theoretic argument
   - Possibly using dimension of commutator algebra
   - Or spectral properties of the cycle graph

3. **Connection to Orthogonal Rank:**
   - Clarify relationship between:
     - Orthogonal rank of graph G (vector orthogonality)
     - Minimum matrix dimension for commutativity pattern
   - These might be related but are NOT the same thing

## Literature References

### Orthogonal Rank of Graphs:
- Lovász theta function: https://en.wikipedia.org/wiki/Lov%C3%A1sz_number
- Orthogonal representations: https://arxiv.org/pdf/1504.03662
- Shiu & Low, "Orthogonal embeddings of graphs": https://www.ejgta.org/index.php/ejgta/article/view/592

### Graph Commutativity Patterns:
- Need to search for "matrix commutativity graph" or "commutativity pattern representation"
- Connection to quantum graph states
- Representation theory of cycle groups

## Recommended Next Steps

1. **Find the correct Weyl construction:**
   - What is the phase function f(a,b)?
   - Or is there a different parameterization?

2. **Verify the lower bound rigorously:**
   - Can we prove k ≥ 45 without assuming orthogonal rank formula?
   - Try small cases: prove k ≥ 2 for n=4, k ≥ 3 for n=9, etc.

3. **Search literature:**
   - "Matrix representations of cycle graphs"
   - "Commutativity patterns"
   - "Heisenberg-Weyl group representations"

4. **Try explicit construction:**
   - For small n (4, 9, 16, 25), try to construct matrices explicitly
   - Use symbolic computation to find phase functions
   - Verify the pattern empirically before generalizing

## Conclusion

**The claimed solution k = 45 is UNVERIFIED numerically.**

The simple Weyl construction fails, and the lower bound argument is incomplete.
The answer may still be correct, but requires:
1. More sophisticated construction
2. Rigorous lower bound proof
3. Clarification of orthogonal rank connection

Further investigation needed before accepting k = 45 as the answer.
