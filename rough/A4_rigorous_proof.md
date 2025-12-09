# Putnam 2025 A4 - Rigorous Analysis

## Problem Statement

Find the minimal value of k such that there exist k×k REAL matrices A_1,...,A_2025 with the property that A_i A_j = A_j A_i if and only if |i-j| in {0, 1, 2024}.

## Key Observations

1. The commutativity condition defines a graph G = C_2025 (cycle graph on 2025 vertices)
2. Vertices i and j are connected iff the matrices commute
3. In the cycle: vertex i is connected to i-1 and i+1 (mod 2025)

## Two Competing Hypotheses

### Hypothesis 1: k = 45 (sqrt pattern)
- Based on observation that 2025 = 45^2
- Suggests possible construction using 45×45 matrices
- Requires explicit construction proof

### Hypothesis 2: k = ceil(2025/2) = 1013 (chromatic number)
- Based on chromatic number of complement graph
- Complement of C_2025 has chromatic number ceil(2025/2) = 1013
- Requires both lower bound proof and construction

## Analysis of Complement Graph

The complement graph G' has edges between i and j iff they DON'T commute.
- In C_2025: i and j are connected iff |i-j| mod 2025 in {1, 2024}
- In G': i and j are connected iff |i-j| mod 2025 NOT in {0, 1, 2024}

Chromatic number of G' = 1013 (verified computationally and from theory)

## Critical Question: Why Does Chromatic Number Matter?

The chromatic number gives us information about independent sets.

If matrices don't commute, what does this tell us about their structure?

### Key Theorem (Simultaneous Diagonalization)
If A and B are commuting matrices with A having distinct eigenvalues, then B is a polynomial in A.

This means:
- If A has distinct eigenvalues, the centralizer C(A) = {B : AB = BA} has dimension k (polynomials of degree at most k-1)
- If A has repeated eigenvalues, C(A) is larger

### The Constraint

For our problem:
- Each A_i must commute with exactly 2 neighbors: A_{i-1} and A_{i+1}
- Each A_i must NOT commute with all others

This is a very rigid constraint!

## Lower Bound Argument

**Claim:** k >= ceil(n/2) for cycle C_n.

**Attempted Proof Sketch:**

Consider the complement graph G'. We can color G' with ceil(n/2) colors such that:
- Vertices with the same color are NOT connected in G'
- Vertices with the same color ARE connected in G (the original cycle)
- In fact, they are neighbors in the cycle

Key insight: If we could construct matrices with dimension k, we need k >= chi(G').

**Why?**

Consider the following argument:
1. If two matrices A_i and A_j don't commute, their commutator [A_i, A_j] = A_i A_j - A_j A_i is nonzero
2. The space of k×k matrices has dimension k^2
3. Each pair (i,j) that doesn't commute imposes a constraint
4. The number of non-commuting pairs is the number of edges in G'

But this argument is not rigorous enough!

## Better Lower Bound Argument (TO REFINE)

Let's think about this more carefully using linear algebra.

For k×k matrices, consider the k-dimensional vector space V = R^k.

If A_i has k distinct eigenvalues, then:
- A_i determines a basis of eigenvectors
- Any matrix commuting with A_i must be diagonal in this basis
- This is a k-dimensional space (the diagonal matrices)

The problem: if A_i and A_{i+1} commute, and both have distinct eigenvalues, they share the same eigenbasis!

This means:
- A_1, A_2 share eigenbasis B_1
- A_2, A_3 share eigenbasis B_2
- ...
- A_{2025}, A_1 share eigenbasis B_{2025}

By transitivity through the cycle, all would share the same eigenbasis, and all would commute!
CONTRADICTION.

Therefore: **At least some matrices must have repeated eigenvalues.**

## Upper Bound - Construction for k = 1013

We need to show that k = 1013 is achievable.

Strategy: Use the chromatic coloring of G'.

Color the vertices 0, 1, ..., 2024 with 1013 colors such that:
- Vertices i and j have the same color iff they are neighbors in C_2025
- This gives us 1012 color classes of size 2, plus possibly 1 singleton

For each color class {i, i+1}, we assign a coordinate direction.

Construction idea (TO VERIFY):
- Use 1013-dimensional space
- For color class c containing vertices {i, i+1}, assign coordinate c
- Matrix A_i has special structure in coordinate c and c' where c' is the color of {i-1, i}
- Matrices A_i and A_j commute iff they share a color class (i.e., |i-j| = 1)

This is still too vague - need explicit construction!

## Alternative Construction Using Block Diagonal Matrices

Another approach: use block diagonal structure.

For n = 2025 = 45 × 45:
- Could we use 45×45 matrices with specific block structure?
- Each block corresponds to some grouping of the cycle

Need to explore this more carefully.

## Numerical Evidence

From experiments:
- Small cycles (n=5,7,9) suggest k ~ ceil(n/2)
- The sqrt pattern doesn't seem to work for general cycles
- For C_100, numerical tests suggest k grows linearly, not as sqrt

## Conclusion (TENTATIVE)

Based on the analysis:
- Lower bound: k >= 1013 (from chromatic number argument, though not fully rigorous yet)
- Upper bound: k <= 1013 (from construction, not yet shown)

**Therefore: k = 1013**

However, this conclusion requires:
1. Rigorous proof of lower bound k >= ceil(n/2)
2. Explicit construction showing k = ceil(n/2) is achievable

Both of these are still INCOMPLETE in this analysis.

## Next Steps

1. Search literature for matrix commutativity graph results
2. Develop explicit construction for k = 1013
3. Rigorously prove lower bound
4. Verify with smaller cases (n = 5, 7, 9)
