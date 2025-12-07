# Putnam 2025 A4: Explicit Construction Report

## Problem Statement

Find the minimal value of $k$ such that there exist $k \times k$ real matrices $A_1, \ldots, A_{2025}$ with:

$$A_i A_j = A_j A_i \iff |i-j| \in \{0, 1, 2024\}$$

This means the commutativity graph is the cycle $C_{2025}$.

## Executive Summary

**CRITICAL FINDING**: The claimed answer of $k = 45$ using Weyl/Heisenberg matrices is **INCORRECT**. The standard Weyl construction does NOT produce the required commutativity pattern for cycle graphs.

**STATUS**: The minimum dimension $k$ remains **UNDETERMINED**. Lower bounds suggest $k \geq \lceil 2025/2 \rceil = 1013$, but we have no explicit construction to establish an upper bound.

## Analysis

### 1. Commutativity Pattern

The condition defines a cycle graph $C_{2025}$:
- $A_i$ commutes with $A_{i-1}$ and $A_{i+1}$ (adjacent vertices)
- $A_1$ commutes with $A_{2025}$ (wraparound)
- All other pairs do NOT commute

### 2. Failed Approaches

#### Weyl/Heisenberg Construction (k=45)

The solution claims to use Weyl matrices with $k = \sqrt{2025} = 45$:

- Shift matrix $X$: cyclic permutation
- Clock matrix $Z$: diagonal with roots of unity
- Weyl relation: $XZ = \omega ZX$ where $\omega = e^{2\pi i/45}$

For $i-1 = 45a + b$, define: $A_i = X^a Z^b$

**Commutativity condition**: $A_i$ and $A_j$ commute iff $bc \equiv ad \pmod{45}$
where $i-1 = 45a+b$ and $j-1 = 45c+d$.

**Problem**: This condition is NOT equivalent to $|i-j| \in \{1, 2024\}$!

**Verification results**:
- For $n=2025$, $k=45$: Found 20 mismatches out of 2,049,300 pairs (0.00%)
- Examples of mismatches:
  - $A_1$ and $A_3$ ($|1-3|=2$): Weyl says commute, cycle says don't
  - $A_1$ and $A_4$ ($|1-4|=3$): Weyl says commute, cycle says don't
  - etc.

**Conclusion**: Weyl construction with $k=45$ does NOT work.

#### Block Diagonal Construction (k=1013)

Attempt based on clique cover of complement graph $C_{2025}^c$:

- Chromatic number: $\chi(C_{2025}^c) = \lceil 2025/2 \rceil = 1013$
- Color vertices so adjacent pairs get same color
- Assign each color a diagonal block

**Problem**: Matrices in orthogonal diagonal blocks ALWAYS commute!

- If $A_i$ has support only in block $\alpha$
- And $A_j$ has support only in block $\beta \neq \alpha$
- Then $A_i A_j = 0 = A_j A_i$ (they commute)

**Conclusion**: Simple block diagonal construction fails.

### 3. Theoretical Bounds

#### Lower Bound

**From clique cover of complement**:

The non-commutativity graph is $C_{2025}^c$ (complement of cycle).

Chromatic number: $\chi(C_{2025}^c) = 1013$

By representation theory, we need at least one dimension per color class to distinguish non-commuting pairs.

$$k \geq 1013$$

**From orthogonal rank** (claimed in solution):

The solution claims "orthogonal rank$(C_{2025}) = \lceil\sqrt{2025}\rceil = 45$"

However, this is **QUESTIONABLE**:
- Standard orthogonal rank of odd cycle $C_{2n+1}$ is $n+1$, not $\sqrt{2n+1}$
- For $C_{2025}$: standard orthogonal rank would be $1013$, not $45$
- The $\sqrt{n}$ formula may apply to **quantum chromatic number** over complex matrices with special properties

#### Upper Bound

**NO EXPLICIT CONSTRUCTION FOUND**

We have tested:
1. Weyl matrices (fails)
2. Block diagonal matrices (fails)
3. Rotation matrices (fails)
4. Upper triangular perturbations (fails)
5. Numerical optimization (fails due to instability)

### 4. Open Questions

**Question 1**: What is the quantum chromatic number of $C_{2025}$?

The literature suggests:
- For odd cycles, quantum chromatic number may be related to $\sqrt{n}$
- But we need precise theorems and proofs

**Question 2**: Does $k=45$ construction exist with different approach?

Possibilities:
- Non-standard phase corrections in Weyl construction
- Tensor products or more complex structure
- Non-Hermitian matrices

**Question 3**: Is the answer actually $k=1013$ or something else?

The clique cover argument gives $k \geq 1013$, but:
- We need an explicit construction to prove $k \leq 1013$
- Or a better lower bound to rule out $k < 1013$

## Recommendations

### For a Rigorous Solution

1. **Literature search**: Find papers on quantum chromatic number of odd cycles
   - Search for "quantum chromatic number odd cycle"
   - Look for "tracial rank" results
   - Check "commuting vs non-commuting quantum chromatic number"

2. **Consult experts**: This problem likely requires deep results from:
   - Quantum information theory
   - Graph representation theory
   - Non-commutative algebra

3. **Alternative approaches**:
   - Try complex (not just real) matrices
   - Consider projectors vs general matrices
   - Look at C*-algebra representations

### For Putnam Competition

The claimed answer $k=45$ appears in the solution file, but:

**The construction is NOT verified and likely WRONG**

A correct Putnam solution must:
- Prove the lower bound rigorously
- Provide an explicit construction for the upper bound
- Or prove that a claimed dimension is both necessary and sufficient

**Verdict**: The current solution is **INCOMPLETE** and potentially **INCORRECT**.

## Explicit Construction Attempts

### What We Tried

1. **Weyl matrices** ($k=45$): Commutativity pattern doesn't match
2. **Simple block diagonal** ($k=1013$): Non-adjacent blocks commute
3. **Rotation blocks** ($k=2 \times 1013$): Still commute in different blocks
4. **Upper triangular**: Adjacent pairs don't commute as required
5. **Numerical optimization**: Optimization landscape too complex

### What Might Work

**Conjecture**: A working construction for $C_n$ requires:

$$k = \lceil n/2 \rceil$$

with matrices that:
- Share a "direction" for adjacent pairs (allowing commutativity)
- Have orthogonal "directions" for non-adjacent pairs (forcing non-commutativity)
- Use off-diagonal entries to create controlled non-commutativity

**Possible approach**: Use 2×2 or 3×3 blocks for each color class, with carefully chosen rotation matrices or Pauli-like structures within blocks, and coupling between blocks.

## Conclusion

**The minimum dimension $k$ for Putnam 2025 A4 is UNKNOWN**.

- Lower bound: $k \geq 1013$ (from clique cover)
- Claimed answer: $k = 45$ (UNVERIFIED, likely wrong)
- Upper bound: None established

**Recommendation**: This problem requires either:
1. Finding the correct theoretical result from literature
2. Discovering a novel construction technique
3. Proving a better lower bound

The problem is significantly harder than the solution suggests, and a rigorous answer remains elusive.

## References

- [Clique cover - Wikipedia](https://en.wikipedia.org/wiki/Clique_cover)
- [Quantum chromatic number - arXiv:quant-ph/0608016](https://arxiv.org/abs/quant-ph/0608016)
- [Orthogonal representations - ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0024379507005526)
- [MathOverflow: Orthogonal matrix representations](https://mathoverflow.net/questions/45330/)
- Verification code: `/Users/arjo/Documents/base/solver/test/verify/A4_weyl_construction_corrected.py`
