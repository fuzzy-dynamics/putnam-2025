# Putnam 2025 A4 - Block Matrix Constructions

## Problem
Find minimal k such that there exist k×k REAL matrices A_1,...,A_2025 with:
- A_i A_j = A_j A_i if and only if |i-j| ∈ {0, 1, 2024}

## Key Constraint
The matrices must be REAL (not complex).

## Current Status
- Answer: k = 45
- Current solution uses complex Weyl matrices with ω = e^(2πi/45)
- Need to adapt to real matrices

---

## Block Matrix Explorations

### 1. Real Representations of Complex Matrices

**Strategy**: Replace each complex matrix by its real 2×2 block representation.

For a complex number z = a + bi, represent as:
$$\begin{pmatrix} a & -b \\ b & a \end{pmatrix}$$

For a complex n×n matrix, this gives a real 2n×2n matrix.

**Application to Weyl matrices**:

The complex construction uses 45×45 matrices X and Z where:
- X = cyclic shift matrix
- Z = diag(1, ω, ω², ..., ω^44) where ω = e^(2πi/45)

**Real representation of Z**:
Each diagonal entry ω^j = cos(2πj/45) + i·sin(2πj/45) becomes a 2×2 block:
$$R_j = \begin{pmatrix} \cos(2πj/45) & -\sin(2πj/45) \\ \sin(2πj/45) & \cos(2πj/45) \end{pmatrix}$$

So Z becomes a 90×90 real matrix that is block diagonal.

**Real representation of X**:
The shift matrix X becomes a 90×90 matrix that shifts blocks of size 2.

**Analysis**:
- This construction gives k = 90
- Each complex 45×45 matrix becomes real 90×90 matrix
- Commutativity is preserved under this representation
- BUT: This gives k = 90, not k = 45!

**Question**: Can we do better?

---

### 2. Direct Real Construction Using Rotation Matrices

**Idea**: Instead of complex phases, use real rotation matrices.

For the cycle C_2025, consider using rotation matrices in higher dimensions.

**Approach**:
For each i ∈ {1,...,2025}, construct A_i as a 45×45 real matrix.

Use the fact that SO(2) acts on ℝ² by rotations:
$$R(θ) = \begin{pmatrix} \cos θ & -\sin θ \\ \sin θ & \cos θ \end{pmatrix}$$

**Block diagonal construction**:
Partition 45 = 22 × 2 + 1 (or other decompositions).

Could construct A_i as block diagonal:
$$A_i = \begin{pmatrix} R(θ_i^{(1)}) & & & \\ & R(θ_i^{(2)}) & & \\ & & \ddots & \\ & & & R(θ_i^{(22)}) \\ & & & & 1 \end{pmatrix}$$

where the θ_i^{(j)} are chosen so that:
- A_i commutes with A_j iff |i-j| ∈ {0,1,2024}

**Analysis**:
Two block diagonal matrices (with same block structure) commute iff each corresponding pair of blocks commutes.

For 2×2 rotation matrices:
- R(α) and R(β) always commute (since SO(2) is abelian)

So this doesn't work - everything commutes!

**Modified approach**: Use different block structures
Could use non-commuting blocks in some positions.

---

### 3. Tensor Product Construction

**Idea**: Since 2025 = 45 × 45, use tensor products.

**Setup**:
Write i ∈ {0,...,2024} as i = 45a + b where a,b ∈ {0,...,44}.

Consider matrices of the form:
$$A_i = M_a \otimes N_b$$

where M_a are d×d matrices and N_b are e×e matrices, giving de×de overall.

**For commutativity**:
$$(M_a \otimes N_b)(M_c \otimes N_d) = (M_a M_c) \otimes (N_b N_d)$$

This commutes with:
$$(M_c \otimes N_d)(M_a \otimes N_b) = (M_c M_a) \otimes (N_d N_b)$$

iff M_a M_c = M_c M_a AND N_b N_d = N_d N_b.

**Analysis of cycle pattern**:
For i = 45a + b, the neighbors are:
- i+1: if b < 44, then (a, b+1); if b = 44, then (a+1, 0)
- i-1: if b > 0, then (a, b-1); if b = 0, then (a-1, 44)
- i+2024: corresponds to i-1 (since 2024 ≡ -1 mod 2025)

The cycle structure in (a,b) coordinates:
(0,0) → (0,1) → ... → (0,44) → (1,0) → (1,1) → ... → (44,44) → (0,0)

For tensor product M_a ⊗ N_b:
- (a,b) and (a,b+1) should commute → need N_b and N_{b+1} to commute
- (a,44) and (a+1,0) should commute → need N_44 and N_0 to commute AND M_a and M_{a+1} to commute

This suggests:
- All N_b should mutually commute (since consecutive b's must commute)
- All M_a should mutually commute (since we need M_a ⊗ N_44 to commute with M_{a+1} ⊗ N_0)

But if everything commutes, we can't get the cycle pattern!

**Conclusion**: Simple tensor products don't work.

---

### 4. Twisted Tensor Products / Mixed Terms

**Idea**: Use combinations like:
$$A_i = M_a \otimes N_b + M'_a \otimes N'_b$$

or more generally:
$$A_i = \sum_{j,k} c_{a,b}^{j,k} M_j \otimes N_k$$

**Analysis**:
This is more general but also more complex to analyze.

**Special case - Weyl-type**:
Use the fact that in the complex construction, we have:
$$A_i = \zeta^{f(a,b)} X^a Z^b$$

where XZ = ωZX (non-commutative!).

The key is the Weyl commutation relation.

**For real matrices**:
We need real matrices X̃ and Z̃ such that:
- X̃^45 = I
- Z̃^45 = I
- X̃Z̃ ≠ Z̃X̃ (non-commutative)

**Option 1**: Use the real representation (2×2 blocks) → gives k = 90

**Option 2**: Find intrinsically real construction with k = 45

---

### 5. Projection-Based Construction

**Idea**: Use matrices of the form:
$$A_i = \sum_{j=1}^{m} λ_i^{(j)} P_j$$

where P_j are orthogonal projections with ∑P_j = I.

**Commutativity**:
Two such matrices commute automatically if they share the same projections.

So this doesn't give non-commutativity.

**Modified approach**: Use non-orthogonal projections or non-commuting basis matrices.

---

### 6. Direct Sum Construction

**Idea**: Build A_i as direct sums of smaller blocks:
$$A_i = B_i^{(1)} \oplus B_i^{(2)} \oplus ... \oplus B_i^{(k)}$$

**Analysis**:
Two block diagonal matrices (with same block structure) commute iff all corresponding blocks commute.

So we need:
- For each block position j, the matrices B_1^{(j)}, B_2^{(j)}, ..., B_2025^{(j)} should exhibit the cycle commutativity pattern
- But these are smaller matrices!

This reduces the problem to smaller cases, but doesn't directly solve it.

---

### 7. Symmetric Matrices / Special Structure

**Question**: Can we use symmetric matrices? Skew-symmetric?

**Observation**:
- Not all symmetric matrices commute with each other
- Not all skew-symmetric matrices commute with each other

So we could potentially use special structures.

**Example - symmetric 2×2 matrices**:
$$A = \begin{pmatrix} a & b \\ b & c \end{pmatrix}, \quad B = \begin{pmatrix} p & q \\ q & r \end{pmatrix}$$

These commute iff:
$$bp + bq = aq + cr$$

This gives constraints but not immediate construction.

---

## Summary of Findings

### What Works (but not optimally):

1. **Real representation of complex Weyl matrices**:
   - Gives k = 90 (not 45)
   - Each complex entry becomes a 2×2 real block
   - Guaranteed to work, but doubles the dimension

### What Doesn't Work:

2. **Pure tensor products M_a ⊗ N_b**:
   - Forces too much commutativity
   - Can't match cycle pattern

3. **Block diagonal with commuting blocks**:
   - Everything commutes if blocks commute
   - Need non-commuting blocks

4. **Projection-based with orthogonal projections**:
   - Forces commutativity

### Open Questions:

1. **Can we achieve k = 45 with real matrices?**
   - Current best: k = 90
   - Lower bound: k ≥ 45 (from orthogonal rank)
   - Is the lower bound tight for REAL matrices?

2. **Refined lower bound for real matrices**:
   - The orthogonal rank argument gives ξ(C_2025) = 45
   - But this might apply to complex matrices
   - Does reality constraint increase the bound?

3. **Alternative constructions**:
   - Are there intrinsically real Weyl-type constructions?
   - Can we use SO(n) representations instead of U(n)?

---

## Next Steps

1. Verify whether k = 45 is achievable with real matrices or if k = 90 is minimal
2. Search literature on real representations of cycle graphs
3. Investigate whether orthogonal rank bounds apply to real vs complex matrices
4. Consider explicit construction with k = 90 as backup answer
