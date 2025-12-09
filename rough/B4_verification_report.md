# Putnam 2025 B4 - Verification Report

## Summary

**Main Result**: The bound $S \leq \frac{(n+2)N}{3}$ is **CORRECT** (verified for $n=2,3$).

**Current Proof Status**: The proof in `/test/solutions/B4.md` has **significant gaps**:
- Lemma 1 (depth bound): **CORRECT**
- Average depth calculation: **CORRECT**
- Support Lemma (Step 7): **FALSE** (counterexamples found)
- Final argument: **INCOMPLETE** (relies on false lemma)

## Detailed Verification

### 1. Lemma 1: Depth Bound

**Claim**: For any position $(i,j)$ with $i+j > n$, we have $a_{i,j} \leq i+j-n$.

**Status**: ✓ **CORRECT**

The induction proof is rigorous:
- Base case (depth 1): Predecessors are in zero region, so $a_{i,j} \in \{0,1\}$
- Inductive step: Predecessor at depth $d-1$ has value $\leq d-1$, so current entry $\leq d$

### 2. Average Depth Calculation

**Claim**: The average depth over all positions in the nonzero region is $(n+2)/3$.

**Status**: ✓ **CORRECT**

The calculation is verified:
- Total positions: $\frac{n(n+1)}{2}$
- Sum of depths: $\frac{n(n+1)(n+2)}{6}$
- Average: $\frac{n+2}{3}$

### 3. Support Lemma (Step 7)

**Claim**: If there are $k$ nonzero entries at depth $\ell \geq 2$, then there must be at least $\lceil k/2 \rceil$ nonzero entries at depth $\ell-1$.

**Status**: ✗ **FALSE**

**Counterexamples**:

For $n=2$:
```
Matrix: [[0, 0],
         [0, 1]]
```
- Depth 2: 1 nonzero entry
- Depth 1: 0 nonzero entries
- Required by lemma: $\lceil 1/2 \rceil = 1$
- **Violation**: 0 < 1

For $n=3$:
```
Matrix: [[0, 0, 0],
         [0, 0, 1],
         [0, 1, 2]]
```
- Depth 3: 1 nonzero entry (value 2)
- Depth 2: 2 nonzero entries
- Depth 1: 0 nonzero entries
- **Multiple violations**

The lemma fails because:
1. Entries can have value 1 even at high depths (by increasing from 0 to 1)
2. Nonzero entries don't need to "propagate" from lower depths

### 4. The Weighted Average Argument

The proof suggests that the weighted average depth of nonzero entries is at most $(n+2)/3$.

**This is FALSE**. We computed:

For $n=2$:
- Matrix with only $(2,2)$ nonzero has weighted average depth = 2
- This exceeds $(n+2)/3 = 4/3$

For $n=3$:
- Matrix with only $(3,3)$ nonzero has weighted average depth = 3
- This exceeds $(n+2)/3 = 5/3$

**The actual bound is**: $\sum_{\ell} \ell \cdot N_\ell \leq \sum_{\ell} \ell \cdot (n-\ell+1)$ (if all positions filled), but $N_\ell$ can be much smaller than $n-\ell+1$.

### 5. Why the Bound Actually Holds

Despite the flawed proof, the bound $S \leq (n+2)N/3$ **is correct**.

**Empirical findings**:

For $n=2$ (6 valid matrices):
- Maximum $S/N = 4/3 = (n+2)/3$ ✓
- Achieved when all positions filled with value = depth

For $n=3$ (28 valid matrices):
- Maximum $S/N = 5/3 = (n+2)/3$ ✓
- Achieved when all positions filled with value = depth

**Key observations**:
1. The bound is **tight** only when:
   - All positions in nonzero region are filled ($N = n(n+1)/2$)
   - All values equal their depth ($a_{i,j} = i+j-n$)

2. For any fixed $N$, the maximum $S$ satisfies $S \leq (n+2)N/3$

3. Partial filling (smaller $N$) gives **slack** in the bound

### 6. What's Missing: The Correct Proof

The current proof is incomplete. We need a rigorous argument showing why $S \leq (n+2)N/3$ for all valid matrices.

**Possible approaches**:

**Approach 1: Linear Programming / Optimization**
- The set of valid matrices forms a polyhedron
- Show that $S/N$ is maximized at the vertex where all positions are filled
- This would require analyzing the constraint structure

**Approach 2: Exchange Argument**
- Given any matrix with $S/N < (n+2)/3$, show we can increase $S/N$ by:
  - Adding more nonzero entries at low depths
  - Increasing values where possible
- Show this process terminates at the all-filled matrix

**Approach 3: Potential Function**
- Define a potential $\Phi$ that relates $S$ and $N$
- Show $\Phi$ is maximized when all positions filled

**Approach 4: Induction on Structure**
- Induct on the number of nonzero entries
- Show that adding entries optimally (to maximize $S$) forces us toward the all-filled configuration

None of these are fully developed in the current proof.

## Computational Verification

Ran exhaustive enumeration for $n=2,3$:

### $n=2$ Results:
- Total valid matrices: 6
- All satisfy $S \leq (n+2)N/3$ ✓
- Maximum ratio: $S/N = 1.333333 = (n+2)/3$
- Bound is tight ✓

### $n=3$ Results:
- Total valid matrices: 28
- All satisfy $S \leq (n+2)N/3$ ✓
- Maximum ratio: $S/N = 1.666667 = (n+2)/3$
- Bound is tight ✓

### Matrix achieving equality for $n=3$:
```
[[0, 0, 1],
 [0, 1, 2],
 [1, 2, 3]]
```
- All positions in nonzero region filled
- Each entry equals its depth: $a_{i,j} = i+j-n$

## Recommendations

1. **Remove or fix the Support Lemma**: It is false and unnecessary

2. **Develop a rigorous completion**: The proof needs a complete argument from Step 5 to the conclusion

3. **Possible correct argument** (sketch):
   - Use Lemma 1: $S \leq \sum_{a_{i,j} \neq 0} (i+j-n)$
   - The key is to show: $\sum_{a_{i,j} \neq 0} (i+j-n) \leq \frac{n+2}{3} \cdot N$
   - This is equivalent to: average depth of nonzero entries $\leq \frac{n+2}{3}$
   - But this is **FALSE** (we found counterexamples)
   - So we need: $S \leq c \cdot \sum_{a_{i,j} \neq 0} (i+j-n)$ for some $c < 1$
   - OR: Use the fact that $S$ grows slower than $\sum (i+j-n)$ when entries don't saturate the depth bound

4. **Alternative approach**: Show the maximum $S$ for each $N$ satisfies the bound
   - This was verified computationally
   - Would need to prove why "greedy filling" from low depths maximizes $S$

## Conclusion

The **answer is correct** and the bound is **tight**, but the **proof is incomplete**.

The main gap is in Steps 6-7, where the proof needs to establish the final inequality rigorously. The Support Lemma is false and the weighted average argument doesn't work.

A complete proof would likely use one of:
- An exchange/greedy argument
- A careful optimization over the constraint set
- A different potential function approach

**Verdict**: The solution needs significant revision to be rigorous enough for Putnam standards.
