# Putnam 2025 B4 - Final Verification Report

## Executive Summary

**Bound**: $S \leq \frac{(n+2)N}{3}$ is **CORRECT** (computationally verified for $n=2,3$).

**Proof Status**: **INCOMPLETE** - has critical gaps that make it non-rigorous.

**Main Issue**: Steps 6-7 rely on a false "Support Lemma" and an invalid weighted average argument.

---

## Problem Statement

For $n \geq 2$, let $A = [a_{i,j}]$ be an $n \times n$ matrix of nonnegative integers such that:
- (a) $a_{i,j} = 0$ when $i+j \leq n$
- (b) $a_{i+1,j} \in \{a_{i,j}, a_{i,j}+1\}$
- (c) $a_{i,j+1} \in \{a_{i,j}, a_{i,j}+1\}$

Let $S$ = sum of all entries, $N$ = number of nonzero entries.

**Prove**: $S \leq \frac{(n+2)N}{3}$

---

## Verification Results

### 1. Lemma 1 (Depth Bound): ✓ CORRECT

**Claim**: $a_{i,j} \leq i+j-n$ for all positions in the nonzero region.

**Verification**: The induction proof is rigorous and correct.

### 2. Average Depth Calculation: ✓ CORRECT

**Claim**: Average depth over all positions in nonzero region is $\frac{n+2}{3}$.

**Verification**: Calculation verified:
- Total positions: $\frac{n(n+1)}{2}$
- Sum of depths: $\frac{n(n+1)(n+2)}{6}$
- Average: $\frac{n+2}{3}$ ✓

### 3. Support Lemma (Step 7): ✗ FALSE

**Claim**: If there are $k$ nonzero entries at depth $\ell \geq 2$, then there must be at least $\lceil k/2 \rceil$ nonzero entries at depth $\ell-1$.

**Verification**: **FALSE** - multiple counterexamples found.

**Counterexample 1** ($n=2$):
```
Matrix: [[0, 0],
         [0, 1]]
```
- Depth 2: 1 nonzero entry
- Depth 1: 0 nonzero entries
- Lemma requires: $\lceil 1/2 \rceil = 1$ entry at depth 1
- **Violation**: $0 < 1$

**Counterexample 2** ($n=3$):
```
Matrix: [[0, 0, 0],
         [0, 0, 1],
         [0, 1, 2]]
```
- Depth 3: 1 nonzero entry
- Depth 2: 2 nonzero entries
- Depth 1: 0 nonzero entries
- Lemma would require nonzero entries at depth 1
- **Violation**: No such entries exist

**Why it fails**: Entries can have value 1 at any depth (by jumping from 0 to 1), so they don't require nonzero predecessors.

### 4. Weighted Average Argument: ✗ FALSE

**Claim** (implicit in Step 7): The weighted average depth of nonzero entries is at most $\frac{n+2}{3}$.

**Verification**: **FALSE** - counterexamples found.

**Counterexample** ($n=2$): Matrix with only position $(2,2)$ nonzero:
```
Matrix: [[0, 0],
         [0, 1]]
```
- Sum of depths for nonzero entries: $D = 2$
- Number of nonzero entries: $N = 1$
- Weighted average depth: $D/N = 2$
- Bound: $(n+2)/3 = 4/3 \approx 1.33$
- **Violation**: $2 > 4/3$

**Counterexample** ($n=3$): Matrix with only position $(3,3)$ nonzero:
```
Matrix: [[0, 0, 0],
         [0, 0, 0],
         [0, 0, 1]]
```
- Weighted average depth: $3$
- Bound: $(n+2)/3 = 5/3 \approx 1.67$
- **Violation**: $3 > 5/3$

**Conclusion**: The sum of depths $D = \sum_{a_{i,j} > 0} (i+j-n)$ can EXCEED $(n+2)N/3$ for sparse matrices.

---

## Computational Verification

### Exhaustive Enumeration Results

**$n=2$**:
- Valid matrices found: 6
- All satisfy $S \leq (n+2)N/3$: ✓ YES
- Maximum ratio: $S/N = 1.333... = (n+2)/3$
- Bound is **TIGHT**

**$n=3$**:
- Valid matrices found: 28
- All satisfy $S \leq (n+2)N/3$: ✓ YES
- Maximum ratio: $S/N = 1.666... = (n+2)/3$
- Bound is **TIGHT**

### Tight Configuration

The bound is achieved with equality when:
1. **All positions** in the nonzero region are filled ($N = n(n+1)/2$)
2. **All values equal their depth** ($a_{i,j} = i+j-n$ for all $i+j > n$)

**Example for $n=3$**:
```
Matrix: [[0, 0, 1],
         [0, 1, 2],
         [1, 2, 3]]

S = 1+1+2+1+2+3 = 10
N = 6
S/N = 10/6 = 5/3 = (n+2)/3 ✓
```

### Key Observations

1. **Tightness only at maximum density**: The bound $S/N = (n+2)/3$ is achieved only when $N$ is maximal.

2. **Slack for partial filling**: When $N < n(n+1)/2$, we have $S/N < (n+2)/3$ (strict inequality).

3. **Depth vs Value Gap**: For sparse matrices (small $N$):
   - Nonzero entries can be at high depths (large $D/N$)
   - But values are much smaller than depths (large gap: $D - S$)
   - Example: Position $(n,n)$ alone has depth $n$ but value only 1

---

## Why the Current Proof Fails

The proof attempts to show:
$$S \leq \sum_{a_{i,j} > 0} (i+j-n) \leq \frac{n+2}{3} \cdot N$$

- **First inequality** ($S \leq \sum (i+j-n)$): ✓ TRUE (from Lemma 1)
- **Second inequality** ($\sum (i+j-n) \leq (n+2)N/3$): ✗ FALSE

The second inequality claims the weighted average depth is at most $(n+2)/3$, which we showed is false.

The gap: While $S \leq \sum (i+j-n)$, we also have $\sum (i+j-n)$ can be MUCH larger than $(n+2)N/3$ for sparse matrices. So why does $S \leq (n+2)N/3$ still hold?

**Answer**: When matrices are sparse (small $N$, high depths), the values are MUCH smaller than the depth bound. The "deficit" $(i+j-n) - a_{i,j}$ is large.

---

## What a Correct Proof Needs

The proof must explain why $S \leq (n+2)N/3$ even though the weighted average depth can exceed $(n+2)/3$.

### Possible Approaches

**Approach 1: Optimization/Linear Programming**
- Formulate as LP: maximize $S$ subject to monotonicity constraints
- Use duality or KKT conditions to derive the bound
- Show optimal solution has all positions filled with value=depth

**Approach 2: Structural Induction**
- More sophisticated induction that tracks the relationship between $S$, $N$, and the position distribution
- Might need to strengthen the induction hypothesis

**Approach 3: Exchange/Greedy Argument**
- Show that to maximize $S$ for given $N$, we should:
  1. Fill positions starting from low depths
  2. Set all values to their maximum (depth)
- Prove this configuration achieves $S = (n+2)N/3$ at maximum

**Approach 4: Potential Function**
- Define a cleverer potential that captures the constraint structure
- Show this potential bounds $S/N$

**Approach 5: Generating Function/Algebraic**
- Use generating functions to count the contribution from each depth layer
- Derive the bound algebraically

---

## Recommendations

### For the Current Solution

1. **REMOVE or FIX Step 7 (Support Lemma)**:
   - The Support Lemma is false and should be removed
   - The "proof sketch" is hand-wavy and not rigorous

2. **REMOVE the Weighted Average Argument**:
   - The claim that weighted average depth $\leq (n+2)/3$ is false
   - Any argument based on this is invalid

3. **ADD a rigorous completion**:
   - Steps 1-5 are correct but incomplete
   - Need a rigorous argument from Step 5 to the conclusion
   - Current text says "a careful accounting shows..." which is not acceptable

### Proposed Fix (Sketch)

After Step 5, instead of the Support Lemma, use:

**Lemma** (Greedy Optimality): For any fixed $N$, the sum $S$ is maximized when:
1. We choose $N$ positions that include all positions at depths $1, 2, \ldots, k$ for some $k$, plus possibly some positions at depth $k+1$
2. We set $a_{i,j} = i+j-n$ for all chosen positions

**Proof of Lemma**: [This needs to be proven rigorously - not trivial!]

**Applying the Lemma**: The maximum $S$ for $N$ positions occurs when we fill the first $N$ positions (ordered by depth) with maximum values. This gives:
$$S \leq \text{sum of first } N \text{ depths}$$

The sum of the first $N$ depths, when $N \leq n(n+1)/2$, can be shown to satisfy:
$$\sum_{i=1}^{N} d_i \leq \frac{n+2}{3} \cdot N$$

where $d_i$ are the depths in increasing order.

**This is the missing piece** that needs to be proven rigorously.

---

## Conclusion

**Overall Assessment**:
- **Answer**: ✓ CORRECT
- **Bound is tight**: ✓ YES
- **Proof completeness**: ✗ INCOMPLETE (major gaps)
- **Proof correctness**: ✗ CONTAINS FALSE STATEMENTS

**Putnam Judging Standard**: The current proof would likely receive **partial credit** but not full marks due to:
- False lemma (Support Lemma)
- Hand-wavy conclusion ("a careful accounting shows...")
- Missing rigorous argument for the key inequality

**What's needed**: A complete rigorous proof of the inequality from Step 5 onwards.

**Computational confidence**: The bound is definitely correct (exhaustively verified for $n=2,3$), so the answer is right. The proof just needs to be made rigorous.

---

## Files Generated

1. `/test/verify/verify_B4.py` - Exhaustive enumeration and verification
2. `/test/verify/analyze_B4_proof.py` - Weighted average analysis
3. `/test/verify/correct_proof_B4.py` - Convexity analysis
4. `/test/verify/find_correct_proof_B4.py` - Pattern finding
5. `/test/verify/B4_final_insight.py` - Greedy strategy analysis
6. `/test/verify/B4_verification_report.md` - Detailed verification
7. `/test/verify/B4_CORRECT_PROOF.md` - Attempted correct proof
8. This file - Final comprehensive report

All verification code is available for review and can be extended for larger $n$ if needed.
