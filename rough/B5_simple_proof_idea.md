# Simple Proof Idea for Putnam 2025 B5

## Observation from Data

Looking at the pattern:
- p=7: 1 inversion, need > 0.75
- p=11: 5 inversions, need > 1.75
- p=13: 3 inversions, need > 2.25
- p=17: 7 inversions, need > 3.25
- p=23: 11 inversions, need > 4.75

The bound p/4 - 1 grows linearly with p, and empirically we always exceed it.

## Key Insight: Counting Argument

Let's think about this differently. We have p-2 consecutive pairs total.

For each pair (k, k+1), exactly ONE of the following holds:
1. I(k+1) < I(k) (inversion)
2. I(k+1) > I(k) (non-inversion)

Let $N$ = number of inversions. We want to show $N > p/4 - 1$.

## Approach: Use the permutation structure

Since $I$ is a permutation, we can think of the sequence $I(1), I(2), \ldots, I(p-1)$ as a rearrangement of $1, 2, \ldots, p-1$.

For a "random" permutation:
- Expected number of inversions among consecutive pairs ≈ (p-2)/2
- But we need to use the specific structure of the INVERSE permutation

## Lemma: Fixed Points and Structure

Key facts about $I$:
1. $I(1) = 1$ (always)
2. $I(p-1) = p-1$ (always, since $(p-1) \cdot (p-1) = p^2 - 2p + 1 \equiv 1 \pmod{p}$)
3. $I(p-k) = p - I(k)$ (symmetry)

## Proof Attempt 1: Lower Bound via Partition

Partition $\{1, \ldots, p-1\}$ into:
- $A = \{1, \ldots, \lfloor p/2 \rfloor\}$
- $B = \{\lceil p/2 \rceil, \ldots, p-1\}$

Since $I$ is a bijection:
- $|I^{-1}(A)| = |A|$
- $|I^{-1}(B)| = |B|$

Consider consecutive pairs (k, k+1). We have:
- About $(p-1)/2 - 1$ pairs with both in same half
- 1 crossing pair

**Conjecture**: Among pairs where both k, k+1 are in the same half, at least some fraction have inversions.

But p=7 shows this isn't always true! We had 0 inversions in A and 0 in B, only the crossing inversion.

## Proof Attempt 2: Indirect Counting

Maybe instead of trying to count inversions directly, we should count NON-inversions and show there can't be too many?

For a non-inversion at k: $I(k+1) > I(k)$.

**Claim**: There cannot be more than $3p/4 - 1$ non-inversions.

If true, then inversions $\geq (p-2) - (3p/4 - 1) = p/4 - 1$... but we need STRICT inequality!

## Proof Attempt 3: Use Quadratic Residues?

Actually, thinking about this more carefully:
- For which k is I(k+1) < I(k)?
- This is equivalent to: $(k+1)^{-1} < k^{-1}$ as integers in $\{1, \ldots, p-1\}$

Let me think about when this happens...

If $k < p/2$ and $k+1 < p/2$:
- We have $k, k+1$ both small
- Their inverses $k^{-1}, (k+1)^{-1}$ could be anywhere in $\{1, \ldots, p-1\}$

Hmm, this is getting complicated.

## Proof Attempt 4: Direct Construction/Pigeonhole

Consider the sets:
- $S_< = \{k : I(k+1) < I(k)\}$ (inversions)
- $S_> = \{k : I(k+1) > I(k)\}$ (non-inversions)

We have $|S_<| + |S_>| = p - 2$.

Now, use the symmetry $I(p-k) = p - I(k)$.

For k ∈ {1, ..., p-2}, consider the pair $(k, p-1-k)$:
- At k: compare I(k+1) vs I(k)
- At p-1-k: compare I(p-k) vs I(p-1-k)
  = compare (p - I(k)) vs (p - I(k+1))
  = compare I(k) vs I(k+1) (reversed!)

So if k has an inversion (I(k+1) < I(k)), then p-1-k has a NON-inversion (I(p-k) > I(p-1-k)).

This means inversions and non-inversions are "balanced" under this pairing!

But wait, we need to be careful about the middle element when p-2 is even...

Actually, p is odd and > 3, so p-2 is odd. This means we can't pair everything perfectly.

Let me think more carefully about this pairing argument.
