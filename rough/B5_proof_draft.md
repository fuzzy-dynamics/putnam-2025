# Proof Draft for Putnam 2025 B5

## Problem
Let $p$ be a prime greater than 3. For each $k \in \{1, \ldots, p-1\}$, let $I(k) \in \{1, 2, \ldots, p-1\}$ be such that $k \cdot I(k) \equiv 1 \pmod{p}$ (the modular inverse).

Prove that the number of integers $k \in \{1, \ldots, p-2\}$ such that $I(k+1) < I(k)$ is greater than $\frac{p}{4} - 1$.

## Observations from Computation

1. The map $I: \{1, \ldots, p-1\} \to \{1, \ldots, p-1\}$ is a permutation (bijection).

2. **Symmetry**: $I(p-k) = p - I(k)$ for all $k \in \{1, \ldots, p-1\}$.
   - Proof: $(p-k) \cdot I(p-k) \equiv 1 \pmod{p}$
   - So $(p-k) \cdot I(p-k) \equiv 1 \pmod{p}$
   - We have $k \cdot I(k) \equiv 1 \pmod{p}$, so $(-k) \cdot (-I(k)) \equiv 1 \pmod{p}$
   - Thus $(p-k) \cdot (p - I(k)) \equiv 1 \pmod{p}$
   - Therefore $I(p-k) = p - I(k)$.

3. From computational testing:
   - For $p = 7$: 1 inversion (bound = 0.75)
   - For $p = 11$: 5 inversions (bound = 1.75)
   - For $p = 23$: 11 inversions (bound = 4.75)
   - The number of inversions is typically around $(p-2)/2$, much larger than the required bound.

## Proof Strategy 1: Partition Argument

Let $m = \lfloor (p-1)/2 \rfloor$.

Define:
- $S = \{1, 2, \ldots, m\}$ (small half)
- $L = \{m+1, m+2, \ldots, p-1\}$ (large half)

Since $I$ is a bijection, we have $|I(S)| = |S| = m$ and $|I(L)| = |L| = p - 1 - m$.

**Key Observation**: Among consecutive pairs $(k, k+1)$ where both $k, k+1 \in S$, let's count how many have $I(k+1) < I(k)$.

Actually, this approach is getting complex. Let me try a different angle.

## Proof Strategy 2: Complementary Counting

Let's count pairs $(k, k+1)$ where $I(k+1) > I(k)$ (non-inversions) and show there are at most $\frac{p}{4} + C$ of them for some small constant $C$.

Since there are $p - 2$ total consecutive pairs, if non-inversions $\leq \frac{p}{4} + C$, then inversions $\geq p - 2 - \frac{p}{4} - C = \frac{3p}{4} - 2 - C$, which is much stronger than needed.

But wait, this seems too strong. Let me reconsider.

## Proof Strategy 3: Using Symmetry

For each $k \in \{1, \ldots, p-2\}$, consider whether $I(k+1) < I(k)$ (an inversion).

By symmetry, if we pair up $k$ with $p - 1 - k$:
- Position $k$ checks if $I(k+1) < I(k)$
- Position $p - 1 - k$ checks if $I(p - k) < I(p - 1 - k)$

Using $I(p-j) = p - I(j)$:
- At position $p - 1 - k$: check if $I(p-k) < I(p-1-k)$
- This becomes: $p - I(k) < p - I(k+1)$
- Equivalently: $I(k) > I(k+1)$, which is the same as $I(k+1) < I(k)$!

So positions $k$ and $p - 1 - k$ have inversions in the SAME pattern!

Wait, let me recalculate this more carefully...

## Proof Strategy 4: Direct Computation Pattern

From the data, I notice:
- Partition $\{1, \ldots, p-1\}$ at $m = (p-1)/2$
- Consecutive pairs $(k, k+1)$ both in the same half contribute to inversions
- The middle crossing pair $(m, m+1)$ often also has an inversion

Let me count more carefully:
- Pairs both in $S$: $m - 1$ pairs
- Pairs both in $L$: $(p - 1 - m) - 1 = p - m - 2$ pairs
- Cross pair: 1 pair

For $p = 11$, $m = 5$:
- Pairs in $S = \{1,2,3,4,5\}$: 4 pairs, 2 inversions
- Pairs in $L = \{6,7,8,9,10\}$: 4 pairs, 2 inversions
- Cross $(5, 6)$: 1 inversion
- Total: 5 inversions

Hmm, about half of the pairs within each half have inversions. If we can show that at least $1/4$ of all pairs have inversions, we're done!

## Proof Strategy 5: Probabilistic/Counting Argument

Among all $p - 2$ consecutive pairs, if we can show that "random" behavior would give us $(p-2)/2$ inversions on average, and that the actual distribution guarantees at least $p/4 - 1$, we'd be done.

For a random permutation, the expected number of inversions among consecutive pairs is $(p-2)/2$ since each pair has a $1/2$ chance of being an inversion.

But we need to use the specific structure of the INVERSE permutation.

Let me think about this differently...

## Approach 6: Focus on Quadrants

Divide $\{1, \ldots, p-1\}$ into 4 parts based on size relative to $p/4$ and $p/2$...

Actually, let me try to formalize the partition argument more carefully.
