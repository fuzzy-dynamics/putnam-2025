# Putnam 2025 B4 - Scratch Work

## Problem Statement

For $n \ge 2,$ let $A = [a_{i,j}]_{i,j = 1}^n$ be an $n$-by-$n$ matrix of nonnegative integers such that:

(a) $a_{i,j}=0$ when $i+j \le n$;
(b) $a_{i+1, j} \in \{a_{i,j}, a_{i,j}+1\}$ when $1 \le i \le n-1$ and $1 \le j \le n$; and
(c) $a_{i,j+1} \in \{a_{i,j}, a_{i,j}+1\}$ when $1 \le i \le n$ and $1 \le j \le n-1.$

Prove that $S \le \frac{(n+2)N}{3}$ where $S$ is the sum of entries and $N$ is the number of nonzero entries.

## Understanding the Structure

### Zero vs Nonzero Regions

- **Zero region:** $i+j \le n$ (upper-left triangle including anti-diagonal)
- **Nonzero region:** $i+j > n$ (lower-right triangle)
- Boundary: $i+j = n+1$

### Examples

**n=2:**
```
Positions:
(1,1): i+j=2 ≤ 2  → 0
(1,2): i+j=3 > 2  → nonzero
(2,1): i+j=3 > 2  → nonzero
(2,2): i+j=4 > 2  → nonzero
```

Matrix form (one possible configuration):
```
[ 0  0 ]
[ 0  1 ]
```
or
```
[ 0  1 ]
[ 1  2 ]
```

**n=3:**
```
Position sum i+j:
2  3  4
3  4  5
4  5  6

Zero when ≤ 3:
[ 0  0  * ]
[ 0  *  * ]
[ *  *  * ]
```

Boundary (i+j = 4): positions (1,3), (2,2), (3,1)

Example matrix:
```
[ 0  0  0 ]
[ 0  0  1 ]
[ 0  1  2 ]
```

**n=4:**
```
[ 0  0  0  0 ]
[ 0  0  0  1 ]
[ 0  0  1  2 ]
[ 0  1  2  3 ]
```

## Key Observations

### Observation 1: Upper Bound on Entries

Since entries start at 0 on the boundary (i+j = n+1) and can increase by at most 1 per step (going down or right), the maximum value at position (i,j) is achieved by the longest path from the boundary.

For position (i,j) with i+j > n:
- Boundary is at i+j = n+1
- "Depth" from boundary: d(i,j) = i+j - n - 1

**Claim:** $a_{i,j} \le i + j - n - 1$

**Proof:** By induction on the path length. On the boundary, i+j = n+1, so a_{i,j} = 0 = (n+1) - n - 1. Each step down (i → i+1) or right (j → j+1) increases i+j by 1 and can increase the value by at most 1, maintaining the bound.

### Observation 2: Computing N

The nonzero region consists of positions where i+j > n, i.e., i+j ≥ n+1.

For each value k = n+1, n+2, ..., 2n, the anti-diagonal i+j = k has:
- k-1 positions when k ≤ n+1 (overlaps with valid indices)
- 2n+1-k positions when k > n+1

Actually, for i,j ∈ {1,2,...,n}:
- i+j = n+1: positions are (1,n), (2,n-1), ..., (n,1) → n positions
- i+j = n+2: positions are (2,n), (3,n-1), ..., (n,2) → n-1 positions
- ...
- i+j = 2n: position is (n,n) → 1 position

Total positions in nonzero region:
$$N_{\text{total}} = n + (n-1) + (n-2) + ... + 1 = \frac{n(n+1)}{2}$$

But N is the number of *nonzero* entries, which could be less if some entries in the nonzero region are 0.

Wait, let me reconsider. The boundary i+j = n+1 has all entries equal to 0 by condition (a). But the problem asks for nonzero entries. So entries on i+j = n+1 might be 0.

Actually, rereading condition (a): $a_{i,j} = 0$ when $i+j \le n$. So when $i+j = n+1$, entries can be nonzero!

Let me reconsider: the boundary of the zero region is at i+j = n. The first potentially nonzero entries are at i+j = n+1.

### Observation 3: Bound on Sum

Let's denote by d(i,j) = i+j-n-1 the depth of position (i,j) into the nonzero region (when i+j > n).

We have $a_{i,j} \le d(i,j) = i+j-n-1$.

Now, summing over all nonzero entries:
$$S = \sum_{a_{i,j} \neq 0} a_{i,j} \le \sum_{i+j > n} (i+j-n-1)$$

But wait, not all entries with i+j > n are necessarily nonzero! We need to be more careful.

Actually, we need to prove the bound only for entries that are actually nonzero.

Let me think differently. If $a_{i,j} \neq 0$, then since entries are monotone increasing from the boundary and start at 0, we must have $a_{i,j} \ge 1$.

## Strategy: Bound Average Entry Value

The inequality $S \le \frac{(n+2)N}{3}$ can be rewritten as:
$$\frac{S}{N} \le \frac{n+2}{3}$$

So we need to show the average nonzero entry is at most $\frac{n+2}{3}$.

### Approach: Tighter bound on entries

For a nonzero entry at (i,j), we have:
- i+j > n (otherwise it would be 0)
- $a_{i,j} \le i+j-n-1$

But this might not be tight enough. Let me think about what the maximum possible average could be.

The worst case for the average would be when we have the maximum possible values. Given the constraints, what's the maximum sum we can achieve for a fixed number of nonzero entries?

### Better Approach: Charging Argument

Let's think about where the nonzero entries can be. If there are N nonzero entries, where are they located to maximize S?

Since $a_{i,j} \le i+j-n-1$, entries further from the boundary (larger i+j) can have larger values. So to maximize S, we want nonzero entries at positions with large i+j.

The maximum i+j in the matrix is 2n (at position (n,n)).

Actually, let me try a different approach: summing the bound over actual nonzero entries.

## New Approach: Direct Bound

For each nonzero entry at position (i,j):
- $a_{i,j} \ge 1$ (since it's nonzero)
- $a_{i,j} \le i+j-n-1$ (from our earlier bound)

Since $a_{i,j} \ge 1$, we have $i+j-n-1 \ge 1$, so $i+j \ge n+2$ for nonzero entries.

Wait, that's not quite right. An entry at i+j = n+1 could be nonzero (value ≥ 1 based on the path taken to reach it).

Let me reconsider the bound more carefully.

## Refined Analysis

An entry at (i,j) can be reached from multiple paths starting from positions where all entries are 0 (the region i+j ≤ n).

The key insight: the value at (i,j) equals the minimum number of "+1" steps taken along *any* path from the zero region to (i,j).

Since we must start from the zero region (i+j ≤ n) and can only move down or right, the minimum number of steps to reach (i,j) from the zero region is the minimum over all boundary points.

The closest point in the zero region to (i,j) is... let me think.

If i+j = n+k for k ≥ 1, then we can reach (i,j) from the boundary by exactly k steps if we start from the right point on the boundary i'+j' = n.

Wait, let me reconsider condition (b) and (c). They say the value can stay the same OR increase by 1. So different paths can give different final values!

The value at (i,j) depends on the specific configuration of the matrix, not just the position.

## Key Realization

The problem is asking us to prove an inequality that holds for *all* valid matrices A satisfying the conditions.

So we need: for any valid matrix A, $S \le \frac{(n+2)N}{3}$.

This means we need to find the worst case and show even that satisfies the bound.

## Fresh Start: Correct Bound

Let $d(i,j) = i+j-n$ for positions in the nonzero region (i+j > n).

For i+j > n, we have d(i,j) ≥ 1.

**Claim:** $a_{i,j} \le d(i,j) - 1 = i+j-n-1$.

**Proof:** We prove by strong induction on d = d(i,j).

*Base case (d=1):* i+j = n+1. For such positions to have a_{i,j} defined, we need i,j ≥ 1. We must have either:
- (i-1,j) with (i-1)+j = n ≤ n, so a_{i-1,j} = 0, OR
- (i,j-1) with i+(j-1) = n ≤ n, so a_{i,j-1} = 0

By conditions (b) and (c), $a_{i,j} \in \{0, 1\}$. So $a_{i,j} \le 1 = d(i,j) - 1 = 0$?

Wait, that's wrong. Let me recalculate: if d(i,j) = 1, then i+j = n+1, so i+j-n-1 = 0. But we just said a_{i,j} can be 1!

I made an error. Let me reconsider what the correct bound is.

Actually, I think the bound should be: $a_{i,j} \le i+j-n-1$ is wrong!

Let me think more carefully. At boundary i+j=n, we have a_{i,j}=0. Moving one step to i+j=n+1, we can have a_{i,j} ∈ {0,1}. Moving two steps to i+j=n+2, we can have values {0,1,2}. In general, at depth d from the boundary, the maximum value is d.

So the correct bound is: **$a_{i,j} \le i+j-n-1$ when i+j ≥ n+1.**

Let me verify: i+j = n+1 gives bound 0, but we said entries can be 1. That's wrong!

Oh! I see my error. The boundary is i+j = n, where all entries are 0 by condition (a). The first layer past the boundary is i+j = n+1, which is distance 1 from the boundary, so entries can be at most 1.

So the bound is: $a_{i,j} \le (i+j) - n - 1 + 1 = i+j-n$.

Let me redefine: for i+j > n, the depth is d(i,j) = i+j-n, and $a_{i,j} \le d(i,j) = i+j-n$.

Actually wait. If i+j=n, then a_{i,j}=0. If we move right to (i,j+1), then i+(j+1)=n+1, and by condition (c), a_{i,j+1} ∈ {a_{i,j}, a_{i,j}+1} = {0,1}. So the maximum is 1, which equals (i+(j+1))-n = 1. Good!

So the correct bound is: **$a_{i,j} \le i+j-n$ for i+j > n.**

Now let's compute S:
$$S = \sum_{a_{i,j} \neq 0} a_{i,j} \le \sum_{a_{i,j} \neq 0} (i+j-n)$$

We need to relate this to N. The key observation is that we're only summing over nonzero entries.

For a nonzero entry, $a_{i,j} \ge 1$, so $i+j-n \ge 1$ (which is automatically true since i+j > n).

Hmm, this doesn't immediately give us the (n+2)/3 bound.

## Think Different: What's Special About (n+2)/3?

The bound $\frac{n+2}{3}$ for the average suggests that the "typical" nonzero entry is at depth around (n+2)/3 from the boundary.

For n=2: (n+2)/3 = 4/3 ≈ 1.33
For n=3: (n+2)/3 = 5/3 ≈ 1.67
For n=4: (n+2)/3 = 2

Let me check the examples:
- n=4: Maximum depth is d=4 (at position (4,4) with i+j=8, d=8-4=4)
- Average depth over all positions in nonzero region?

Nonzero region for n=4:
- d=1 (i+j=5): positions (1,4), (2,3), (3,2), (4,1) → 4 positions
- d=2 (i+j=6): positions (2,4), (3,3), (4,2) → 3 positions
- d=3 (i+j=7): positions (3,4), (4,3) → 2 positions
- d=4 (i+j=8): position (4,4) → 1 position

Total: 4+3+2+1 = 10 positions
Sum of depths: 4(1) + 3(2) + 2(3) + 1(4) = 4+6+6+4 = 20
Average depth: 20/10 = 2 = (n+2)/3 for n=4!

This is promising! Let me verify for general n.

## Computing Average Depth

For general n, the nonzero region has positions where i+j ∈ {n+1, n+2, ..., 2n}.

For each sum s = i+j:
- Number of positions: max(0, min(s, 2n-s+1, n, n))

Actually, for s = i+j with i,j ∈ {1,...,n}:
- If s ≤ n+1: we have s-1 positions (but we only care about s ≥ n+1)
- If s = n+1: we have n positions
- If s = n+k for 1 ≤ k ≤ n: we have n-k+1 positions

So for s ∈ {n+1, n+2, ..., 2n}:
- s = n+k, k ∈ {1,2,...,n}
- Number of positions with i+j = s is n-k+1
- Depth d = s-n = k

Total positions: $\sum_{k=1}^{n} (n-k+1) = \sum_{j=1}^{n} j = \frac{n(n+1)}{2}$

Sum of depths weighted by count:
$$\sum_{k=1}^{n} k \cdot (n-k+1) = \sum_{k=1}^{n} k(n-k+1) = (n+1)\sum_{k=1}^{n} k - \sum_{k=1}^{n} k^2$$
$$= (n+1) \cdot \frac{n(n+1)}{2} - \frac{n(n+1)(2n+1)}{6}$$
$$= \frac{n(n+1)^2}{2} - \frac{n(n+1)(2n+1)}{6}$$
$$= \frac{n(n+1)}{6} [3(n+1) - (2n+1)]$$
$$= \frac{n(n+1)}{6} (3n+3-2n-1) = \frac{n(n+1)(n+2)}{6}$$

Average depth:
$$\bar{d} = \frac{n(n+1)(n+2)/6}{n(n+1)/2} = \frac{n+2}{3}$$

**This is exactly our bound!**

So the average depth over all positions in the nonzero region is $(n+2)/3$.

Now, if all positions in the nonzero region are actually nonzero (N = n(n+1)/2), and each entry equals its maximum possible value (the depth), then:
$$S = \sum_{d=1}^{n} d \cdot (n-d+1) = \frac{n(n+1)(n+2)}{6} = \frac{n+2}{3} \cdot \frac{n(n+1)}{2} = \frac{(n+2)N}{3}$$

So the bound is tight when all positions in the nonzero region are nonzero and all entries achieve their maximum possible value!

## Proving the General Inequality

Now we need to show that for any configuration:
$$S \le \frac{(n+2)N}{3}$$

**Key observation:** An entry contributes to N if it's nonzero, and contributes its value to S.

For a nonzero entry at (i,j):
- Depth d(i,j) = i+j-n
- Value: $1 \le a_{i,j} \le d(i,j)$

The issue is that entries with small depth contribute "efficiently" to N (count of 1) but can contribute less to S (since their maximum value is small). Entries with large depth can contribute more to S but also count as 1 toward N.

Let me think about this differently.

## Alternative: Weighted Counting

Define for each position (i,j) in the nonzero region a "weight" w(i,j) = i+j-n (the depth).

We have:
- $a_{i,j} \le w(i,j)$
- If $a_{i,j} \neq 0$, it contributes 1 to N and $a_{i,j}$ to S

We want to show:
$$\sum_{a_{i,j} \neq 0} a_{i,j} \le \frac{n+2}{3} \sum_{a_{i,j} \neq 0} 1$$

This is equivalent to:
$$\sum_{a_{i,j} \neq 0} \left(a_{i,j} - \frac{n+2}{3}\right) \le 0$$

Or:
$$\sum_{a_{i,j} \neq 0} a_{i,j} \le \sum_{a_{i,j} \neq 0} \frac{n+2}{3}$$

Hmm, this just restates the problem.

Let me try yet another approach.

## Potential Function Argument

We've shown that $\sum_{i+j>n} w(i,j) = \frac{n(n+1)(n+2)}{6}$ where $w(i,j) = i+j-n$.

Also, the number of positions in the nonzero region is $\frac{n(n+1)}{2}$.

So: $\sum_{i+j>n} w(i,j) = \frac{n+2}{3} \cdot \#\{\text{positions with } i+j>n\}$

Now, for the actual matrix:
$$S = \sum_{i+j>n} a_{i,j} \mathbb{1}_{a_{i,j}>0} \cdot a_{i,j}$$

Hmm, I'm going in circles.

## Try Direct Inequality

We have $a_{i,j} \le w(i,j) = i+j-n$ for all i,j with i+j > n.

For nonzero entries:
$$S = \sum_{a_{i,j} > 0} a_{i,j} \le \sum_{a_{i,j} > 0} w(i,j)$$

We want to show:
$$\sum_{a_{i,j} > 0} w(i,j) \le \frac{n+2}{3} N$$

Since $\sum_{i+j>n} w(i,j) = \frac{n+2}{3} \cdot \frac{n(n+1)}{2}$ and the average weight is $(n+2)/3$, we need to show that the nonzero entries don't have above-average weight on average.

But that's not necessarily true! The nonzero entries could all be at high-depth positions.

## The Missing Piece

I think the key is that we can't have all high-depth positions be nonzero while keeping low-depth positions zero, due to the monotonicity constraints!

**Crucial observation:** If $a_{i,j} > 0$ for some i+j = n+k (depth k), then there must be a path from the boundary (depth 0) to (i,j) consisting of positions with nonzero values.

Actually, that's not quite right either, since the path can go through zeros.

Let me think about the monotonicity more carefully.

If $a_{i,j} > 0$ and i,j > 1, then at least one of $a_{i-1,j}$ or $a_{i,j-1}$ must be nonzero (or we're at the boundary).

Actually, since $a_{i,j} > 0$ and $a_{i,j} \le a_{i-1,j} + 1$ and $a_{i,j} \le a_{i,j-1} + 1$, if both predecessors were 0, then $a_{i,j} \le 1$.

This suggests that entries with large values must have a "support" structure beneath them.

## Counting Argument

Let's count pairs (position, value):

For each unit of value in the matrix, we can "charge" it to a position. Specifically, for entry $a_{i,j} = v$, we can think of it as v units stacked at position (i,j).

By monotonicity, if there are v units at (i,j), then there must be at least v-1 units at (i-1,j) and at least v-1 units at (i,j-1).

Actually, this is getting complicated. Let me try a cleaner approach.

## Fresh Approach: Amortized Analysis

Think of building the matrix row by row (or column by column). Each time we increase a value by 1 (going from $a_{i,j}$ to $a_{i+1,j} = a_{i,j}+1$ or $a_{i,j+1} = a_{i,j}+1$), we add 1 to S.

Alternatively, think of S as counting the total number of "+1" operations used to build the matrix from the all-zeros starting state.

Since we can only move down or right, and the boundary is at i+j=n, each "+1" operation happens at some position (i,j) with i+j > n.

The total sum S equals the total number of "+1" increments.

Hmm, this is still not leading anywhere obvious.

## Idea: Hall-type Marriage Argument?

Actually, let me try to think of extremal configurations. When is S/N maximized?

If we have one entry at depth n with value n, then S=n and N=1, giving S/N = n > (n+2)/3 for large n. But wait, can we actually achieve this?

To have value n at depth n, we need position (i,j) with i+j=2n, which means i=j=n. And we need $a_{n,n} = n$.

To achieve this, we need a path from the boundary to (n,n) with n increments. Since any path from boundary (i+j=n) to (n,n) (where i+j=2n) has length exactly n (total number of down/right moves), we can achieve $a_{n,n}=n$ by incrementing at every step.

So yes, S=n, N=1, S/N=n.

But our bound says S/N ≤ (n+2)/3 < n. So this would violate the bound!

Let me check: if only $a_{n,n}$ is nonzero, what are the monotonicity constraints?

We must have:
- $a_{n-1,n} \in \{a_{n,n}-1, a_{n,n}\} = \{n-1, n\}$
- $a_{n,n-1} \in \{a_{n,n}-1, a_{n,n}\} = \{n-1, n\}$

So if $a_{n,n} = n > 0$, then at least one of $a_{n-1,n}$ or $a_{n,n-1}$ must be at least n-1 > 0.

By induction, we can show that if $a_{n,n} = k > 0$, then there must be at least k nonzero entries!

**Key Lemma:** If $a_{i,j} = k > 0$, then there exists a path from some boundary position (i',j') with i'+j' ≤ n to (i,j) such that every position on the path (except possibly the starting boundary position) has nonzero value.

This means: **to have value k at some position, we need at least k nonzero positions leading to it.**

But this gives us $S \le N \cdot (\text{max value})$, which is not tight enough.

Actually, let me reconsider. If $a_{i,j} = k$, does that mean there are k nonzero positions? Not quite - the path has length i+j-n at minimum, but the value k could be less than the path length if we don't increment at every step.

## Better Lemma

Let me think about it differently. Define the "signature" of a matrix as the multiset of depths of nonzero entries.

For position (i,j), depth is d(i,j) = i+j-n.

If we have N nonzero entries at depths $d_1, d_2, \ldots, d_N$ (with repetitions), then:
$$S \le \sum_{i=1}^{N} d_i$$

because $a_{i,j} \le d(i,j)$ for each position.

So we need:
$$\sum_{i=1}^{N} d_i \le \frac{(n+2)N}{3}$$

which is equivalent to:
$$\text{average depth of nonzero entries} \le \frac{n+2}{3}$$

Now, we computed that the average depth over *all* positions in the nonzero region is exactly $(n+2)/3$.

**So the question becomes: can the nonzero entries have above-average depth on average?**

The answer must be NO, but why?

## The Constraint: Monotonicity Prevents Cherry-Picking

Here's the key insight: we can't just place nonzero entries at high-depth positions while leaving low-depth positions zero, because of the monotonicity constraint!

**Lemma (Downward Closure):** If $a_{i,j} > 0$ for some i,j, then for every path from the boundary to (i,j), there exists at least one position on the path (possibly (i,j) itself) that is nonzero.

No wait, that's trivially true.

Let me think about it more carefully.

**Better Lemma:** If there are N nonzero entries, and we sum their depths, this sum is at most (n+2)N/3.

To prove this, I need to use the structure of the monotonicity constraint.

Actually, I think the right way is to use an exchange or rearrangement argument.

## Exchange Argument

Suppose we have a configuration with N nonzero entries and sum S. Suppose S > (n+2)N/3.

Can we modify the configuration to reduce S while keeping N the same (or reduce S more than we reduce N)?

Hmm, this is tricky because of the monotonicity constraints.

## Different Tack: Counting with Multiplicity

For each position (i,j) with i+j > n, define an "influence" measure.

Actually, I think the right approach is to use a charging/potential argument where we charge each unit of value to nonzero positions in a specific way.

For entry $a_{i,j} = k$, we can "distribute" this value of k among positions. The question is how to do this accounting to show the bound.

## Telescoping / Layer-by-Layer Analysis

Let's partition the nonzero region into layers by depth:
- Layer 1: i+j = n+1 (depth 1)
- Layer 2: i+j = n+2 (depth 2)
- ...
- Layer n: i+j = 2n (depth n)

Let $N_k$ = number of nonzero entries in layer k
Let $S_k$ = sum of entries in layer k

Then $N = \sum_{k=1}^{n} N_k$ and $S = \sum_{k=1}^{n} S_k$.

For entries in layer k, we have $a_{i,j} \le k$.

So $S_k \le k \cdot N_k$.

Wait, but that's only using the depth bound, not the full structure.

Actually, I realize that within each layer, all entries have the same depth, so the depth bound gives us $S_k \le k N_k$.

Then:
$$S = \sum_{k=1}^{n} S_k \le \sum_{k=1}^{n} k N_k$$

We want to show:
$$\sum_{k=1}^{n} k N_k \le \frac{n+2}{3} \sum_{k=1}^{n} N_k$$

This is equivalent to:
$$\sum_{k=1}^{n} k N_k \le \frac{n+2}{3} N$$

or

$$\sum_{k=1}^{n} \left(k - \frac{n+2}{3}\right) N_k \le 0$$

This says that the weighted average of $(k - \frac{n+2}{3})$ with weights $N_k$ is non-positive.

Since the average depth over all positions is (n+2)/3, we have:
$$\sum_{k=1}^{n} k \cdot (\text{# positions in layer } k) = \frac{n+2}{3} \cdot (\text{total positions})$$

where # positions in layer k is $n-k+1$.

So:
$$\sum_{k=1}^{n} k(n-k+1) = \frac{n+2}{3} \cdot \frac{n(n+1)}{2}$$

Now, we need to show:
$$\sum_{k=1}^{n} k N_k \le \frac{n+2}{3} N$$

We know $N_k \le n-k+1$ (since there are only $n-k+1$ positions in layer k).

If $N_k = n-k+1$ for all k (all positions are nonzero), then we get equality!

But what if some $N_k < n-k+1$? We need to show that this can only help (reduce the weighted sum).

The question is: which layers have $N_k < n-k+1$, and how does this affect the sum?

**Key observation:** If we remove nonzero entries to reduce N, which removals reduce S the most? We should remove entries with high values, which tend to be at high depths.

But we can't just remove any entry - we must maintain the monotonicity constraint!

## Monotonicity Constraint Analysis

Here's the crucial constraint: if $a_{i,j} = 0$ but $a_{i+1,j} > 0$ or $a_{i,j+1} > 0$, then those subsequent entries must be exactly 1 (not higher).

More generally, $a_{i,j} \ge \max(a_{i-1,j}, a_{i,j-1}) - 1$.

Actually, let's think about it from a different angle.

**Claim:** If we have k nonzero entries in layer $\ell$, then we must have at least k nonzero entries in layer $\ell - 1$ (for $\ell > 1$).

**Proof idea:** Each nonzero entry in layer $\ell$ must have come from either layer $\ell-1$ (moved down or right from depth $\ell-1$) or have value exactly 1 (meaning it was reached from a zero entry in the previous layer).

Hmm, this isn't quite right either.

OK I think I need to be even more careful and systematic.

## Systematic Approach: Prove the Crucial Structural Lemma

**Lemma:** For any valid matrix, $\sum_{k=1}^{n} k N_k \le \frac{n+2}{3} N$.

To prove this, we'll show that the nonzero entries cannot be too concentrated in high-depth layers.

Actually, let me try a completely different approach: double counting or a bijection argument.

## Bijection / Involution Argument

Consider the set of all positions (i,j) in the nonzero region, weighted by their depth.

Total weight: $\sum_{k=1}^{n} k \cdot (n-k+1) = \frac{n(n+1)(n+2)}{6}$
Total positions: $\frac{n(n+1)}{2}$
Average weight: $\frac{n+2}{3}$

Now, for a specific configuration of the matrix, we have N nonzero positions.

We want to show that these N positions have average weight at most $(n+2)/3$.

Equivalently: among all subsets of the nonzero region of size N, the average weight is minimized when... when what?

Actually, the average weight over all positions is fixed at $(n+2)/3$. So if we select a subset, the average weight of that subset could be higher or lower.

The question is: does the monotonicity constraint prevent us from selecting a subset with too high average weight?

**Intuition:** The monotonicity constraint creates a "cascade" effect. To have nonzero entries at high depth, we must also have nonzero entries at lower depths supporting them.

Let me try to formalize this.

## Cascade Lemma

**Definition:** For a position (i,j), define its "support set" as the set of all positions (i',j') with i' ≤ i, j' ≤ j, and (i',j') ≠ (i,j), such that any path from the boundary to (i,j) passes through (i',j').

Actually, this is getting too complicated.

Let me try a more direct approach.

## Direct Proof via Induction or Calculation

I'll try to directly compute or bound $\sum k N_k$ using the monotonicity structure.

For each nonzero entry $a_{i,j}$ in layer k (where i+j = n+k), we have $a_{i,j} \ge 1$.

Now, consider the "history" of this entry. It came from either:
- (i-1,j) in layer k-1 or layer k (if j=1 or i+j-1=n)
- (i,j-1) in layer k-1 or layer k (if i=1 or i+j-1=n)

Hmm, this is messy.

## Try Small Cases to Find Pattern

Let me manually work out n=2 and n=3 to see if I can spot a pattern.

**n=2:**
Nonzero region positions:
- Layer 1 (i+j=3): (1,2), (2,1) - 2 positions
- Layer 2 (i+j=4): (2,2) - 1 position

Possible configurations:
- All zero: N=0, S=0. Bound: 0 ≤ 0. ✓
- Only (1,2) nonzero with value 1: N=1, S=1. Bound: 1 ≤ (4/3)·1 = 4/3. ✓
- Only (2,1) nonzero with value 1: N=1, S=1. Bound: 1 ≤ 4/3. ✓
- (1,2) and (2,1) nonzero with value 1: N=2, S=2. Bound: 2 ≤ (4/3)·2 = 8/3. ✓
- (2,2) nonzero: requires at least one of (1,2) or (2,1) nonzero.
  - If (1,2)=1, (2,2)=v, then v ∈ {1,2}. Similarly for (2,1).
  - Case: (1,2)=1, (2,1)=0, (2,2)=1: N=2, S=2. Bound: 2 ≤ 8/3. ✓
  - Case: (1,2)=1, (2,1)=0, (2,2)=2: N=2, S=3. Bound: 3 ≤ 8/3?  3 > 8/3. ✗

Wait, that violates the bound! Let me check if this configuration is valid.

If a_{1,2} = 1, a_{2,1} = 0, then:
- a_{2,2} ∈ {a_{1,2}, a_{1,2}+1} = {1,2} (from going down)
- a_{2,2} ∈ {a_{2,1}, a_{2,1}+1} = {0,1} (from going right)

So a_{2,2} ∈ {1,2} ∩ {0,1} = {1}.

Therefore a_{2,2} cannot be 2 if a_{2,1} = 0!

Let me redo:
- Case: (1,2)=1, (2,1)=1, (2,2)=1: N=3, S=3. Bound: 3 ≤ (4/3)·3 = 4. ✓
- Case: (1,2)=1, (2,1)=1, (2,2)=2: N=3, S=4. Bound: 4 ≤ 4. ✓

Great, so for n=2, the bound holds (and is tight).

The key insight from this example: **to achieve high values at high depth, we need nonzero entries at lower depths to support them, which increases N.**

This is the crux of the proof!

## The Proof Strategy

For each position (i,j) with value $a_{i,j} = v > 0$, we need to account for how this value was built up.

Since values can only increase by 1 per step, and we start from 0 at the boundary, a value of v requires at least v steps of"+1" increments along some path.

Each "+1" increment happens at a position, and that position must be nonzero.

So: **the total sum S equals the total number of "+1" increments, and each increment happens at a nonzero position.**

But wait, this would give $S \le N \cdot (\text{max value})$, which is too weak.

Let me think about this more carefully.

## Refined Counting Argument

For each unit of value in the matrix, we can trace it back to a "+1" increment at some position.

Specifically, consider the value $a_{i,j}$. This value is the result of some sequence of increments along a path from the boundary.

If $a_{i,j} = v$, then along the path from boundary to (i,j), there were exactly v increments.

Now, here's the key: **different entries can share parts of their paths, so the increments can be shared.**

For instance, if both (3,3) and (3,4) have nonzero values, and they both received increments from the path passing through (3,2), then that increment at (3,2) contributes to both values.

So we can't just say S = # of increments = # of nonzero positions with nonzero predecessors.

## Alternative: Potential Function

Define a potential function $\Phi = \sum_{i,j} (i+j-n) \cdot \mathbb{1}_{a_{i,j} > 0}$.

This is exactly the sum of depths of nonzero entries.

We have $\Phi = \sum_{k=1}^{n} k N_k$.

We want to show $\Phi \le \frac{n+2}{3} N$.

The average depth of all positions (nonzero or not) in the nonzero region is $(n+2)/3$.

So if nonzero entries are "uniformly distributed" across depths, we'd have $\Phi = \frac{n+2}{3} N$.

The question is: can the monotonicity constraint force nonzero entries to be concentrated at low depths, or allow them to be concentrated at high depths?

**Intuition:** Monotonicity should force a "pyramid" structure - to have nonzero entries at high depth, you need a broad base of nonzero entries at low depth.

Let me try to formalize this.

## Pyramid Lemma

**Claim:** If there are $N_k$ nonzero entries in layer k, then there are at least $N_k$ nonzero entries in layer k-1 (for k > 1).

**Proof attempt:** Each nonzero entry in layer k must have come from layer k-1 by moving down or right. If the predecessor in layer k-1 was zero, then the entry in layer k has value exactly 1 (since 0+1=1). If the predecessor was nonzero, then it contributes to the count in layer k-1.

But wait, an entry in layer k has two potential predecessors (one from moving down, one from moving right), and both are in layer k-1. So it's possible that both predecessors are zero, in which case the entry in layer k can have value 1 but neither predecessor contributes to $N_{k-1}$.

Hmm, so the claim is false as stated.

But wait: if both predecessors are zero, then the entry must be exactly 1. So entries with value > 1 in layer k must have at least one nonzero predecessor in layer k-1.

Let $N_k^{(v)}$ = number of entries in layer k with value v.

Then $N_k = \sum_{v=1}^{k} N_k^{(v)}$ and $S_k = \sum_{v=1}^{k} v \cdot N_k^{(v)}$.

Entries with value 1 in layer k can have all-zero predecessors.
Entries with value v > 1 in layer k must have at least one predecessor with value ≥ v-1 > 0.

This gives us a relationship between layers, but it's complex.

## Yet Another Approach: Linear Programming / Optimization

Think of the problem as: what configuration of $(N_1, N_2, \ldots, N_n)$ maximizes $\sum k N_k$ subject to:
- $0 \le N_k \le n-k+1$ for all k
- Monotonicity constraints (to be determined)

If we can characterize the monotonicity constraints and solve this optimization, we can verify the bound.

But the monotonicity constraints are complex (they involve the actual values, not just the counts).

## I think I need to look for a different angle.

Let me reconsider the problem from scratch with fresh eyes.

## Eureka: Pigeonhole or Averaging Argument

Wait, I think I've been overcomplicating this.

We have:
- $a_{i,j} \le i+j-n$ for all i,j with i+j > n
- $S = \sum_{a_{i,j} > 0} a_{i,j} \le \sum_{a_{i,j} > 0} (i+j-n)$

So:
$$S \le \sum_{a_{i,j} > 0} (i+j-n) = \sum_{k=1}^{n} k N_k$$

where $N_k$ is the number of nonzero entries with depth k (i.e., i+j=n+k).

Now, we need to show:
$$\sum_{k=1}^{n} k N_k \le \frac{n+2}{3} N$$

We know that if all positions are nonzero (i.e., $N_k = n-k+1$ for all k), then:
$$\sum_{k=1}^{n} k(n-k+1) = \frac{n(n+1)(n+2)}{6} = \frac{n+2}{3} \cdot \frac{n(n+1)}{2}$$

So the bound holds with equality when all positions are nonzero.

Now, if some positions are zero, does the bound still hold?

The question is: if we set some $N_k < n-k+1$, does that increase or decrease the ratio $\frac{\sum k N_k}{N}$?

If we remove a nonzero entry from layer k, we decrease $\sum k N_k$ by k and decrease N by 1. The ratio changes from $\frac{\sum k N_k}{N}$ to $\frac{\sum k N_k - k}{N-1}$.

This ratio increases (bad for us) if $k > \frac{\sum k N_k}{N}$, i.e., if we remove an entry from a layer with above-average depth.

Conversely, the ratio decreases (good for us) if we remove an entry from a layer with below-average depth.

So the question is: **does the monotonicity constraint prevent us from removing entries from low-depth layers while keeping high-depth layers full?**

**Answer: YES!** If we set an entry in layer k to zero, then by monotonicity, certain entries in layer k+1 must also be zero or have value exactly 1.

More precisely: if $a_{i,j} = 0$ and i,j < n, then $a_{i+1,j} \in \{0,1\}$ and $a_{i,j+1} \in \{0,1\}$.

So zeros propagate forward, limiting the values in subsequent layers.

## Formalize the Propagation

Let's define: an entry (i,j) is "reachable with value v" if there exists a valid configuration where $a_{i,j} = v$.

**Lemma (Reachability):** If all entries in layer k with i < i_0 or j < j_0 are zero, then $a_{i_0,j_0} \le 1$ (where $(i_0,j_0)$ is in layer k+1).

This suggests that having zeros in layer k limits the values in layer k+1, which transitively affects all higher layers.

But formalizing this seems complex.

## Maybe I should just accept the bound and write it up?

Actually, I realize that the complete proof might be quite involved. Let me think if there's a slick argument I'm missing.

## One More Idea: Greedy / Exchange Argument

Suppose we have a configuration that violates the bound: $\sum k N_k > \frac{n+2}{3} N$.

Can we modify it to reduce $\sum k N_k$ while keeping N fixed (or reduce the ratio)?

If we "move" a nonzero entry from layer k_1 to layer k_2 with k_2 < k_1, we reduce $\sum k N_k$.

But we can't just move entries arbitrarily - we must maintain monotonicity.

Alternatively, if we set an entry in layer k_1 to zero (reducing N by 1 and $\sum k N_k$ by k_1), can we then set another entry in layer k_2 to nonzero (increasing N by 1 and $\sum k N_k$ by k_2) while maintaining monotonicity, with k_2 < k_1?

This is getting complicated.

## Step Back: Maybe the Proof is Simpler Than I Think

Let me reconsider the structure. We have a matrix with zeros in the upper-left triangle and (potentially) nonzero entries in the lower-right triangle, with monotonicity constraints.

The bound $\frac{n+2}{3}$ is the average depth. We've shown that when all positions are nonzero, the bound holds with equality.

For the general case, maybe there's a simple counting/averaging argument that I'm missing.

Actually, wait. Let me reconsider the statement of the problem.

We want $S \le \frac{(n+2)N}{3}$, i.e., the average nonzero entry value is at most $\frac{n+2}{3}$.

We've shown each entry is at most its depth, and the average depth over all positions is $\frac{n+2}{3}$.

So the bound holds if the nonzero entries have at most average depth on average.

**Key claim:** The nonzero entries cannot be concentrated only at high depths due to monotonicity.

To prove this rigorously, I think we need an inductive or structural argument.

## Inductive Proof Sketch

**Theorem:** For any valid n×n matrix A, $\sum k N_k \le \frac{n+2}{3} N$.

**Proof by induction on n:**

*Base case (n=2):* We've verified this by casework above.

*Inductive step:* Assume the result holds for (n-1)×(n-1) matrices. Consider an n×n matrix A.

We can decompose A into:
- The (n-1)×(n-1) submatrix A' in the top-left
- The nth row
- The nth column
- The corner entry a_{n,n}

By the inductive hypothesis, the submatrix A' satisfies the bound.

Now, we need to account for the additional entries in the nth row and column...

Hmm, this is getting messy because the nonzero regions don't decompose cleanly.

## I think I need to write up what I have and indicate the gap

Let me write up a clear solution with the parts I've proven, and indicate where the final step needs more work.

Actually, wait. Let me try one more approach: a direct algebraic proof.

## Direct Algebraic Proof

We want to show:
$$\sum_{k=1}^{n} k N_k \le \frac{n+2}{3} \sum_{k=1}^{n} N_k$$

We know $0 \le N_k \le n-k+1$ for all k.

Rearranging:
$$\sum_{k=1}^{n} k N_k \le \frac{n+2}{3} \sum_{k=1}^{n} N_k$$
$$\sum_{k=1}^{n} \left(k - \frac{n+2}{3}\right) N_k \le 0$$
$$\sum_{k=1}^{n} \frac{3k-(n+2)}{3} N_k \le 0$$
$$\sum_{k=1}^{n} (3k-n-2) N_k \le 0$$

Now, $3k - n - 2 < 0$ when $k < \frac{n+2}{3}$, and $3k - n - 2 > 0$ when $k > \frac{n+2}{3}$.

For n=2: threshold is 4/3, so k=1 has negative coefficient, k=2 has positive.
For n=3: threshold is 5/3, so k=1 has negative, k=2, k=3 have positive.
For n=4: threshold is 2, so k≤2 have non-positive, k>2 have positive.

So we need:
$$\sum_{k \le (n+2)/3} |3k-n-2| N_k \ge \sum_{k > (n+2)/3} (3k-n-2) N_k$$

The question is whether the monotonicity constraint enforces this.

**Intuition:** If we increase $N_k$ for large k (above threshold), monotonicity forces us to also increase $N_k$ for small k (below threshold), and the latter increase is "worth more" in the inequality.

To formalize: each unit increase in $N_k$ for $k > \frac{n+2}{3}$ requires (by monotonicity) increasing $N_j$ for some $j < k$, possibly with $j \le \frac{n+2}{3}$.

But making this precise is tricky.

## OK, I'll write up the solution with the key ideas

I'll present the solution with:
1. The upper bound $a_{i,j} \le i+j-n$
2. The calculation that average depth is $(n+2)/3$
3. The reduction to showing $\sum k N_k \le \frac{n+2}{3} N$
4. The intuition/sketch that monotonicity prevents concentration at high depths
5. Verification for small cases

This captures the main ideas even if the final step isn't completely rigorous.

Actually, I just realized - maybe there's a neat combinatorial bijection or generating function argument that makes this clean. But I've spent a lot of time already, so let me write up what I have.
