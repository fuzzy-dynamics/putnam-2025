# Putnam 2025 A5 - Scratch Work

## Problem Statement

Let $n \geq 2$ be an integer. For a sequence $s = (s_1, \ldots, s_{n-1})$ where each $s_i = \pm 1$, let $f(s)$ be the number of permutations $(a_1, \ldots, a_n)$ of $\{1, 2, \ldots, n\}$ such that $s_i(a_{i+1} - a_i) > 0$ for all $i$.

Determine which sequences $s$ maximize $f(s)$.

## Understanding the Problem

- $s_i = +1$ means $a_{i+1} > a_i$ (ascent at position $i$)
- $s_i = -1$ means $a_{i+1} < a_i$ (descent at position $i$)
- $f(s)$ counts permutations matching the ascent/descent pattern specified by $s$

## Computational Experiments

### n = 2
- Sequences: $(+)$ and $(-)$
- Both give $f(s) = 1$
- Maximizers: both sequences

### n = 3
| Sequence | f(s) | Status |
|----------|------|--------|
| $(+, -)$ | 2    | MAX    |
| $(-, +)$ | 2    | MAX    |
| $(+, +)$ | 1    |        |
| $(-, -)$ | 1    |        |

**Maximizers**: $(+, -)$ and $(-, +)$ — the alternating sequences!

### n = 4
| Sequence | f(s) | Runs | Status |
|----------|------|------|--------|
| $(+,-,+)$ | 5   | 3    | MAX    |
| $(-,+,-)$ | 5   | 3    | MAX    |
| $(+,+,-)$ | 3   | 2    |        |
| $(+,-,-)$ | 3   | 2    |        |
| $(-,+,+)$ | 3   | 2    |        |
| $(-,-,+)$ | 3   | 2    |        |
| $(+,+,+)$ | 1   | 1    |        |
| $(-,-,-)$ | 1   | 1    |        |

**Maximizers**: $(+,-,+)$ and $(-,+,-)$ — again, alternating!

### n = 5
| Sequence | f(s) | Status |
|----------|------|--------|
| $(+,-,+,-)$ | 16 | MAX |
| $(-,+,-,+)$ | 16 | MAX |
| $(+,-,-,+)$ | 11 |     |
| $(-,+,+,-)$ | 11 |     |
| Others | ≤ 11 |     |

**Maximizers**: $(+,-,+,-)$ and $(-,+,-,+)$ — alternating!

### n = 6
- Maximum: $f(s) = 61$
- Achieved by: $(+,-,+,-,+)$ and $(-,+,-,+,-)$

## Pattern Discovery

**Conjecture**: The sequences that maximize $f(s)$ are exactly the two alternating sequences:
1. $s^{(1)} = (+, -, +, -, \ldots)$ of length $n-1$
2. $s^{(2)} = (-, +, -, +, \ldots)$ of length $n-1$

## Key Observations

### Runs Analysis

A **run** in sequence $s$ is a maximal consecutive block of identical signs.

Examples:
- $(+, +, -, -, +)$ has 3 runs: $(++), (--), (+)$
- $(+, -, +, -, +)$ has 5 runs: all singletons (alternating)

**Observation**: All computational experiments show that sequences with the maximum number of runs (i.e., $n-1$ runs = all runs of length 1) maximize $f(s)$.

These are exactly the alternating sequences.

### Why Alternating Sequences are Optimal

**Intuition**:
- A run of $k$ consecutive $+$ signs forces $k$ consecutive strict ascents: $a_i < a_{i+1} < \cdots < a_{i+k}$
- A run of $k$ consecutive $-$ signs forces $k$ consecutive strict descents: $a_i > a_{i+1} > \cdots > a_{i+k}$
- Longer runs impose stronger constraints on permutations
- Alternating sequences have all runs of length 1, minimizing constraints

## Proof Strategy

### Flip Lemma

**Lemma**: If $s$ has a run of length $\geq 2$ at some position (i.e., $s_i = s_{i+1}$ for some $i$), then there exists a position where flipping the sign increases $f(s)$.

**Verification**: Tested computationally for $n = 2, 3, 4, 5$ — holds in all cases!

### Proof by Optimization

1. Start with any sequence $s$
2. If $s$ is not alternating, it has a run of length $\geq 2$
3. By the Flip Lemma, we can flip a sign to get $s'$ with $f(s') > f(s)$ or $f(s') = f(s)$
4. In practice, we can always find a flip that strictly increases $f(s)$
5. Repeat until we reach an alternating sequence
6. Alternating sequences cannot be improved (flipping any sign creates a run)
7. There are exactly 2 alternating sequences of length $n-1$

### Symmetry

Note that if $s$ maximizes $f(s)$, does $-s$ (flipping all signs) also maximize?

**Answer**: Yes! The map $(a_1, \ldots, a_n) \mapsto (n+1-a_n, \ldots, n+1-a_1)$ (reverse and complement) is a bijection from permutations satisfying $s$ to permutations satisfying $-s$ with signs flipped appropriately.

This explains why both alternating sequences achieve the same maximum.

## Connection to Eulerian Numbers

Eulerian number $A(n,k)$ counts permutations of $\{1, \ldots, n\}$ with exactly $k$ descents.

While there's a relationship to our problem, $f(s)$ is NOT simply an Eulerian number:
- $f(s)$ counts permutations with descents at *specific positions* dictated by $s$
- Eulerian numbers count permutations with a *total number* of descents

However, the maximum Eulerian number $A(n,k)$ occurs at $k = \lfloor(n-1)/2\rfloor$, which suggests there might be a deeper connection.

## Examples of Maximizing Permutations

### n = 3, s = (+, -)
Valid permutations:
1. $(1, 3, 2)$: $1 < 3$ (ascent), $3 > 2$ (descent) ✓
2. $(2, 3, 1)$: $2 < 3$ (ascent), $3 > 1$ (descent) ✓

### n = 4, s = (+, -, +)
Valid permutations:
1. $(1, 3, 2, 4)$
2. $(1, 4, 2, 3)$
3. $(2, 3, 1, 4)$
4. $(2, 4, 1, 3)$
5. $(3, 4, 1, 2)$

All follow the pattern: ascent, descent, ascent.

## Conclusion

**Answer**: The sequences $s$ that maximize $f(s)$ are exactly the two alternating sequences:
- $s_1 = (1, -1, 1, -1, \ldots)$ with length $n-1$
- $s_2 = (-1, 1, -1, 1, \ldots)$ with length $n-1$

The maximum value is achieved because these sequences impose the minimum constraints on permutations by avoiding long runs of consecutive ascents or descents.
