# Rigorous Proof for Putnam 2025 B6

## Problem
Find the largest real constant $r$ such that there exists $g: \mathbb{N} \to \mathbb{N}$ with
$$g(n+1) - g(n) \geq (g(g(n)))^r \text{ for all } n \in \mathbb{N}.$$

## Strategy for Rigorous Proof

The asymptotic argument is not rigorous because:
1. It assumes $g(n) \sim n^\alpha$ without justification
2. It doesn't prove that non-polynomial functions can't do better
3. The "$\sim$" notation is imprecise for a rigorous proof

### What we need to prove:

1. **Construction:** There exists $g$ with $r = 1/4$ (this part is easy)
2. **Optimality:** For any $r > 1/4$ and any $g: \mathbb{N} \to \mathbb{N}$, the constraint fails for some $n$

### Key Ideas for Rigorous Upper Bound

**Approach 1: Direct analysis of growth rates**

Define $h(n) = \ln g(n)$. Then:
- $g(n+1) - g(n) \geq (g(g(n)))^r$
- Taking logs (assuming $g(n+1) - g(n) \geq 1$):
  - $\ln(g(n+1) - g(n)) \geq r \ln g(g(n))$
  - $\ln(g(n+1) - g(n)) \geq r h(g(n))$

**Approach 2: Lower bound on $g$ from the constraint**

From $g(n+1) - g(n) \geq (g(g(n)))^r$, summing:
$$g(n) \geq g(1) + \sum_{k=1}^{n-1} (g(g(k)))^r$$

If $g$ is increasing (necessary for $g: \mathbb{N} \to \mathbb{N}$ to be unbounded), then $g(g(k))$ is also increasing.

**Approach 3: Upper bound on $g$ from injectivity**

For $g: \mathbb{N} \to \mathbb{N}$ to satisfy the constraint, we need:
- $g$ must be unbounded (otherwise $g(g(n))$ is bounded, making RHS bounded, but LHS must sum to infinity)
- $g$ should be roughly injective to avoid "wasting" values

**Approach 4: Comparison with specific functions**

Suppose $g(n) \geq cn^\alpha$ for large $n$. Then:
- $g(g(n)) \geq c(cn^\alpha)^\alpha = c^{1+\alpha} n^{\alpha^2}$
- $g(n+1) - g(n)$ is approximately the derivative: $\sim c\alpha n^{\alpha-1}$

For the constraint:
$$c\alpha n^{\alpha-1} \geq (c^{1+\alpha} n^{\alpha^2})^r$$
$$c\alpha n^{\alpha-1} \geq c^{r(1+\alpha)} n^{r\alpha^2}$$

For large $n$, we need: $\alpha - 1 \geq r\alpha^2$

So: $r \leq \frac{\alpha-1}{\alpha^2}$

This is maximized at $\alpha = 2$, giving $r \leq 1/4$.

**But this is still not rigorous!** We need to prove:
1. Any $g$ satisfying the constraint must have $g(n) \geq cn^\alpha$ for some constants
2. The above analysis actually rules out all functions, not just polynomial ones

### Rigorous Approach: Discrete Iteration Bounds

Let me try a different approach using discrete sums and careful estimates.

**Claim:** If $g: \mathbb{N} \to \mathbb{N}$ satisfies $g(n+1) - g(n) \geq (g(g(n)))^r$ for all $n$, and $r > 1/4$, then $g$ cannot be unbounded.

**Proof idea:**
1. Show that if $g$ is unbounded, it must grow at least polynomially
2. Show that polynomial growth forces $r \leq 1/4$
3. Show that faster-than-polynomial growth makes the constraint fail

Let me work this out more carefully...
