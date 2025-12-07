# Putnam 2025 B6 - Scratch Work

## Problem
Find the largest real constant $r$ such that there exists a function $g:\mathbb{N}\to\mathbb{N}$ such that
$$g(n+1)-g(n)\geq(g(g(n)))^r$$
for all $n\in\mathbb{N}$.

## Initial Analysis

### Case 1: g(n) = n (identity)
- $g(n+1) - g(n) = (n+1) - n = 1$
- $g(g(n)) = g(n) = n$
- Constraint: $1 \geq n^r$

For large $n$, this fails for any $r > 0$. So identity doesn't work.

### Case 2: g(n) = cn for constant c > 1
- $g(n+1) - g(n) = c(n+1) - cn = c$
- $g(g(n)) = g(cn) = c^2n$
- Constraint: $c \geq (c^2n)^r = c^{2r}n^r$

For large $n$, this requires $r = 0$ (or $c \geq c^{2r}n^r$ fails).

### Case 3: Polynomial growth g(n) ~ n^\alpha

Let's analyze more carefully. Suppose $g(n) \approx n^\alpha$ for some $\alpha > 1$.

Then:
- $g(n+1) - g(n) \approx \alpha n^{\alpha-1}$ (by derivative approximation)
- $g(g(n)) \approx g(n^\alpha) \approx (n^\alpha)^\alpha = n^{\alpha^2}$

The constraint becomes:
$$\alpha n^{\alpha-1} \gtrsim (n^{\alpha^2})^r = n^{r\alpha^2}$$

For this to hold for large $n$, we need:
$$\alpha - 1 \geq r\alpha^2$$
$$r \leq \frac{\alpha - 1}{\alpha^2}$$

## Finding the Maximum r

To maximize $r$, we need to maximize $f(\alpha) = \frac{\alpha - 1}{\alpha^2}$ for $\alpha > 1$.

$$f'(\alpha) = \frac{\alpha^2 - (\alpha-1) \cdot 2\alpha}{\alpha^4} = \frac{\alpha^2 - 2\alpha^2 + 2\alpha}{\alpha^4} = \frac{-\alpha^2 + 2\alpha}{\alpha^4} = \frac{\alpha(2-\alpha)}{\alpha^4} = \frac{2-\alpha}{\alpha^3}$$

Setting $f'(\alpha) = 0$: $2 - \alpha = 0$, so $\alpha = 2$.

At $\alpha = 2$:
$$f(2) = \frac{2-1}{2^2} = \frac{1}{4}$$

Check second derivative to confirm maximum:
- For $\alpha < 2$: $f'(\alpha) > 0$ (increasing)
- For $\alpha > 2$: $f'(\alpha) < 0$ (decreasing)

So $\alpha = 2$ gives a maximum, with $r = \frac{1}{4}$.

## Constructing g with α = 2

We want $g(n) \approx n^2$. Let's try $g(n) = \lceil n^2 \rceil$ or similar.

Actually, let me be more careful. We need:
$$g(n+1) - g(n) \geq (g(g(n)))^{1/4}$$

### Attempt 1: g(n) = n^2

- $g(n+1) - g(n) = (n+1)^2 - n^2 = 2n + 1$
- $g(g(n)) = g(n^2) = (n^2)^2 = n^4$
- $(g(g(n)))^{1/4} = (n^4)^{1/4} = n$

Constraint: $2n + 1 \geq n$ ✓

This works! But we need $g: \mathbb{N} \to \mathbb{N}$, and $g(n) = n^2$ already satisfies this.

Let me verify more carefully for small values:

- $n=1$: $g(2) - g(1) = 4 - 1 = 3 \geq (g(g(1)))^{1/4} = (g(1))^{1/4} = 1^{1/4} = 1$ ✓
- $n=2$: $g(3) - g(2) = 9 - 4 = 5 \geq (g(g(2)))^{1/4} = (g(4))^{1/4} = 16^{1/4} = 2$ ✓
- $n=3$: $g(4) - g(3) = 16 - 9 = 7 \geq (g(g(3)))^{1/4} = (g(9))^{1/4} = 81^{1/4} = 3$ ✓

The pattern holds: $2n+1 \geq n$ for all $n \geq 1$.

## Can we do better than r = 1/4?

Let's check if $r > 1/4$ is possible.

If $r = 1/4 + \epsilon$ for small $\epsilon > 0$, then for $g(n) = n^2$:
$$2n + 1 \geq n^{4(1/4 + \epsilon)} = n^{1 + 4\epsilon} = n \cdot n^{4\epsilon}$$

For large $n$, $n^{4\epsilon}$ grows unbounded, so this fails.

Could we use a different function? If $g(n) \sim n^\alpha$ with $\alpha \neq 2$, we showed that $r \leq \frac{\alpha-1}{\alpha^2}$, which is maximized at $\alpha = 2$.

## Proving r = 1/4 is optimal

We need to show that for any $r > 1/4$, no such function $g$ exists.

Key observation: If $g: \mathbb{N} \to \mathbb{N}$ is strictly increasing (which it must be to satisfy the constraint for large $n$), then:

Let's think about the growth rate. From the recurrence:
$$g(n+1) \geq g(n) + (g(g(n)))^r$$

This means $g$ grows at least as fast as the sum of these increments.

For $g(n) \approx n^\alpha$:
- $g(g(n)) \approx n^{\alpha^2}$
- Increment: $(g(g(n)))^r \approx n^{r\alpha^2}$
- But also: $g(n+1) - g(n) \approx \alpha n^{\alpha-1}$

So we need: $\alpha n^{\alpha-1} \gtrsim n^{r\alpha^2}$

This gives: $\alpha - 1 \geq r\alpha^2$, or $r \leq \frac{\alpha-1}{\alpha^2}$.

The maximum over all $\alpha > 1$ is $\frac{1}{4}$ at $\alpha = 2$.

For subpolynomial or superpolynomial growth, the constraint becomes even tighter.

Therefore, $r = 1/4$ is optimal.
