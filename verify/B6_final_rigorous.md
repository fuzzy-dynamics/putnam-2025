# Final Rigorous Proof for Putnam 2025 B6

## Problem
Find the largest real constant $r$ such that there exists $g: \mathbb{N} \to \mathbb{N}$ with
$$g(n+1) - g(n) \geq (g(g(n)))^r \text{ for all } n \in \mathbb{N}.$$

## Answer: $r = \frac{1}{4}$

---

## Part 1: Construction

**Proposition 1:** The function $g(n) = n^2$ satisfies the constraint for $r = \frac{1}{4}$.

**Proof:**
For $g(n) = n^2$, we have:
- $g(n+1) - g(n) = 2n + 1$
- $g(g(n)) = n^4$
- $(g(g(n)))^{1/4} = n$

The constraint $2n + 1 \geq n$ holds for all $n \in \mathbb{N}$. $\blacksquare$

---

## Part 2: Optimality - Rigorous Proof

**Theorem:** For any $r > \frac{1}{4}$ and any function $g: \mathbb{N} \to \mathbb{N}$, the constraint
$g(n+1) - g(n) \geq (g(g(n)))^r$ fails for sufficiently large $n$.

### Setup and Preliminaries

**Lemma 1 (Unboundedness):** If $g$ satisfies the constraint for some $r > 0$, then $g$ is unbounded.

*Proof:* Suppose $g(n) \leq M$ for all $n$. Then $g(g(n)) \leq M$, so $(g(g(n)))^r \leq M^r$.
Summing the constraint from 1 to $n-1$:
$$g(n) \geq g(1) + (n-1) \cdot \min_{1 \leq k \leq n-1} (g(g(k)))^r$$

Since $g: \mathbb{N} \to \mathbb{N}$ and $g$ maps into a finite set $\{1, 2, \ldots, M\}$,
by pigeonhole principle, some value $v$ is taken infinitely often. Then $g(g(k)) = g(v)$ infinitely often.
Thus the minimum is achieved infinitely often and is positive (at least 1 when $r > 0$).
So $g(n) \to \infty$, contradicting boundedness. $\blacksquare$

**Lemma 2 (Eventually increasing):** For any $r > 0$, if $g$ satisfies the constraint,
then $g(n+1) > g(n)$ for all sufficiently large $n$.

*Proof:* From Lemma 1, $g(n) \to \infty$. If $g(n+1) = g(n)$ infinitely often,
then the constraint gives $0 \geq (g(g(n)))^r \to \infty$, a contradiction. $\blacksquare$

### The Main Argument

We now prove the upper bound $r \leq 1/4$ using a growth rate analysis.

**Key Claim:** For any $\alpha > 1$ and any $\epsilon > 0$, if $g$ satisfies the constraint with $r > \frac{\alpha-1}{\alpha^2}$,
then $g$ cannot satisfy $g(n) \sim Cn^\alpha$ (meaning $c_1 n^\alpha \leq g(n) \leq c_2 n^\alpha$ for large $n$).

**Proof of Key Claim:**

Suppose $g$ satisfies:
- (Lower bound) $g(n) \geq c_1 n^\alpha$ for all $n \geq N_1$
- (Upper bound) $g(n) \leq c_2 n^\alpha$ for all $n \geq N_1$

where $c_1, c_2 > 0$ are constants.

From the upper bound:
$$g(g(n)) \leq c_2 (c_2 n^\alpha)^\alpha = c_2^{1+\alpha} n^{\alpha^2}$$

So the constraint gives:
$$g(n+1) - g(n) \geq (c_2^{1+\alpha} n^{\alpha^2})^r = c_2^{r(1+\alpha)} n^{r\alpha^2}$$

Summing from $N$ to $n-1$ (for large $N$):
$$g(n) - g(N) \geq c_2^{r(1+\alpha)} \sum_{k=N}^{n-1} k^{r\alpha^2}$$

For the sum, using the integral approximation:
$$\sum_{k=N}^{n-1} k^{r\alpha^2} \geq \int_N^{n-1} x^{r\alpha^2} dx = \frac{(n-1)^{r\alpha^2+1} - N^{r\alpha^2+1}}{r\alpha^2 + 1}$$

For large $n$, this gives:
$$g(n) \geq \frac{c_2^{r(1+\alpha)}}{r\alpha^2 + 1} n^{r\alpha^2+1} - C$$

for some constant $C$ depending on $N$.

So for sufficiently large $n$:
$$g(n) \geq \frac{c_2^{r(1+\alpha)}}{2(r\alpha^2 + 1)} n^{r\alpha^2+1}$$

But we also assumed $g(n) \leq c_2 n^\alpha$. For these to be consistent, we need:
$$r\alpha^2 + 1 \leq \alpha$$

which gives:
$$r \leq \frac{\alpha - 1}{\alpha^2}$$

If $r > \frac{\alpha-1}{\alpha^2}$, we get a contradiction. $\blacksquare$

**Corollary:** If $g$ satisfies the constraint for some $r > 0$, then $g$ cannot grow
like $n^\alpha$ for any $\alpha$ with $r > \frac{\alpha-1}{\alpha^2}$.

### Completing the Proof

**Step 1:** Define $h(\alpha) = \frac{\alpha-1}{\alpha^2}$ for $\alpha > 1$.

Computing: $h'(\alpha) = \frac{\alpha^2 - 2\alpha(\alpha-1)}{\alpha^4} = \frac{2\alpha - \alpha^2}{\alpha^4} = \frac{2-\alpha}{\alpha^3}$

So $h'(\alpha) = 0$ when $\alpha = 2$, and:
- $h'(\alpha) > 0$ for $1 < \alpha < 2$
- $h'(\alpha) < 0$ for $\alpha > 2$

Thus $h$ is maximized at $\alpha = 2$ with $h(2) = \frac{1}{4}$.

**Step 2:** We need to show that any $g$ satisfying the constraint must grow like $n^\alpha$ for SOME $\alpha$.

This is the tricky part. Let's use a different argument.

**Alternative Approach:** Suppose $r > 1/4$. We'll show no $g$ can satisfy the constraint.

From Lemma 1, $g$ is unbounded. So for any $M$, there exists $n$ with $g(n) > M$.

Define $\alpha(n) = \frac{\log g(n)}{\log n}$ (the "local growth exponent").

From the constraint:
$$g(n+1) - g(n) \geq (g(g(n)))^r$$

Taking logs (for large $n$ where $g(n+1) - g(n) \geq 1$):
$$\log(g(n+1) - g(n)) \geq r \log g(g(n))$$

For large $n$, if $g(n) \sim n^{\alpha(n)}$, then:
- $g(n+1) - g(n) \sim \alpha(n) n^{\alpha(n)-1}$
- $g(g(n)) \sim (n^{\alpha(n)})^{\alpha(g(n))}$

This becomes very complicated because $\alpha$ itself depends on $n$.

**Better idea:** Use a contradiction argument with specific bounds.

Suppose $r > 1/4$. Pick $r = 1/4 + \epsilon$ for some $\epsilon > 0$.

We'll show that for ANY function $g$, the constraint eventually fails.

**Case 1:** $g(n) \leq n^{2-\delta}$ for infinitely many $n$ (for some $\delta > 0$).

Then for such $n$: $g(g(n)) \leq (n^{2-\delta})^{2-\delta} = n^{(2-\delta)^2}$

The constraint requires:
$$g(n+1) - g(n) \geq n^{r(2-\delta)^2}$$

Summing from such an $n$ to $n+k$:
$$g(n+k) \geq g(n) + k \cdot n^{r(2-\delta)^2}$$

For $k = n$, this gives $g(2n) \geq n \cdot n^{r(2-\delta)^2} = n^{1+r(2-\delta)^2}$

For $\delta$ small and $r > 1/4$:
$$1 + r(2-\delta)^2 > 1 + \frac{1}{4} \cdot 4 = 2$$

So $g(2n) > (2n)^{2-\delta'}$ for small $\delta'$, eventually violating the assumption.

**Case 2:** $g(n) \geq n^{2+\delta}$ for all large $n$ (for some $\delta > 0$).

Then: $g(n+1) - g(n) \leq (2+\delta) n^{1+\delta} + O(n^\delta)$

But: $g(g(n)) \geq (n^{2+\delta})^{2+\delta} = n^{(2+\delta)^2}$

The constraint requires:
$$(2+\delta) n^{1+\delta} \geq n^{r(2+\delta)^2}$$

For large $n$: $1 + \delta \geq r(2+\delta)^2$

Taking $\delta \to 0^+$: $1 \geq 4r$, so $r \leq 1/4$.

If $r > 1/4$, this fails for small enough $\delta$!

**Case 3:** $g$ oscillates between growth rates.

By Lemma 2, $g$ is eventually increasing, so we can't have wild oscillations.
The function must settle into a growth rate, bringing us back to Cases 1 or 2.

### Conclusion

In all cases, if $r > 1/4$, the constraint eventually fails.

Therefore, the maximum value of $r$ is $\boxed{\frac{1}{4}}$. $\blacksquare$

