# Putnam 2025 B2 - Detailed Algebra Verification

## Step 1: Centroid Formulas

### 2D Region Centroid
The region $R$ is bounded by $x=0$, $x=1$, $y=0$, and $y=f(x)$.

Area: $A = \int_0^1 f(x) \, dx$

First moment about y-axis: $M_y = \int_0^1 x \cdot f(x) \, dx$

Centroid: $x_1 = \frac{M_y}{A} = \frac{\int_0^1 x f(x) \, dx}{\int_0^1 f(x) \, dx}$

**VERIFIED**: Correct.

### Solid of Revolution Centroid
When rotating about the x-axis, we get disks of radius $r = f(x)$.

Volume element: $dV = \pi [f(x)]^2 \, dx$

Total volume: $V = \int_0^1 \pi [f(x)]^2 \, dx$

First moment: $M = \int_0^1 x \cdot \pi [f(x)]^2 \, dx$

Centroid: $x_2 = \frac{M}{V} = \frac{\int_0^1 x [f(x)]^2 \, dx}{\int_0^1 [f(x)]^2 \, dx}$

**VERIFIED**: Correct. The $\pi$ cancels.

## Step 2: Cross-Multiplication

Need to prove:
$$\frac{\int_0^1 x f(x) \, dx}{\int_0^1 f(x) \, dx} < \frac{\int_0^1 x [f(x)]^2 \, dx}{\int_0^1 [f(x)]^2 \, dx}$$

Since both denominators are positive (f is strictly increasing and continuous from [0,1] to [0, infinity), so $f$ is not identically zero), we can cross-multiply preserving the inequality:

$$\left(\int_0^1 x f(x) \, dx\right) \left(\int_0^1 [f(x)]^2 \, dx\right) < \left(\int_0^1 x [f(x)]^2 \, dx\right) \left(\int_0^1 f(x) \, dx\right)$$

**VERIFIED**: Correct.

## Step 3: The Double Integral

Define:
$$I = \int_0^1 \int_0^1 (y - x) f(x) f(y) [f(y) - f(x)] \, dx \, dy$$

### Claim: $I > 0$

For any $(x, y) \in [0,1]^2$:

- If $x < y$: $(y-x) > 0$ and $f(y) - f(x) > 0$ (strict increasing), so $(y-x)[f(y)-f(x)] > 0$
- If $x > y$: $(y-x) < 0$ and $f(y) - f(x) < 0$, so $(y-x)[f(y)-f(x)] > 0$
- If $x = y$: $(y-x)[f(y)-f(x)] = 0$

The integrand is $(y-x)[f(y)-f(x)] \cdot f(x)f(y)$.

Since $f$ is continuous, strictly increasing on $[0,1]$, and maps to $[0, \infty)$, we know:
- $f(x) f(y) > 0$ for $(x,y)$ in a set of positive measure (specifically, wherever $f(x) > 0$ and $f(y) > 0$)
- $(y-x)[f(y)-f(x)] \geq 0$ everywhere, with equality only on the diagonal $x = y$

Therefore, the integrand is strictly positive on a set of positive measure (e.g., the region where $x \neq y$ and both $f(x), f(y) > 0$), giving $I > 0$.

**VERIFIED**: The argument is correct.

## Step 4: Expanding the Double Integral

Starting with:
$$I = \int_0^1 \int_0^1 (y - x) f(x) f(y) [f(y) - f(x)] \, dx \, dy$$

Expand $[f(y) - f(x)]$:
$$I = \int_0^1 \int_0^1 (y - x) f(x) f(y) [f(y) - f(x)] \, dx \, dy$$
$$= \int_0^1 \int_0^1 (y - x) [f(x) f(y)^2 - f(x)^2 f(y)] \, dx \, dy$$

Expand $(y-x)$:
$$= \int_0^1 \int_0^1 [y f(x) f(y)^2 - x f(x) f(y)^2 - y f(x)^2 f(y) + x f(x)^2 f(y)] \, dx \, dy$$

Separate into four terms:
$$I = \int_0^1 \int_0^1 y f(x) f(y)^2 \, dx \, dy - \int_0^1 \int_0^1 x f(x) f(y)^2 \, dx \, dy$$
$$\quad - \int_0^1 \int_0^1 y f(x)^2 f(y) \, dx \, dy + \int_0^1 \int_0^1 x f(x)^2 f(y) \, dx \, dy$$

**VERIFIED**: Algebra is correct.

## Step 5: Applying Fubini's Theorem

Term 1: $\int_0^1 \int_0^1 y f(x) f(y)^2 \, dx \, dy = \int_0^1 y f(y)^2 \, dy \int_0^1 f(x) \, dx$

Term 2: $\int_0^1 \int_0^1 x f(x) f(y)^2 \, dx \, dy = \int_0^1 x f(x) \, dx \int_0^1 f(y)^2 \, dy$

Term 3: $\int_0^1 \int_0^1 y f(x)^2 f(y) \, dx \, dy = \int_0^1 y f(y) \, dy \int_0^1 f(x)^2 \, dx$

Term 4: $\int_0^1 \int_0^1 x f(x)^2 f(y) \, dx \, dy = \int_0^1 x f(x)^2 \, dx \int_0^1 f(y) \, dy$

So:
$$I = \left(\int_0^1 y f(y)^2 \, dy\right)\left(\int_0^1 f(x) \, dx\right) - \left(\int_0^1 x f(x) \, dx\right)\left(\int_0^1 f(y)^2 \, dy\right)$$
$$\quad - \left(\int_0^1 y f(y) \, dy\right)\left(\int_0^1 f(x)^2 \, dx\right) + \left(\int_0^1 x f(x)^2 \, dx\right)\left(\int_0^1 f(y) \, dy\right)$$

**VERIFIED**: Fubini's theorem application is correct.

## Step 6: Simplifying

Since $x$ and $y$ are dummy variables, we can rename them consistently:

$$I = \left(\int_0^1 x f(x)^2 \, dx\right)\left(\int_0^1 f(x) \, dx\right) - \left(\int_0^1 x f(x) \, dx\right)\left(\int_0^1 f(x)^2 \, dx\right)$$
$$\quad - \left(\int_0^1 x f(x) \, dx\right)\left(\int_0^1 f(x)^2 \, dx\right) + \left(\int_0^1 x f(x)^2 \, dx\right)\left(\int_0^1 f(x) \, dx\right)$$

Grouping like terms:
$$I = 2\left[\left(\int_0^1 x f(x)^2 \, dx\right)\left(\int_0^1 f(x) \, dx\right) - \left(\int_0^1 x f(x) \, dx\right)\left(\int_0^1 f(x)^2 \, dx\right)\right]$$

**VERIFIED**: The factorization of 2 is correct.

## Step 7: Concluding

Since $I > 0$, we have:
$$2\left[\left(\int_0^1 x f(x)^2 \, dx\right)\left(\int_0^1 f(x) \, dx\right) - \left(\int_0^1 x f(x) \, dx\right)\left(\int_0^1 f(x)^2 \, dx\right)\right] > 0$$

Therefore:
$$\left(\int_0^1 x f(x)^2 \, dx\right)\left(\int_0^1 f(x) \, dx\right) > \left(\int_0^1 x f(x) \, dx\right)\left(\int_0^1 f(x)^2 \, dx\right)$$

Dividing both sides by the positive quantities $\int_0^1 f(x) \, dx$ and $\int_0^1 f(x)^2 \, dx$:
$$\frac{\int_0^1 x f(x)^2 \, dx}{\int_0^1 f(x)^2 \, dx} > \frac{\int_0^1 x f(x) \, dx}{\int_0^1 f(x) \, dx}$$

This is exactly $x_2 > x_1$.

**VERIFIED**: The conclusion is correct.

## Summary

All steps of the proof are mathematically correct:

1. Centroid formulas - Correct
2. Cross-multiplication - Correct
3. Double integral positivity - Correct
4. Expansion of double integral - Correct
5. Application of Fubini's theorem - Correct
6. Simplification to factor of 2 - Correct
7. Final conclusion - Correct

The proof is complete and rigorous.
