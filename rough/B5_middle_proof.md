# Proof that the Middle Pair Has an Inversion

## Claim
For $p > 3$ prime, let $k_0 = (p-1)/2$ (the middle position). Then $I(k_0 + 1) < I(k_0)$.

## Computational Observation
For all tested primes, we have:
- $I((p+1)/2) = 2$
- $I((p-1)/2) = p - 2$

This would immediately give $I(k_0 + 1) = 2 < p - 2 = I(k_0)$!

## Proof that $I((p+1)/2) = 2$

We need to show that $\frac{p+1}{2} \cdot 2 \equiv 1 \pmod{p}$.

$$\frac{p+1}{2} \cdot 2 = p + 1 \equiv 1 \pmod{p}$$

Yes! This is always true.

## Proof that $I((p-1)/2) = p - 2$

We need to show that $\frac{p-1}{2} \cdot (p-2) \equiv 1 \pmod{p}$.

$$\frac{p-1}{2} \cdot (p-2) = \frac{(p-1)(p-2)}{2} = \frac{p^2 - 3p + 2}{2}$$

Modulo $p$:
$$\frac{p^2 - 3p + 2}{2} \equiv \frac{-3p + 2}{2} \equiv \frac{2}{2} = 1 \pmod{p}$$

Wait, let me be more careful. We have:
$$\frac{p-1}{2} \cdot (p-2) \pmod{p}$$

Since $p-2 \equiv -2 \pmod{p}$:
$$\frac{p-1}{2} \cdot (-2) \equiv -(p-1) \equiv 1 \pmod{p}$$

Yes! This works.

## Conclusion

For the middle pair $k_0 = (p-1)/2$ and $k_0 + 1 = (p+1)/2$:
- $I(k_0) = I((p-1)/2) = p - 2$
- $I(k_0 + 1) = I((p+1)/2) = 2$
- Therefore $I(k_0 + 1) = 2 < p - 2 = I(k_0)$

So the middle pair ALWAYS has an inversion!

This is a crucial result for the proof.
