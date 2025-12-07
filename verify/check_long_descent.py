#!/usr/bin/env python3
"""
Check cases where o_k takes a long time to reach 1.
"""

from math import gcd


def trace_until_stable(m0: int, n0: int, max_steps: int = 200):
    """Trace until o_k = 1."""
    m, n = m0, n0

    print(f"\nTracing (m_0, n_0) = ({m0}, {n0})")
    print(f"{'k':>4} {'o_k':>15} {'d_k':>10}")
    print("-" * 35)

    for k in range(max_steps):
        a_k = 2 * m + 1
        b_k = 2 * n + 1
        d_k = gcd(a_k, b_k)
        delta_k = abs(a_k - b_k)

        # Compute odd part
        o_k = delta_k
        while o_k % 2 == 0:
            o_k //= 2

        print(f"{k:4d} {o_k:15d} {d_k:10d}")

        if o_k == 1:
            print(f"\nReached o_k = 1 at k = {k}")
            return k

        # Compute next step
        g = gcd(a_k, b_k)
        m = a_k // g
        n = b_k // g

    print(f"\nDid not reach o_k = 1 within {max_steps} steps")
    print(f"Final o_k = {o_k}")
    return None


def main():
    # Cases that didn't reach o_k = 1 in 50 steps
    cases = [
        (5, 11),
        (2, 5),
        (50, 77),
    ]

    for m0, n0 in cases:
        stable_at = trace_until_stable(m0, n0, max_steps=100)


if __name__ == "__main__":
    main()
