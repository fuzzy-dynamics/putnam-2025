#!/usr/bin/env python3
"""
Investigate: when does d_k > 1?

For d_k > 1, we need some odd prime p > 1 to divide both a_k and b_k.

Key observation: a_k = 2m_k + 1, b_k = 2n_k + 1
If p | a_k and p | b_k, then:
  2m_k ≡ -1 (mod p)
  2n_k ≡ -1 (mod p)

This means 2(m_k - n_k) ≡ 0 (mod p)
If p is odd and p > 2, then m_k ≡ n_k (mod p).

But we also have: m_k / n_k = a_{k-1} / b_{k-1}
So: m_k * b_{k-1} = n_k * a_{k-1}
"""

from math import gcd


def find_when_gcd_hits(m0: int, n0: int, target_divisor: int, max_steps: int = 10000):
    """Find when d_k is divisible by target_divisor."""
    m, n = m0, n0

    for k in range(max_steps):
        a_k = 2 * m + 1
        b_k = 2 * n + 1
        d_k = gcd(a_k, b_k)

        if d_k % target_divisor == 0:
            # Compute odd part
            delta_k = abs(a_k - b_k)
            o_k = delta_k
            while o_k % 2 == 0:
                o_k //= 2

            print(f"(m_0, n_0) = ({m0:3d}, {n0:3d}): "
                  f"d_{k} = {d_k} (divisible by {target_divisor}) at k = {k}")
            print(f"  a_k = {a_k}, b_k = {b_k}, o_k = {o_k}")
            print(f"  Checking: a_k mod {target_divisor} = {a_k % target_divisor}, "
                  f"b_k mod {target_divisor} = {b_k % target_divisor}")
            return k

        # Compute next step
        g = gcd(a_k, b_k)
        m = a_k // g
        n = b_k // g

    print(f"(m_0, n_0) = ({m0:3d}, {n0:3d}): "
          f"d_k not divisible by {target_divisor} within {max_steps} steps")
    return None


def main():
    print("Finding when d_k is divisible by 3:\n")

    # Cases where o_k = 3 stays constant
    cases = [
        (5, 11, 3),
        (2, 5, 3),
        (50, 77, 3),  # o_k = 27 = 3^3
        (50, 77, 9),  # Check for 9
        (50, 77, 27), # Check for 27
    ]

    for m0, n0, divisor in cases:
        find_when_gcd_hits(m0, n0, divisor, max_steps=10000)
        print()


if __name__ == "__main__":
    main()
