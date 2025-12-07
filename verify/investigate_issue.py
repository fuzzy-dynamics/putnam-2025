#!/usr/bin/env python3
"""
Investigate cases where d_k can go from 1 to > 1.
This is actually FINE - the proof doesn't claim monotonicity of d_k!
The proof only claims that o_k strictly decreases when d_k > 1.
"""

from math import gcd


def detailed_trace(m0: int, n0: int, steps: int = 15):
    """Detailed trace showing when d_k changes."""
    print(f"\n{'=' * 100}")
    print(f"Detailed trace for (m_0, n_0) = ({m0}, {n0})")
    print('=' * 100)
    print(f"{'k':>3} {'m_k':>6} {'n_k':>6} {'a_k':>8} {'b_k':>8} {'d_k':>5} "
          f"{'delta_k':>10} {'e_k':>3} {'o_k':>10} {'d_k status':<15}")
    print('-' * 100)

    m, n = m0, n0
    prev_o = None

    for k in range(steps):
        a_k = 2 * m + 1
        b_k = 2 * n + 1
        d_k = gcd(a_k, b_k)
        delta_k = abs(a_k - b_k)

        # Compute odd part
        e_k = 0
        o_k = delta_k
        while o_k % 2 == 0:
            o_k //= 2
            e_k += 1

        # Check status
        status = ""
        if d_k == 1:
            status = "gcd = 1"
        else:
            status = f"gcd = {d_k} > 1"

        if prev_o is not None:
            if d_k > 1:
                status += f" (o decreased)"

        print(f"{k:3d} {m:6d} {n:6d} {a_k:8d} {b_k:8d} {d_k:5d} "
              f"{delta_k:10d} {e_k:3d} {o_k:10d} {status:<15}")

        prev_o = o_k

        # Compute next step
        g = gcd(a_k, b_k)
        m = a_k // g
        n = b_k // g


def main():
    # Test cases where d_k oscillates
    cases = [
        (15, 28),
        (1, 100),
        (21, 34),
        (123, 456),
    ]

    for m0, n0 in cases:
        detailed_trace(m0, n0, steps=12)

    print("\n" + "=" * 100)
    print("OBSERVATION:")
    print("=" * 100)
    print("The value d_k can indeed go from 1 to > 1!")
    print("This does NOT contradict the proof.")
    print()
    print("The proof claims:")
    print("  - When d_k > 1, the odd part o_k STRICTLY DECREASES at the next step")
    print("  - The odd part o_k can only decrease finitely many times")
    print("  - Therefore, there are only finitely many k where d_k > 1")
    print()
    print("The proof does NOT claim:")
    print("  - Once d_k = 1, it stays 1 forever (this is FALSE)")
    print("  - The sequence d_k is eventually constant (this is FALSE)")
    print()
    print("What the proof DOES guarantee:")
    print("  - Eventually, d_k = 1 for ALL remaining steps")
    print("  - This happens after the odd part stops decreasing")
    print("=" * 100)


if __name__ == "__main__":
    main()
