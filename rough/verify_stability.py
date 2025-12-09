#!/usr/bin/env python3
"""
Verify that once d_k = 1, it remains 1 forever.
"""

from math import gcd


def verify_stability_property(m0: int, n0: int, steps: int = 30):
    """
    Verify: if d_k = 1, then d_{k+1} = 1.

    This follows from: o_{k+1} = o_k / d_k = o_k / 1 = o_k
    So the odd part doesn't change when d_k = 1.
    """
    m, n = m0, n0
    found_stable = False
    stable_from = None

    for k in range(steps):
        a_k = 2 * m + 1
        b_k = 2 * n + 1
        d_k = gcd(a_k, b_k)

        # Check if we've reached stability
        if d_k == 1:
            if not found_stable:
                found_stable = True
                stable_from = k

        # If we were stable but now d_k > 1, that's a problem
        elif found_stable:
            print(f"STABILITY VIOLATION: (m_0, n_0) = ({m0}, {n0})")
            print(f"  d_k = 1 starting at k = {stable_from}")
            print(f"  But d_{k} = {d_k} > 1")
            return False

        # Compute next step
        g = gcd(a_k, b_k)
        m = a_k // g
        n = b_k // g

    if found_stable:
        print(f"(m_0, n_0) = ({m0:4d}, {n0:4d}): Stable from k = {stable_from:2d}, verified for {steps - stable_from} steps")
    else:
        print(f"(m_0, n_0) = ({m0:4d}, {n0:4d}): Not stable within {steps} steps (d_k > 1 throughout or still decreasing)")

    return True


def main():
    print("=" * 80)
    print("Verifying Stability Property: Once d_k = 1, it stays 1 forever")
    print("=" * 80)

    test_cases = [
        (1, 2),
        (3, 7),
        (5, 11),
        (2, 5),
        (7, 13),
        (10, 17),
        (15, 28),
        (100, 101),
        (1, 100),
        (21, 34),
        (50, 77),
        (123, 456),
    ]

    all_pass = True
    for m0, n0 in test_cases:
        if not verify_stability_property(m0, n0, steps=50):
            all_pass = False

    print("=" * 80)
    if all_pass:
        print("RESULT: Stability property verified for all test cases")
        print("Once d_k = 1, it remains 1 for all subsequent steps.")
    else:
        print("RESULT: Stability property FAILED for some cases")
    print("=" * 80)


if __name__ == "__main__":
    main()
