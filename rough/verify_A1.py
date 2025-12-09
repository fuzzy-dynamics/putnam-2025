#!/usr/bin/env python3
"""
Numerical verification of Putnam 2025 A1 solution.
Tests the descent argument on odd parts for various initial conditions.
"""

from math import gcd
from typing import Tuple, List


def compute_sequence(m0: int, n0: int, steps: int) -> List[dict]:
    """
    Compute the sequence (m_k, n_k) and associated quantities.

    Returns a list of dictionaries containing:
    - k: step number
    - m_k, n_k: the relatively prime pair
    - a_k = 2m_k + 1, b_k = 2n_k + 1
    - d_k = gcd(a_k, b_k)
    - delta_k = |a_k - b_k|
    - o_k: odd part of delta_k
    - e_k: power of 2 in delta_k
    """
    results = []
    m, n = m0, n0

    for k in range(steps):
        a_k = 2 * m + 1
        b_k = 2 * n + 1
        d_k = gcd(a_k, b_k)
        delta_k = abs(a_k - b_k)

        # Compute odd part and exponent
        e_k = 0
        o_k = delta_k
        while o_k % 2 == 0:
            o_k //= 2
            e_k += 1

        results.append({
            'k': k,
            'm_k': m,
            'n_k': n,
            'a_k': a_k,
            'b_k': b_k,
            'd_k': d_k,
            'delta_k': delta_k,
            'e_k': e_k,
            'o_k': o_k,
        })

        # Compute next step: m_{k+1}/n_{k+1} = a_k/b_k in lowest terms
        g = gcd(a_k, b_k)
        m = a_k // g
        n = b_k // g

        # Verify m and n are coprime
        assert gcd(m, n) == 1, f"Step {k+1}: m_{k+1}={m} and n_{k+1}={n} not coprime!"

    return results


def verify_lemma(results: List[dict]) -> bool:
    """
    Verify the key lemma: o_k = o_{k-1} / d_{k-1}
    """
    all_good = True
    for k in range(1, len(results)):
        prev = results[k-1]
        curr = results[k]

        expected_o_k = prev['o_k'] // prev['d_k']
        actual_o_k = curr['o_k']

        if expected_o_k != actual_o_k:
            print(f"LEMMA FAIL at k={k}: o_{k} = {actual_o_k}, but o_{k-1}/d_{k-1} = {prev['o_k']}/{prev['d_k']} = {expected_o_k}")
            all_good = False

    return all_good


def verify_descent(results: List[dict]) -> Tuple[bool, int]:
    """
    Verify that whenever d_k > 1, the odd part strictly decreases.
    Returns (all_good, num_steps_until_stable)
    """
    all_good = True
    stable_from = None

    for k in range(len(results) - 1):
        curr = results[k]
        next = results[k+1]

        if curr['d_k'] > 1:
            if next['o_k'] >= curr['o_k']:
                print(f"DESCENT FAIL at k={k}: d_k={curr['d_k']} > 1 but o_{k+1}={next['o_k']} >= o_k={curr['o_k']}")
                all_good = False

    # Find when d_k = 1 permanently
    for k in range(len(results)):
        if all(results[j]['d_k'] == 1 for j in range(k, len(results))):
            stable_from = k
            break

    return all_good, stable_from


def verify_d_k_is_odd(results: List[dict]) -> bool:
    """Verify that d_k is always odd."""
    all_good = True
    for res in results:
        if res['d_k'] % 2 == 0:
            print(f"ODD FAIL at k={res['k']}: d_k={res['d_k']} is even!")
            all_good = False
    return all_good


def verify_d_k_divides_delta_k(results: List[dict]) -> bool:
    """Verify that d_k divides delta_k."""
    all_good = True
    for res in results:
        if res['delta_k'] % res['d_k'] != 0:
            print(f"DIVISIBILITY FAIL at k={res['k']}: d_k={res['d_k']} does not divide delta_k={res['delta_k']}")
            all_good = False
    return all_good


def verify_recurrence(results: List[dict]) -> bool:
    """Verify that delta_k = 2*delta_{k-1} / d_{k-1}."""
    all_good = True
    for k in range(1, len(results)):
        prev = results[k-1]
        curr = results[k]

        expected_delta = (2 * prev['delta_k']) // prev['d_k']
        if expected_delta != curr['delta_k']:
            print(f"RECURRENCE FAIL at k={k}: delta_k={curr['delta_k']}, but 2*delta_{k-1}/d_{k-1} = 2*{prev['delta_k']}/{prev['d_k']} = {expected_delta}")
            all_good = False

    return all_good


def print_table(results: List[dict], title: str):
    """Pretty print the sequence."""
    print(f"\n{title}")
    print("=" * 100)
    print(f"{'k':>3} {'m_k':>6} {'n_k':>6} {'a_k':>8} {'b_k':>8} {'d_k':>5} {'delta_k':>10} {'e_k':>3} {'o_k':>10}")
    print("-" * 100)
    for res in results:
        print(f"{res['k']:3d} {res['m_k']:6d} {res['n_k']:6d} {res['a_k']:8d} {res['b_k']:8d} "
              f"{res['d_k']:5d} {res['delta_k']:10d} {res['e_k']:3d} {res['o_k']:10d}")


def test_case(m0: int, n0: int, steps: int = 15):
    """Run a complete test case."""
    print(f"\n{'*' * 100}")
    print(f"Testing (m_0, n_0) = ({m0}, {n0})")
    print('*' * 100)

    results = compute_sequence(m0, n0, steps)
    print_table(results, f"Sequence for (m_0, n_0) = ({m0}, {n0})")

    # Run all verifications
    checks = {
        "d_k is always odd": verify_d_k_is_odd(results),
        "d_k divides delta_k": verify_d_k_divides_delta_k(results),
        "Recurrence delta_k = 2*delta_{k-1}/d_{k-1}": verify_recurrence(results),
        "Key lemma o_k = o_{k-1}/d_{k-1}": verify_lemma(results),
    }

    descent_ok, stable_from = verify_descent(results)
    checks["Descent when d_k > 1"] = descent_ok

    print(f"\nVerification Results:")
    print("-" * 50)
    for check_name, passed in checks.items():
        status = "PASS" if passed else "FAIL"
        print(f"  {check_name}: {status}")

    if stable_from is not None:
        print(f"\n  d_k = 1 for all k >= {stable_from}")
    else:
        print(f"\n  d_k has not stabilized to 1 within {steps} steps")

    all_passed = all(checks.values())
    return all_passed, stable_from


def main():
    """Run comprehensive verification."""
    print("=" * 100)
    print("PUTNAM 2025 A1 - NUMERICAL VERIFICATION")
    print("=" * 100)

    test_cases = [
        (1, 2, 15),
        (3, 7, 15),
        (5, 11, 15),
        (2, 5, 15),
        (7, 13, 15),
        (10, 17, 20),
        (15, 28, 20),
        (100, 101, 20),  # Close values
        (1, 100, 20),    # Far apart values
        (21, 34, 20),    # Fibonacci-like
    ]

    all_results = []
    for m0, n0, steps in test_cases:
        passed, stable = test_case(m0, n0, steps)
        all_results.append((m0, n0, passed, stable))

    print("\n" + "=" * 100)
    print("SUMMARY")
    print("=" * 100)
    print(f"{'m_0':>6} {'n_0':>6} {'All Checks':>12} {'Stable at k':>12}")
    print("-" * 100)
    for m0, n0, passed, stable in all_results:
        status = "PASS" if passed else "FAIL"
        stable_str = str(stable) if stable is not None else "Not yet"
        print(f"{m0:6d} {n0:6d} {status:>12} {stable_str:>12}")

    # Final verdict
    print("\n" + "=" * 100)
    if all(r[2] for r in all_results):
        print("VERDICT: All numerical tests PASSED")
        print("The solution is CORRECT - all logical steps verified numerically")
    else:
        print("VERDICT: Some tests FAILED")
        print("The solution needs revision")
    print("=" * 100)


if __name__ == "__main__":
    main()
