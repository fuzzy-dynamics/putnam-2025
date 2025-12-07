#!/usr/bin/env python3
"""
Verification script for Putnam 2025 A5

Problem: For sequence s = (s_1, ..., s_{n-1}) with s_i = +/- 1,
f(s) = number of permutations of {1,...,n} with s_i(a_{i+1} - a_i) > 0 for all i.
Find which sequences maximize f(s).

Answer: The two alternating sequences (+,-,+,-,...) and (-,+,-,+,...) maximize f(s).
"""

from itertools import permutations, product
from math import comb


def compute_f(n, s):
    """Compute f(s) by direct enumeration."""
    if n <= 1:
        return 1
    if len(s) == 0:
        return 1
    count = 0
    for perm in permutations(range(1, n+1)):
        valid = True
        for i in range(len(s)):
            if s[i] * (perm[i+1] - perm[i]) <= 0:
                valid = False
                break
        if valid:
            count += 1
    return count


def get_peaks(s):
    """Get valid peak positions where max element can be placed."""
    n = len(s) + 1
    peaks = []
    for j in range(1, n+1):
        ok = True
        if j > 1 and s[j-2] != 1:
            ok = False
        if j < n and s[j-1] != -1:
            ok = False
        if ok:
            peaks.append(j)
    return peaks


def compute_f_recursive(n, s):
    """Compute f(s) using the recursion formula."""
    if n <= 1:
        return 1
    if len(s) == 0:
        return 1

    peaks = get_peaks(s)
    total = 0
    for j in peaks:
        s_L = s[:j-2] if j > 2 else ()
        s_R = s[j:] if j < n else ()
        f_L = compute_f(j-1, s_L)
        f_R = compute_f(n-j, s_R)
        total += comb(n-1, j-1) * f_L * f_R
    return total


def is_alternating(s):
    """Check if sequence is alternating."""
    if len(s) <= 1:
        return True
    return all(s[i] != s[i+1] for i in range(len(s)-1))


def verify_all(max_n=7):
    """Verify the theorem for all n up to max_n."""
    print("=" * 60)
    print("Verification of Putnam 2025 A5")
    print("=" * 60)
    print()

    all_correct = True

    for n in range(2, max_n + 1):
        print(f"n = {n}:")

        # Compute f(s) for all sequences
        results = {}
        for s in product([1, -1], repeat=n-1):
            f_s = compute_f(n, s)
            results[s] = f_s

        # Find maximum
        max_f = max(results.values())
        max_seqs = [s for s, f in results.items() if f == max_f]

        # Check if maximizers are exactly the alternating sequences
        alt_seqs = [s for s in max_seqs if is_alternating(s)]
        all_alt = len(alt_seqs) == len(max_seqs) == 2

        # Verify recursion formula
        recursion_ok = True
        for s in results:
            f_direct = results[s]
            f_rec = compute_f_recursive(n, s)
            if f_direct != f_rec:
                recursion_ok = False
                print(f"  RECURSION MISMATCH: {s}, direct={f_direct}, recursive={f_rec}")

        status = "PASS" if all_alt and recursion_ok else "FAIL"
        print(f"  Max f(s) = {max_f}")
        print(f"  Maximizers are alternating: {all_alt}")
        print(f"  Recursion verified: {recursion_ok}")
        print(f"  Status: {status}")
        print()

        if not (all_alt and recursion_ok):
            all_correct = False

    print("=" * 60)
    if all_correct:
        print("ALL VERIFICATIONS PASSED")
    else:
        print("SOME VERIFICATIONS FAILED")
    print("=" * 60)

    return all_correct


if __name__ == "__main__":
    verify_all()
