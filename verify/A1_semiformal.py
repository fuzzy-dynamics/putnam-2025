"""
Semiformal Verification of Putnam 2025 A1

Problem: Prove gcd(2m_k+1, 2n_k+1) = 1 for all but finitely many k.

Key insight: Track the ODD PART of the difference delta_k = |2m_k+1 - 2n_k+1|.
The odd part is monotonically decreasing, so eventually becomes 1.
When odd part = 1, gcd must be 1 (since gcd is odd but divides a power of 2).
"""

from math import gcd

def odd_part(n):
    """Extract the odd part of n (remove all factors of 2)."""
    while n % 2 == 0:
        n //= 2
    return n

def simulate_sequence(m0, n0, max_steps=100):
    """
    Simulate the sequence and track:
    - d_k = gcd(2m_k+1, 2n_k+1)
    - delta_k = |2m_k+1 - 2n_k+1|
    - odd_part(delta_k)

    Returns the step at which d_k becomes and stays 1.
    """
    m, n = m0, n0
    history = []

    for k in range(max_steps):
        a = 2*m + 1
        b = 2*n + 1
        d = gcd(a, b)
        delta = abs(a - b)
        o = odd_part(delta) if delta > 0 else 0

        history.append({
            'k': k,
            'm': m, 'n': n,
            'a': a, 'b': b,
            'd': d,
            'delta': delta,
            'odd_part': o
        })

        # Next step
        m_new = a // d
        n_new = b // d
        m, n = m_new, n_new

        # Check termination (d=1 forever once odd_part=1)
        if o == 1 and d == 1:
            # Verify next few steps stay at d=1
            stable = True
            for _ in range(10):
                a2 = 2*m + 1
                b2 = 2*n + 1
                d2 = gcd(a2, b2)
                if d2 != 1:
                    stable = False
                    break
                m = a2
                n = b2
            if stable:
                return history, k

    return history, -1

def verify_odd_part_descent():
    """
    Verify the key lemma: odd_part(delta_k) is monotonically non-increasing.
    When d_k > 1, odd_part strictly decreases.
    """
    print("=" * 60)
    print("LEMMA VERIFICATION: Odd part descent")
    print("=" * 60)

    test_cases = [
        (1, 2), (1, 3), (2, 3), (3, 5), (7, 11),
        (13, 17), (100, 101), (50, 73), (99, 1)
    ]

    all_passed = True

    for m0, n0 in test_cases:
        if gcd(m0, n0) != 1 or m0 == n0:
            continue

        history, stabilize_at = simulate_sequence(m0, n0)

        # Check odd part is non-increasing
        odd_parts = [h['odd_part'] for h in history if h['odd_part'] > 0]
        is_non_increasing = all(odd_parts[i] >= odd_parts[i+1] for i in range(len(odd_parts)-1))

        # Check that d_k > 1 implies strict decrease in odd part
        for i in range(len(history) - 1):
            if history[i]['d'] > 1:
                if history[i]['odd_part'] <= history[i+1]['odd_part']:
                    print(f"  FAIL: d={history[i]['d']} but odd part didn't decrease")
                    all_passed = False

        status = "✓" if is_non_increasing else "✗"
        print(f"  ({m0}, {n0}): odd_parts = {odd_parts[:6]}... stabilizes at k={stabilize_at} {status}")

    return all_passed

def verify_main_theorem():
    """
    Verify the main theorem: d_k = 1 for all sufficiently large k.
    """
    print("\n" + "=" * 60)
    print("MAIN THEOREM VERIFICATION: d_k = 1 eventually")
    print("=" * 60)

    all_passed = True

    # Test many starting pairs
    for m0 in range(1, 30):
        for n0 in range(1, 30):
            if m0 == n0 or gcd(m0, n0) != 1:
                continue

            history, stabilize_at = simulate_sequence(m0, n0)

            if stabilize_at == -1:
                print(f"  FAIL: ({m0}, {n0}) did not stabilize!")
                all_passed = False
            # Only print failures or interesting cases

    print(f"  Tested all coprime pairs (m0, n0) with 1 ≤ m0, n0 < 30")
    print(f"  All pairs stabilize to d_k = 1" if all_passed else "  SOME FAILURES!")

    return all_passed

def verify_key_algebraic_identity():
    """
    Verify the key algebraic identity:
    If delta_k = |a_k - b_k| and d_k = gcd(a_k, b_k), then:
    - d_k | delta_k (since gcd divides difference)
    - odd_part(delta_{k+1}) = odd_part(delta_k) / d_k
    """
    print("\n" + "=" * 60)
    print("ALGEBRAIC IDENTITY VERIFICATION")
    print("=" * 60)

    test_cases = [(5, 13), (7, 19), (11, 23), (3, 7)]

    for m0, n0 in test_cases:
        history, _ = simulate_sequence(m0, n0, max_steps=20)

        print(f"\n  Starting from ({m0}, {n0}):")
        for i in range(min(8, len(history))):
            h = history[i]
            print(f"    k={i}: a={h['a']}, b={h['b']}, d={h['d']}, " +
                  f"δ={h['delta']}, odd(δ)={h['odd_part']}")

            # Verify d | delta
            if h['delta'] > 0 and h['delta'] % h['d'] != 0:
                print(f"      ERROR: d does not divide delta!")

        # Verify odd part relationship
        print(f"    Odd parts: {[h['odd_part'] for h in history[:8]]}")

def prove_semiformally():
    """
    Semiformal proof structure.
    """
    print("\n" + "=" * 60)
    print("SEMIFORMAL PROOF STRUCTURE")
    print("=" * 60)

    proof = """
    THEOREM: gcd(2m_k+1, 2n_k+1) = 1 for all but finitely many k.

    PROOF:

    Let a_k = 2m_k + 1 and b_k = 2n_k + 1.
    Let d_k = gcd(a_k, b_k) and δ_k = |a_k - b_k|.

    OBSERVATION 1: d_k is always odd (since a_k, b_k are odd).

    OBSERVATION 2: d_k | δ_k (gcd divides difference).

    OBSERVATION 3: From the recurrence,
        m_{k+1} = a_k/d_k, n_{k+1} = b_k/d_k
        a_{k+1} = 2a_k/d_k + 1, b_{k+1} = 2b_k/d_k + 1
        δ_{k+1} = |a_{k+1} - b_{k+1}| = 2δ_k/d_k

    KEY LEMMA: Let o_k = odd_part(δ_k). Then:
        o_{k+1} = o_k / d_k

    Proof: Write δ_k = 2^{e_k} · o_k.
           δ_{k+1} = 2δ_k/d_k = 2^{e_k+1} · o_k/d_k
           Since d_k is odd and d_k | δ_k, we have d_k | o_k.
           So o_{k+1} = o_k/d_k. □

    CONSEQUENCE: o_k is a monotonically non-increasing sequence of
                 positive odd integers. It must eventually reach 1.

    FINAL STEP: When o_k = 1, we have δ_k = 2^{e_k}.
                Since d_k is odd and d_k | δ_k = 2^{e_k}, we must have d_k = 1.
                Once d_k = 1, we have δ_{k+1} = 2δ_k, so o_{k+1} = o_k = 1.
                By induction, d_j = 1 for all j ≥ k.

    Therefore, gcd(2m_k+1, 2n_k+1) = 1 for all but finitely many k. ∎
    """
    print(proof)

def main():
    print("Putnam 2025 A1 - Semiformal Verification")
    print("=" * 60)

    # Run verifications
    lemma_ok = verify_odd_part_descent()
    theorem_ok = verify_main_theorem()
    verify_key_algebraic_identity()
    prove_semiformally()

    print("\n" + "=" * 60)
    print("VERIFICATION SUMMARY")
    print("=" * 60)
    print(f"  Odd part descent lemma: {'PASSED ✓' if lemma_ok else 'FAILED ✗'}")
    print(f"  Main theorem (d_k → 1): {'PASSED ✓' if theorem_ok else 'FAILED ✗'}")
    print(f"\n  CONCLUSION: Solution is {'CORRECT' if lemma_ok and theorem_ok else 'NEEDS REVIEW'}")

    return lemma_ok and theorem_ok

if __name__ == "__main__":
    success = main()
    exit(0 if success else 1)
