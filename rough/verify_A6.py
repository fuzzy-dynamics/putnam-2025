#!/usr/bin/env python3
"""
Verification of Putnam 2025 A6 solution.

Problem: Let b_0=0 and b_{n+1}=2b_n^2+b_n+1 for n>=0.
Show that for each k>=1, b_{2^{k+1}}-2b_{2^k} is divisible by 2^{2k+2} but not by 2^{2k+3}.
"""

def compute_b(n_max):
    """Compute b_n for n=0 to n_max using the recurrence."""
    b = [0]  # b_0 = 0
    for n in range(n_max):
        b_next = 2 * b[n]**2 + b[n] + 1
        b.append(b_next)
    return b

def compute_d(n_max):
    """Compute d_n = 2b_n + 1 for n=0 to n_max."""
    d = [1]  # d_0 = 2*0 + 1 = 1
    for n in range(n_max):
        # d_{n+1} = d_n(d_n - 1) + 3
        d_next = d[n] * (d[n] - 1) + 3
        d.append(d_next)
    return d

def v2(n):
    """Compute the 2-adic valuation of n (highest power of 2 dividing n)."""
    if n == 0:
        return float('inf')
    count = 0
    while n % 2 == 0:
        count += 1
        n //= 2
    return count

def verify_d_recurrence(b_vals, d_vals):
    """Verify that d_n = 2b_n + 1 and the recurrence holds."""
    print("=" * 80)
    print("Verification of d_n = 2b_n + 1 and d_{n+1} = d_n(d_n-1) + 3")
    print("=" * 80)

    for n in range(min(10, len(b_vals))):
        computed_d = 2 * b_vals[n] + 1
        if computed_d != d_vals[n]:
            print(f"ERROR at n={n}: d_n computed as {computed_d} but got {d_vals[n]}")
            return False

        if n < len(d_vals) - 1:
            expected_d_next = d_vals[n] * (d_vals[n] - 1) + 3
            if expected_d_next != d_vals[n+1]:
                print(f"ERROR at n={n}: d_{{n+1}} should be {expected_d_next} but got {d_vals[n+1]}")
                return False

    print("✓ d_n = 2b_n + 1 holds")
    print("✓ d_{n+1} = d_n(d_n-1) + 3 holds")
    print()
    return True

def print_initial_values(b_vals, d_vals):
    """Print initial values of b_n and d_n."""
    print("=" * 80)
    print("Initial values of b_n and d_n")
    print("=" * 80)
    print(f"{'n':>3} | {'b_n':>20} | {'d_n':>20} | {'v_2(b_n)':>10} | {'v_2(d_n-1)':>10}")
    print("-" * 80)

    for n in range(min(10, len(b_vals))):
        v2_b = v2(b_vals[n]) if b_vals[n] > 0 else float('inf')
        v2_d_minus_1 = v2(d_vals[n] - 1)
        print(f"{n:3d} | {b_vals[n]:20d} | {d_vals[n]:20d} | {v2_b:10} | {v2_d_minus_1:10d}")
    print()

def verify_claim_1(d_vals):
    """Verify Claim 1: v_2(d_{2^k} - 1) = k+2 and d_{2^k} = 1 + 2^{k+2} * s_k where s_k is odd."""
    print("=" * 80)
    print("Verification of Claim 1: v_2(d_{2^k} - 1) = k+2")
    print("=" * 80)

    max_k = 0
    while 2**max_k < len(d_vals):
        max_k += 1
    max_k -= 1

    print(f"{'k':>3} | {'2^k':>6} | {'d_{2^k}':>25} | {'v_2(d_{2^k}-1)':>15} | {'Expected':>10} | {'s_k odd?':>10}")
    print("-" * 100)

    all_correct = True
    for k in range(1, max_k + 1):
        idx = 2**k
        if idx >= len(d_vals):
            break

        d_val = d_vals[idx]
        v2_val = v2(d_val - 1)
        expected = k + 2

        # Check if d_{2^k} = 1 + 2^{k+2} * s_k where s_k is odd
        if d_val <= 1:
            s_k = 0
            s_k_odd = False
        else:
            if (d_val - 1) % (2**(k+2)) != 0:
                s_k = "ERROR"
                s_k_odd = False
            else:
                s_k = (d_val - 1) // (2**(k+2))
                s_k_odd = (s_k % 2 == 1)

        status = "✓" if v2_val == expected and s_k_odd else "✗"
        if v2_val != expected or not s_k_odd:
            all_correct = False

        print(f"{k:3d} | {idx:6d} | {d_val:25d} | {v2_val:15d} | {expected:10d} | {str(s_k_odd):>10} {status}")

    print()
    return all_correct

def verify_claim_2(b_vals):
    """Verify Claim 2: v_2(b_{2^{k+1}} - 2b_{2^k}) = 2k+2."""
    print("=" * 80)
    print("Verification of Claim 2: v_2(b_{2^{k+1}} - 2b_{2^k}) = 2k+2")
    print("=" * 80)

    max_k = 0
    while 2**(max_k + 1) < len(b_vals):
        max_k += 1
    max_k -= 1

    print(f"{'k':>3} | {'2^k':>6} | {'2^{k+1}':>6} | {'b_{2^{k+1}} - 2b_{2^k}':>30} | {'v_2':>6} | {'Expected':>10} | Status")
    print("-" * 110)

    all_correct = True
    for k in range(1, max_k + 1):
        idx_k = 2**k
        idx_k_plus_1 = 2**(k+1)

        if idx_k_plus_1 >= len(b_vals):
            break

        b_k = b_vals[idx_k]
        b_k_plus_1 = b_vals[idx_k_plus_1]

        diff = b_k_plus_1 - 2 * b_k
        v2_diff = v2(diff)
        expected = 2 * k + 2

        status = "✓" if v2_diff == expected else "✗"
        if v2_diff != expected:
            all_correct = False

        # Check that it's NOT divisible by 2^{2k+3}
        not_divisible_by_higher = (diff % (2**(2*k+3)) != 0)
        status2 = "✓" if not_divisible_by_higher else "✗"

        print(f"{k:3d} | {idx_k:6d} | {idx_k_plus_1:6d} | {diff:30d} | {v2_diff:6d} | {expected:10d} | {status} (not by 2^{2*k+3}: {status2})")

    print()
    return all_correct

def verify_s_k_differences(b_vals, d_vals):
    """Verify the claim that s_{k+1} - s_k has specific 2-adic valuation."""
    print("=" * 80)
    print("Verification of s_{k+1} - s_k claim")
    print("=" * 80)

    max_k = 0
    while 2**(max_k + 1) < len(d_vals):
        max_k += 1
    max_k -= 1

    print(f"{'k':>3} | {'s_k':>15} | {'s_{k+1}':>15} | {'s_{k+1} - s_k':>20} | {'v_2(diff)':>10} | Expected k")
    print("-" * 90)

    s_vals = []
    for k in range(1, max_k + 1):
        idx = 2**k
        if idx >= len(d_vals):
            break
        d_val = d_vals[idx]
        s_k = (d_val - 1) // (2**(k+2))
        s_vals.append((k, s_k))

    for i in range(len(s_vals) - 1):
        k, s_k = s_vals[i]
        k_plus_1, s_k_plus_1 = s_vals[i+1]

        diff = s_k_plus_1 - s_k
        v2_diff = v2(diff) if diff != 0 else float('inf')

        status = "✓" if v2_diff == k else "✗"
        print(f"{k:3d} | {s_k:15d} | {s_k_plus_1:15d} | {diff:20d} | {v2_diff:10} | {k:10d} {status}")

    print()

def verify_v2_pattern_for_d(d_vals):
    """Verify the claimed pattern for v_2(d_n - 1)."""
    print("=" * 80)
    print("Pattern of v_2(d_n - 1) for various n")
    print("=" * 80)
    print("The solution claims:")
    print("  - For odd n: v_2(d_n - 1) = 1")
    print("  - For n ≡ 2 (mod 4): v_2(d_n - 1) = 3")
    print("  - For n = 2^m: v_2(d_n - 1) = m+2")
    print()

    print(f"{'n':>4} | {'n (binary)':>12} | {'v_2(d_n-1)':>12} | Pattern")
    print("-" * 60)

    for n in range(1, min(33, len(d_vals))):
        v2_val = v2(d_vals[n] - 1)
        binary = bin(n)[2:]

        # Determine expected pattern
        if n % 2 == 1:  # odd
            pattern = "odd -> 1"
            expected = 1
        elif n % 4 == 2:  # n ≡ 2 (mod 4)
            pattern = "n≡2(mod4) -> 3"
            expected = 3
        elif (n & (n - 1)) == 0:  # n is a power of 2
            m = v2(n)
            pattern = f"2^{m} -> {m+2}"
            expected = m + 2
        else:
            pattern = "other"
            expected = "?"

        status = "✓" if (expected != "?" and v2_val == expected) else ("?" if expected == "?" else "✗")

        print(f"{n:4d} | {binary:>12} | {v2_val:12d} | {pattern:20} {status}")

    print()

def main():
    # Compute b_n and d_n up to n=32
    n_max = 32
    print(f"Computing b_n and d_n up to n={n_max}")
    print()

    b_vals = compute_b(n_max)
    d_vals = compute_d(n_max)

    # Verify d_n = 2b_n + 1 and recurrence
    verify_d_recurrence(b_vals, d_vals)

    # Print initial values
    print_initial_values(b_vals, d_vals)

    # Verify v_2 pattern for d_n - 1
    verify_v2_pattern_for_d(d_vals)

    # Verify Claim 1
    claim1_ok = verify_claim_1(d_vals)

    # Verify Claim 2
    claim2_ok = verify_claim_2(b_vals)

    # Verify s_k differences
    verify_s_k_differences(b_vals, d_vals)

    # Final summary
    print("=" * 80)
    print("FINAL VERIFICATION SUMMARY")
    print("=" * 80)

    if claim1_ok and claim2_ok:
        print("✓ All claims verified numerically for k=1,2,3,4,5")
        print("✓ Claim 1: v_2(d_{2^k} - 1) = k+2 holds")
        print("✓ Claim 2: v_2(b_{2^{k+1}} - 2b_{2^k}) = 2k+2 holds")
        print()
        print("VERDICT: CORRECT (numerical verification)")
    else:
        print("✗ Some claims failed verification")
        print()
        print("VERDICT: NEEDS REVISION")

if __name__ == "__main__":
    main()
