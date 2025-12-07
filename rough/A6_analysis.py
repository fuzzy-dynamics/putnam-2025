#!/usr/bin/env python3
"""
Deeper analysis of the sequence modulo powers of 2
"""
import sys
sys.set_int_max_str_digits(100000)

def v2(n):
    """Compute 2-adic valuation of n"""
    if n == 0:
        return float('inf')
    count = 0
    while n % 2 == 0:
        count += 1
        n //= 2
    return count

def compute_sequence(max_n=20):
    """Compute b_0, b_1, ..., b_max_n"""
    b = [0]
    for n in range(max_n):
        b_next = 2 * b[n]**2 + b[n] + 1
        b.append(b_next)
    return b

def analyze_mod_powers_of_2():
    """Analyze b_n modulo powers of 2"""
    b = compute_sequence(20)

    print("="*60)
    print("Analysis of b_{2^k} modulo 2^{k+2}")
    print("="*60)

    for k in range(1, 5):
        idx = 2**k
        if idx < len(b):
            modulus = 2**(k+2)
            val = b[idx] % modulus
            val_div = b[idx] // (2**(k+1))

            print(f"\nk = {k}:")
            print(f"  b_{{2^{k}}} = b_{{{idx}}}")
            print(f"  v_2(b_{{2^{k}}}) = {v2(b[idx])}")
            print(f"  b_{{2^{k}}} mod 2^{{{k+2}}} = {val}")
            print(f"  b_{{2^{k}}} / 2^{{{k+1}}} mod 2 = {val_div % 2}")

    print("\n" + "="*60)
    print("Analysis of the recurrence for b_{2^k}")
    print("="*60)

    # The recurrence is: b_{n+1} = 2b_n^2 + b_n + 1
    # Let's see what happens when we iterate from b_{2^k} to b_{2^{k+1}}

    for k in range(1, 4):
        idx = 2**k
        if idx < len(b):
            print(f"\nk = {k}: Computing from b_{{{idx}}} to b_{{{2*idx}}}:")
            print(f"  b_{{{idx}}} has v_2 = {v2(b[idx])}")

            # Check a few intermediate values
            current = b[idx]
            for i in range(5):
                next_val = 2 * current**2 + current + 1
                print(f"    After {i+1} step(s): v_2 = {v2(next_val)}")
                current = next_val
                if idx + i + 1 <= 2*idx and idx + i + 1 < len(b):
                    print(f"      (b_{{{idx + i + 1}}} has v_2 = {v2(b[idx + i + 1])})")

    print("\n" + "="*60)
    print("Direct computation of b_{2^{k+1}} - 2b_{2^k}")
    print("="*60)

    for k in range(1, 4):
        idx1 = 2**(k+1)
        idx2 = 2**k
        if idx1 < len(b):
            diff = b[idx1] - 2*b[idx2]
            val = v2(diff)

            # Extract the odd part
            odd_part = diff // (2**val)

            print(f"\nk = {k}:")
            print(f"  b_{{{idx1}}} - 2*b_{{{idx2}}}")
            print(f"  v_2(diff) = {val} = 2*{k} + 2")
            print(f"  diff / 2^{val} = {odd_part} (odd part)")
            print(f"  odd part mod 8 = {odd_part % 8}")

if __name__ == "__main__":
    analyze_mod_powers_of_2()
