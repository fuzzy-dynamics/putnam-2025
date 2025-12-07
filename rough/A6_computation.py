#!/usr/bin/env python3
"""
Compute the sequence b_n and analyze 2-adic valuations
"""
import sys
sys.set_int_max_str_digits(100000)

def v2(n):
    """Compute 2-adic valuation of n (highest power of 2 dividing n)"""
    if n == 0:
        return float('inf')
    count = 0
    while n % 2 == 0:
        count += 1
        n //= 2
    return count

def compute_sequence(max_n=20):
    """Compute b_0, b_1, ..., b_max_n"""
    b = [0]  # b_0 = 0
    for n in range(max_n):
        b_next = 2 * b[n]**2 + b[n] + 1
        b.append(b_next)
    return b

def analyze_sequence():
    """Compute and analyze the sequence"""
    b = compute_sequence(20)

    print("Sequence terms and 2-adic valuations:")
    print("n\tb_n\t\tv_2(b_n)")
    print("-" * 50)
    for n in range(min(10, len(b))):
        val = v2(b[n]) if b[n] != 0 else "inf"
        print(f"{n}\t{b[n]}\t\t{val}")

    print("\n" + "="*50)
    print("Powers of 2:")
    print("="*50)

    # Compute for powers of 2
    for k in range(1, 5):
        idx = 2**k
        if idx < len(b):
            val = v2(b[idx])
            # Only print the 2-adic valuation, not the full number
            print(f"b_{{2^{k}}} (index {idx}): v_2 = {val}, has {len(str(b[idx]))} digits")
            print()

    print("="*50)
    print("Testing the divisibility condition:")
    print("="*50)

    # Test b_{2^{k+1}} - 2*b_{2^k}
    for k in range(1, 4):
        idx1 = 2**(k+1)
        idx2 = 2**k
        if idx1 < len(b):
            diff = b[idx1] - 2*b[idx2]
            val = v2(diff)
            expected_min = 2*k + 2
            expected_max = 2*k + 2  # Should be exactly this

            print(f"k = {k}:")
            print(f"  b_{{2^{k+1}}} - 2*b_{{2^k}} = b_{{{idx1}}} - 2*b_{{{idx2}}}")
            print(f"  diff has {len(str(abs(diff)))} digits")
            print(f"  v_2(diff) = {val}")
            print(f"  Expected: divisible by 2^{expected_min} but not 2^{expected_min+1}")
            print(f"  Check: v_2 = {expected_min}? {val == expected_min}")
            print()

if __name__ == "__main__":
    analyze_sequence()
