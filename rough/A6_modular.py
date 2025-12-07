#!/usr/bin/env python3
"""
Analyze b_n modulo powers of 2 to understand the structure
"""
import sys
sys.set_int_max_str_digits(100000)

def compute_mod(b_n, modulus):
    """Compute next term modulo a power of 2"""
    return (2 * b_n**2 + b_n + 1) % modulus

def v2(n):
    """Compute 2-adic valuation"""
    if n == 0:
        return float('inf')
    count = 0
    while n % 2 == 0:
        count += 1
        n //= 2
    return count

def analyze_doubling_map(k):
    """
    Analyze the map from b_{2^k} to b_{2^{k+1}}
    Track values modulo 2^{2k+3}
    """
    print(f"\n{'='*60}")
    print(f"Analyzing k={k}: b_{{2^{k}}} → b_{{2^{k+1}}}")
    print(f"{'='*60}")

    # Compute the actual values
    b = [0]
    for i in range(2**(k+1) + 1):
        b_next = 2 * b[-1]**2 + b[-1] + 1
        b.append(b_next)

    idx1 = 2**k
    idx2 = 2**(k+1)

    print(f"\nb_{{2^{k}}} = b_{{{idx1}}}")
    print(f"v_2(b_{{{idx1}}}) = {v2(b[idx1])}")

    print(f"\nb_{{2^{k+1}}} = b_{{{idx2}}}")
    print(f"v_2(b_{{{idx2}}}) = {v2(b[idx2])}")

    # Key difference
    diff = b[idx2] - 2*b[idx1]
    print(f"\nb_{{{idx2}}} - 2*b_{{{idx1}}}:")
    print(f"v_2(diff) = {v2(diff)} (expected: {2*k+2})")

    # Check modulo various powers
    for m in range(2*k+1, 2*k+5):
        mod = 2**m
        val_mod = diff % mod
        print(f"diff mod 2^{m} = {val_mod}")

    # Extract the pattern
    exact_val = v2(diff)
    odd_part = diff // (2**exact_val)
    print(f"\nOdd part: {odd_part % 16} (mod 16)")

    # Now analyze the structure of b_{2^k} more carefully
    print(f"\nStructure of b_{{2^{k}}}:")
    val_k = v2(b[idx1])
    print(f"b_{{2^{k}}} = 2^{val_k} · c where c = {b[idx1] // (2**val_k)} is odd")
    print(f"b_{{2^{k}}} mod 2^{{{val_k+2}}} = {b[idx1] % (2**(val_k+2))}")

    # Check the form b_{2^k} ≡ 2^{k+1} (mod 2^{k+2})
    expected_form = 2**(k+1)
    actual_mod = b[idx1] % (2**(k+2))
    print(f"b_{{2^{k}}} mod 2^{{{k+2}}} = {actual_mod} (expected: {expected_form})")
    print(f"Match: {actual_mod == expected_form}")

def main():
    """Run analysis for k=1,2,3"""
    for k in range(1, 4):
        analyze_doubling_map(k)

if __name__ == "__main__":
    main()
