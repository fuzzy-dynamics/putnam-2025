#!/usr/bin/env python3
"""Simple verification of Putnam 2025 A6."""

def v2(n):
    """2-adic valuation."""
    if n == 0:
        return float('inf')
    count = 0
    while n % 2 == 0:
        count += 1
        n //= 2
    return count

# Compute b_n
b = [0]  # b_0 = 0
for n in range(32):
    b_next = 2 * b[n]**2 + b[n] + 1
    b.append(b_next)

print("First few values of b_n:")
for i in range(min(10, len(b))):
    print(f"b_{i} = {b[i]}")

print("\nCompute d_n = 2b_n + 1:")
d = [2*b[i] + 1 for i in range(len(b))]
for i in range(min(10, len(d))):
    print(f"d_{i} = {d[i]}")

print("\nVerify d recurrence d_{n+1} = d_n(d_n-1) + 3:")
for i in range(min(5, len(d)-1)):
    expected = d[i] * (d[i] - 1) + 3
    actual = d[i+1]
    print(f"d_{i+1}: expected {expected}, actual {actual}, match: {expected == actual}")

print("\n" + "="*80)
print("CLAIM 1: v_2(d_{2^k} - 1) = k+2")
print("="*80)
for k in range(1, 6):
    idx = 2**k
    if idx >= len(d):
        break
    val = d[idx] - 1
    v2_val = v2(val)
    expected = k + 2
    # Extract s_k
    s_k = (d[idx] - 1) // (2**(k+2))
    s_k_odd = (s_k % 2 == 1)
    print(f"k={k}: d_{{{idx}}} = {d[idx]}, v_2(d_{{{idx}}}-1) = {v2_val}, expected = {expected}, s_{k} = {s_k}, odd = {s_k_odd}")

print("\n" + "="*80)
print("CLAIM 2: v_2(b_{2^{k+1}} - 2b_{2^k}) = 2k+2")
print("="*80)
for k in range(1, 6):
    idx_k = 2**k
    idx_k1 = 2**(k+1)
    if idx_k1 >= len(b):
        break
    diff = b[idx_k1] - 2*b[idx_k]
    v2_diff = v2(diff)
    expected = 2*k + 2
    not_by_higher = (diff % (2**(2*k+3)) != 0)
    print(f"k={k}: b_{{{idx_k1}}} - 2*b_{{{idx_k}}} = {diff}, v_2 = {v2_diff}, expected = {expected}, not by 2^{{{2*k+3}}}: {not_by_higher}")

print("\n" + "="*80)
print("s_k differences: verify v_2(s_{k+1} - s_k) = k")
print("="*80)
s_vals = []
for k in range(1, 6):
    idx = 2**k
    if idx >= len(d):
        break
    s_k = (d[idx] - 1) // (2**(k+2))
    s_vals.append((k, s_k))

for i in range(len(s_vals) - 1):
    k, s_k = s_vals[i]
    k1, s_k1 = s_vals[i+1]
    diff = s_k1 - s_k
    v2_diff = v2(diff) if diff != 0 else float('inf')
    print(f"k={k}: s_{k} = {s_k}, s_{{{k+1}}} = {s_k1}, diff = {diff}, v_2(diff) = {v2_diff}, expected = {k}")

print("\n" + "="*80)
print("Pattern of v_2(d_n - 1)")
print("="*80)
for n in range(1, min(33, len(d))):
    v = v2(d[n] - 1)
    is_pow2 = (n & (n-1)) == 0
    if is_pow2:
        m = v2(n)
        expected = m + 2
        print(f"n={n:2d} (2^{m}): v_2(d_{n}-1) = {v}, expected = {expected}")
    elif n % 2 == 1:
        if n <= 9:
            print(f"n={n:2d} (odd): v_2(d_{n}-1) = {v}, expected = 1")
    elif n % 4 == 2:
        if n <= 10:
            print(f"n={n:2d} (≡2 mod 4): v_2(d_{n}-1) = {v}, expected = 3")
