#!/usr/bin/env python3
"""
Check if the bound p/4 - 1 is actually achieved or tight.
"""

def modinv(k, p):
    return pow(k, -1, p)

def count_inversions(p):
    I = [0] + [modinv(k, p) for k in range(1, p)]
    inversions = sum(1 for k in range(1, p-1) if I[k+1] < I[k])
    return inversions

print("p | Inversions | p/4-1 | Inversions > p/4-1?")
print("-" * 50)

for p in [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]:
    inv = count_inversions(p)
    bound = p/4 - 1
    passes = "YES" if inv > bound else "NO"
    print(f"{p:2d} | {inv:10d} | {bound:5.2f} | {passes}")

# Key question: what's the minimum excess?
print("\n" + "="*50)
print("Minimum margin over bound:")
min_margin = float('inf')
worst_p = None

for p in range(5, 200):
    # Check if p is prime
    if p < 2:
        continue
    is_prime = all(p % i != 0 for i in range(2, int(p**0.5) + 1))
    if not is_prime:
        continue

    inv = count_inversions(p)
    bound = p/4 - 1
    margin = inv - bound

    if margin < min_margin:
        min_margin = margin
        worst_p = p

print(f"Worst case: p={worst_p}, margin={min_margin:.2f}")

# For p=5,7: inversions = 1, bound = 0.25, 0.75
# So we still beat the bound!
