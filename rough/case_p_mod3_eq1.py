#!/usr/bin/env python3
"""
For primes p ≡ 1 (mod 3), position 2 does NOT have an inversion.
Check which positions DO have inversions.
"""

def modinv(k, p):
    return pow(k, -1, p)

# Primes p ≡ 1 (mod 3) and p > 3
primes_mod3_eq1 = [7, 13, 19, 31, 37, 43, 61, 67, 73, 79]

for p in primes_mod3_eq1:
    I = [0] + [modinv(k, p) for k in range(1, p)]

    print(f"\n{'='*60}")
    print(f"p = {p} ≡ 1 (mod 3)")
    print(f"{'='*60}")

    # Find first few positions with inversions
    first_inversions = []
    for k in range(1, min(10, p-1)):
        if I[k+1] < I[k]:
            first_inversions.append(k)
            if len(first_inversions) <= 3:
                print(f"Position {k}: I({k})={I[k]}, I({k+1})={I[k+1]} [INVERSION]")

    print(f"First inversions at positions: {first_inversions[:5]}")

    # Check the middle position (should always have inversion)
    mid = (p-1)//2
    if I[mid+1] < I[mid]:
        print(f"Middle position {mid}: I({mid})={I[mid]}, I({mid+1})={I[mid+1]} [INVERSION] ✓")

    total_inversions = sum(1 for k in range(1, p-1) if I[k+1] < I[k])
    bound = p/4 - 1

    print(f"\nTotal inversions: {total_inversions}")
    print(f"Bound: {bound:.2f}")
    print(f"Margin: {total_inversions - bound:.2f}")

    # Check paired inversions
    mid = (p-1)//2
    B = 0
    for k in range(1, mid):
        k_prime = p - 1 - k
        if I[k+1] < I[k] and I[k_prime+1] < I[k_prime]:
            B += 1

    print(f"B (paired inversions) = {B}")
    print(f"2B + 1 = {2*B + 1}")

print("\n" + "="*60)
print("SUMMARY: For p ≡ 1 (mod 3)")
print("="*60)

print("\nAll have at least 1 inversion (the middle position).")
print("For p = 5, 7: B = 0, total = 1 > bound ✓")
print("For p ≥ 11: Need to check if B ≥ 1")

# Check B for p ≡ 1 (mod 3) and p ≥ 11
print("\nB values for p ≡ 1 (mod 3), p ≥ 11:")
for p in [13, 19, 31, 37, 43, 61, 67, 73, 79]:
    I = [0] + [modinv(k, p) for k in range(1, p)]
    mid = (p-1)//2
    B = sum(1 for k in range(1, mid)
            if I[k+1] < I[k] and I[p-k] < I[p-1-k])

    print(f"  p = {p}: B = {B}, 2B+1 = {2*B+1}, bound = {p/4-1:.2f}")
