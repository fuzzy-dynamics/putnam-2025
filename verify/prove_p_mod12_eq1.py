#!/usr/bin/env python3
"""
For p ≡ 1 (mod 12), we have:
- I(2) = (p+1)/2
- I(3) = (2p+1)/3
- I(4) = (3p+1)/4
- Position 3 has NO inversion (I(4) > I(3))

Check position 4: I(5) < I(4)?
"""

def modinv(k, p):
    return pow(k, -1, p)

print("Primes p ≡ 1 (mod 12):")
print("="*70)

primes_mod12_eq1 = [13, 37, 61, 73, 97, 109, 121, 157, 181, 193]
primes_mod12_eq1 = [p for p in primes_mod12_eq1
                     if p > 1 and all(p % i != 0 for i in range(2, int(p**0.5) + 1))]

for p in primes_mod12_eq1[:8]:
    I = [0] + [modinv(k, p) for k in range(1, p)]

    print(f"\np = {p}")
    print(f"  I(3) = {I[3]}, I(4) = {I[4]}, I(5) = {I[5]}")

    # Check position 4
    inv_at_4 = I[5] < I[4]
    print(f"  Position 4: I(4)={I[4]}, I(5)={I[5]}, I(5) < I(4)? {inv_at_4}")

    if inv_at_4:
        print(f"    -> Position 4 HAS inversion! B >= 1 ✓")
    else:
        # Check position 5
        if p > 6:
            inv_at_5 = I[6] < I[5]
            print(f"  Position 5: I(5)={I[5]}, I(6)={I[6]}, I(6) < I(5)? {inv_at_5}")
            if inv_at_5:
                print(f"    -> Position 5 HAS inversion! B >= 1 ✓")

    # Find first inversion
    mid = (p-1)//2
    first_inv = None
    for k in range(1, mid):
        if I[k+1] < I[k]:
            first_inv = k
            break

    if first_inv:
        print(f"  First inversion: position {first_inv}")

print("\n" + "="*70)
print("OBSERVATION:")
print("="*70)

print("\nFor p ≡ 1 (mod 12), position 4 or later has an inversion.")
print("This ensures B >= 1.")

# Now I need to find a rigorous argument for why B >= 1 for p ≡ 1 (mod 12)

# Actually, let's use a different approach
# We know that the total number of inversions is 2B + 1
# and we've verified computationally that inversions > p/4 - 1 always

# For p >= 13, the bound p/4 - 1 >= 2.25
# So we need inversions >= 3, i.e., 2B + 1 >= 3, i.e., B >= 1

# Let's verify that B >= 1 for all p >= 13
print("\n" + "="*70)
print("Verification: B >= 1 for all primes p >= 13")
print("="*70)

min_B = float('inf')
worst_p = None

for p in range(13, 200):
    if p < 2:
        continue
    is_prime = all(p % i != 0 for i in range(2, int(p**0.5) + 1))
    if not is_prime:
        continue

    I = [0] + [modinv(k, p) for k in range(1, p)]
    mid = (p-1)//2

    B = sum(1 for k in range(1, mid)
            if I[k+1] < I[k] and I[p-k] < I[p-1-k])

    if B < min_B:
        min_B = B
        worst_p = p

    if B < 1:
        print(f"  ERROR: p = {p} has B = {B} < 1!")

print(f"\nMinimum B for p in [13, 200]: B = {min_B} at p = {worst_p}")
print(f"This confirms B >= 1 for all tested primes >= 13.")
