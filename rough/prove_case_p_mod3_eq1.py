#!/usr/bin/env python3
"""
For p ≡ 1 (mod 3), we know:
- I(2) = (p+1)/2
- I(3) = (2p+1)/3
- Position 2: I(3) > I(2) (no inversion)

Check position 3: does I(4) < I(3)?
We need to find I(4).

4 * I(4) ≡ 1 (mod p)
I(4) ≡ 4^{-1} (mod p)

For p ≡ 1 (mod 4): I(4) = (3p+1)/4
For p ≡ 3 (mod 4): I(4) = (p+1)/4
"""

def modinv(k, p):
    return pow(k, -1, p)

print("Primes p ≡ 1 (mod 3), p >= 11:")
print("="*70)

for p in [13, 19, 31, 37, 43, 61, 67, 73, 79]:
    I = [0] + [modinv(k, p) for k in range(1, p)]

    I_2 = I[2]
    I_3 = I[3]
    I_4 = I[4]

    # Theoretical values
    I_2_theory = (p+1)//2
    I_3_theory = (2*p+1)//3
    I_4_theory_mod4_eq1 = (3*p+1)//4
    I_4_theory_mod4_eq3 = (p+1)//4

    mod_3 = p % 3
    mod_4 = p % 4
    mod_12 = p % 12

    print(f"\np = {p} ≡ {mod_12} (mod 12)")
    print(f"  I(2) = {I_2}, theory = (p+1)/2 = {I_2_theory}, match: {I_2 == I_2_theory}")
    print(f"  I(3) = {I_3}, theory = (2p+1)/3 = {I_3_theory}, match: {I_3 == I_3_theory}")

    if mod_4 == 1:
        print(f"  I(4) = {I_4}, theory = (3p+1)/4 = {I_4_theory_mod4_eq1}, match: {I_4 == I_4_theory_mod4_eq1}")
        I_4_theory = I_4_theory_mod4_eq1
    else:
        print(f"  I(4) = {I_4}, theory = (p+1)/4 = {I_4_theory_mod4_eq3}, match: {I_4 == I_4_theory_mod4_eq3}")
        I_4_theory = I_4_theory_mod4_eq3

    # Check inversions
    inv_at_3 = I_4 < I_3
    inv_at_4 = I[5] < I_4 if p > 5 else False

    print(f"  Position 3: I(3)={I_3}, I(4)={I_4}, I(4) < I(3)? {inv_at_3}")

    if inv_at_3:
        print(f"    -> Position 3 HAS inversion! By pairing, position {p-4} also has inversion.")
        print(f"    -> Therefore B >= 1 ✓")

print("\n" + "="*70)
print("ANALYSIS:")
print("="*70)

print("\nFor p ≡ 1 (mod 3), we have I(3) = (2p+1)/3.")
print("\nPosition 3 has inversion iff I(4) < I(3) = (2p+1)/3.")

print("\nCase 1: p ≡ 1 (mod 12), so p ≡ 1 (mod 3) and p ≡ 1 (mod 4)")
print("  I(4) = (3p+1)/4")
print("  Check: (3p+1)/4 < (2p+1)/3")
print("         3(3p+1) < 4(2p+1)")
print("         9p + 3 < 8p + 4")
print("         p < 1  [FALSE]")
print("  So position 3 has NO inversion for p ≡ 1 (mod 12).")

print("\nCase 2: p ≡ 7 (mod 12), so p ≡ 1 (mod 3) and p ≡ 3 (mod 4)")
print("  I(4) = (p+1)/4")
print("  Check: (p+1)/4 < (2p+1)/3")
print("         3(p+1) < 4(2p+1)")
print("         3p + 3 < 8p + 4")
print("         -1 < 5p  [TRUE for p > 0]")
print("  So position 3 HAS an inversion for p ≡ 7 (mod 12)! ✓")

print("\nFor p ≡ 7 (mod 12), position 3 has an inversion,")
print("and by Lemma 3, position p-4 also has an inversion.")
print("Therefore B >= 1 for all primes p ≡ 7 (mod 12).")

print("\nWhat about p ≡ 1 (mod 12)?")
print("Need to check other positions...")

# Check p ≡ 1 (mod 12) more carefully
print("\n" + "="*70)
print("DETAILED ANALYSIS: p ≡ 1 (mod 12)")
print("="*70)

for p in [13, 37, 61, 73]:  # Primes ≡ 1 (mod 12)
    I = [0] + [modinv(k, p) for k in range(1, p)]

    print(f"\np = {p} ≡ 1 (mod 12)")

    # Find first inversion (excluding the middle)
    mid = (p-1)//2
    first_inv = None
    for k in range(1, mid):
        if I[k+1] < I[k]:
            first_inv = k
            break

    if first_inv:
        print(f"  First inversion at position {first_inv}")
        print(f"  I({first_inv}) = {I[first_inv]}, I({first_inv+1}) = {I[first_inv+1]}")
        print(f"  By pairing, position {p-1-first_inv} also has inversion.")
        print(f"  Therefore B >= 1 ✓")
