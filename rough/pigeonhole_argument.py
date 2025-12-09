#!/usr/bin/env python3
"""
Pigeonhole-based argument for B5.

Key insight: The permutation I must satisfy certain constraints.
Since I is an involution with specific structure, we can bound inversions from below.
"""

def modinv(k, p):
    return pow(k, -1, p)

def detailed_structure(p):
    """
    Analyze the structure more carefully.

    KEY FACTS:
    1. I is an involution: I(I(k)) = k
    2. Fixed points: I(1) = 1, I(p-1) = p-1
    3. Middle values: I((p+1)/2) = 2, I((p-1)/2) = p-2
    4. Symmetry: I(p-k) = p - I(k)

    Question: Can we bound inversions using these constraints?
    """
    I = [0] + [modinv(k, p) for k in range(1, p)]

    print(f"\n{'='*60}")
    print(f"p = {p}")
    print(f"{'='*60}")

    # Consider the first few and last few positions
    print("First few:")
    for k in range(1, min(5, p)):
        print(f"  I({k}) = {I[k]}")

    print("Last few:")
    for k in range(max(1, p-4), p):
        print(f"  I({k}) = {I[k]}")

    # Key observation: I(1) = 1, I(2) = (p+1)/2
    # So from position 1 to position 2, we jump from 1 to (p+1)/2
    # This is a huge jump!

    # From position 2 to position 3: I(2) = (p+1)/2 to I(3) = ?
    # If I(3) < (p+1)/2, then position 2 has an inversion

    jump_1_to_2 = I[2] - I[1]
    print(f"\nJump from I(1) to I(2): {I[1]} -> {I[2]} (+{jump_1_to_2})")

    if 3 <= p-1:
        jump_2_to_3 = I[3] - I[2]
        print(f"Jump from I(2) to I(3): {I[2]} -> {I[3]} ({jump_2_to_3:+d})")
        if I[3] < I[2]:
            print("  -> Position 2 has an INVERSION")

    # Now, the key question: for which primes does position 2 have an inversion?
    # This happens when I(3) < (p+1)/2

    # We know I(3) = inverse of 3 mod p
    # For p = 2 mod 3: I(3) = (p+1)/3
    # For p = 1 mod 3: I(3) = (2p+1)/3

    if p % 3 == 2:
        I_3_formula = (p+1)//3
        print(f"\np ≡ 2 (mod 3), so I(3) = (p+1)/3 = {I_3_formula}")
        print(f"I(2) = (p+1)/2 = {(p+1)//2}")
        print(f"I(3) < I(2)? {I_3_formula} < {(p+1)//2}? {I_3_formula < (p+1)//2}")
    elif p % 3 == 1:
        I_3_formula = (2*p+1)//3
        print(f"\np ≡ 1 (mod 3), so I(3) = (2p+1)/3 = {I_3_formula}")
        print(f"I(2) = (p+1)/2 = {(p+1)//2}")
        print(f"I(3) < I(2)? {I_3_formula} < {(p+1)//2}? {I_3_formula < (p+1)//2}")

    inversions = sum(1 for k in range(1, p-1) if I[k+1] < I[k])
    bound = p/4 - 1

    print(f"\nInversions: {inversions}, Bound: {bound:.2f}, Exceeds: {inversions > bound}")

for p in [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]:
    detailed_structure(p)

print("\n" + "="*60)
print("PATTERN ANALYSIS")
print("="*60)

# Check the pattern: when does position 2 have an inversion?

pos_2_inversions = []
for p in [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83]:
    is_prime = p > 1 and all(p % i != 0 for i in range(2, int(p**0.5) + 1))
    if not is_prime:
        continue

    I = [0] + [modinv(k, p) for k in range(1, p)]

    has_inv_at_2 = I[3] < I[2] if 3 < p else False

    if has_inv_at_2:
        pos_2_inversions.append(p)
        print(f"p = {p:2d} (mod 3 = {p % 3}, mod 12 = {p % 12:2d}): Position 2 HAS inversion")
    else:
        print(f"p = {p:2d} (mod 3 = {p % 3}, mod 12 = {p % 12:2d}): Position 2 NO inversion")

print(f"\nPrimes where position 2 has inversion: {pos_2_inversions}")

# Pattern: position 2 has inversion iff p ≡ 2 (mod 3)
