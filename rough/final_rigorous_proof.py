#!/usr/bin/env python3
"""
Final rigorous proof attempt.

KEY INSIGHT: We need to prove inversions > p/4 - 1.

Since inversions = 2B + 1, we need:
2B + 1 > p/4 - 1
2B > p/4 - 2
B > p/8 - 1

For p >= 11, we need B >= 1 (since B is an integer).
For p = 5, 7: B = 0 but inversions = 1 still beats the bound.

The challenge: PROVE that B >= 1 for p >= 11 without computation.

Alternative approach: Prove directly that at least one pair (k, p-1-k) with k != mid
has inversions.
"""

def modinv(k, p):
    return pow(k, -1, p)

def detailed_analysis(p):
    """Detailed analysis to find the key mathematical insight"""
    I = [0] + [modinv(k, p) for k in range(1, p)]

    print(f"\n{'='*60}")
    print(f"p = {p}")
    print(f"{'='*60}")

    mid = (p-1)//2

    # Check specific positions
    print(f"\nKey positions:")
    print(f"I(1) = {I[1]} (always 1)")
    print(f"I(2) = {I[2]} (inverse of 2)")
    print(f"I({mid}) = {I[mid]} (mid)")
    print(f"I({mid+1}) = {I[mid+1]} (mid+1, always 2)")
    print(f"I(p-2) = I({p-2}) = {I[p-2]}")
    print(f"I(p-1) = I({p-1}) = {I[p-1]} (always p-1)")

    # Key question: when does position 2 have an inversion?
    # Position 2 has inversion if I(3) < I(2)
    if 3 <= p-1:
        has_inversion_at_2 = I[3] < I[2]
        print(f"\nPosition 2: I(2)={I[2]}, I(3)={I[3]}, has inversion? {has_inversion_at_2}")

    # Position p-3 has inversion if I(p-2) < I(p-3)
    if p >= 5:
        has_inversion_at_pm3 = I[p-2] < I[p-3]
        print(f"Position p-3={p-3}: I({p-3})={I[p-3]}, I({p-2})={I[p-2]}, has inversion? {has_inversion_at_pm3}")

    # By pairing, if position 2 has inversion, so does position p-1-2 = p-3
    # Position 2 pairs with position p-3

    # Actually, let me verify the pairing claim more carefully
    for k in range(1, mid+1):
        k_prime = p - 1 - k
        if k == k_prime:
            continue  # Skip the middle position

        k_has_inv = I[k+1] < I[k] if k+1 < p else False
        kp_has_inv = I[k_prime+1] < I[k_prime] if k_prime+1 < p else False

        if k_has_inv != kp_has_inv:
            print(f"ERROR: Pairing broken at k={k}, k'={k_prime}")

    # Count B
    B = 0
    for k in range(1, mid):
        k_prime = p - 1 - k
        k_has_inv = I[k+1] < I[k]
        kp_has_inv = I[k_prime+1] < I[k_prime]
        if k_has_inv and kp_has_inv:
            B += 1
            print(f"Pair ({k}, {k_prime}) both have inversions")

    print(f"\nB = {B}")
    print(f"Total inversions = 2B + 1 = {2*B + 1}")

    inversions_actual = sum(1 for k in range(1, p-1) if I[k+1] < I[k])
    print(f"Actual inversions: {inversions_actual}")

    # What if we look at small k?
    print(f"\nLooking at small positions:")
    for k in range(1, min(5, p-1)):
        if k+1 < p:
            inv = "INV" if I[k+1] < I[k] else "---"
            print(f"k={k}: I({k})={I[k]:2d}, I({k+1})={I[k+1]:2d} {inv}")

for p in [5, 7, 11, 13, 17, 19, 23]:
    detailed_analysis(p)

print("\n" + "="*60)
print("THEORETICAL ARGUMENT ATTEMPT")
print("="*60)

# Let's think about this differently
# For small p:
# p=5: inversions=1 > 0.25 ✓
# p=7: inversions=1 > 0.75 ✓

# For p >= 11, we claim B >= 1, i.e., at least one pair has inversions

# Consider position 2: has inversion if I(3) < I(2)
# We know I(2) = (p+1)/2 (the inverse of 2)

# Wait, let me verify I(2)
for p in [5, 7, 11, 13, 17, 19, 23, 29]:
    I_2 = modinv(2, p)
    expected = (p+1)//2
    print(f"p={p}: I(2) = {I_2}, (p+1)/2 = {expected}, match? {I_2 == expected}")
