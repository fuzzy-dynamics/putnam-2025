"""
Rigorous analysis to understand WHY we get >= p/4 - 1 inversions.

Key question: Can we prove a lower bound on the number of inversions?
"""

def mod_inverse(k, p):
    return pow(k, p - 2, p)

def rigorous_count(p):
    """
    Rigorous counting argument.

    Partition at p/2 gives us A = {1, ..., (p-1)/2} and B = {(p+1)/2, ..., p-1}.

    Key facts:
    1. |A| = |B| = (p-1)/2
    2. I is a bijection, so exactly (p-1)/2 elements map to A and (p-1)/2 map to B
    3. Since I(1) = 1, we have 1 ∈ I(A) (since 1 ∈ A)
    4. Since I(p-1) = p-1, we have p-1 ∈ I(B) (since p-1 ∈ B)

    Let's count more carefully.
    """
    inv_map = {k: mod_inverse(k, p) for k in range(1, p)}

    # Partition
    A = set(range(1, (p+1)//2))
    B = set(range((p+1)//2, p))

    print(f"\n{'='*70}")
    print(f"p = {p}")
    print(f"A = {{1, ..., {max(A)}}}, |A| = {len(A)}")
    print(f"B = {{{min(B)}, ..., {p-1}}}, |B| = {len(B)}")
    print(f"{'='*70}")

    # Elements of A that map to A
    A_to_A = [k for k in A if inv_map[k] in A]
    A_to_B = [k for k in A if inv_map[k] in B]
    B_to_A = [k for k in B if inv_map[k] in A]
    B_to_B = [k for k in B if inv_map[k] in B]

    print(f"\nMapping structure:")
    print(f"  A → A: {len(A_to_A)} elements")
    print(f"  A → B: {len(A_to_B)} elements")
    print(f"  B → A: {len(B_to_A)} elements")
    print(f"  B → B: {len(B_to_B)} elements")

    # Since I is a bijection, A_to_A = B_to_A (both count elements that map to A)
    # and A_to_B = B_to_B (both count elements that map to B)
    print(f"\nConsistency check:")
    print(f"  |A_to_A| + |B_to_A| = {len(A_to_A) + len(B_to_A)}, should be |A| = {len(A)}")
    print(f"  |A_to_B| + |B_to_B| = {len(A_to_B) + len(B_to_B)}, should be |B| = {len(B)}")

    # Count consecutive pairs
    pairs_AA = 0  # k, k+1 both in A
    pairs_AB = 0  # k in A, k+1 in B (crossing)
    pairs_BB = 0  # k, k+1 both in B

    for k in range(1, p-1):
        if k in A and k+1 in A:
            pairs_AA += 1
        elif k in A and k+1 in B:
            pairs_AB += 1
        elif k in B and k+1 in B:
            pairs_BB += 1

    print(f"\nConsecutive pairs:")
    print(f"  Both in A: {pairs_AA}")
    print(f"  Cross A→B: {pairs_AB}")
    print(f"  Both in B: {pairs_BB}")
    print(f"  Total: {pairs_AA + pairs_AB + pairs_BB}")

    # Count inversions
    inv_AA = 0
    inv_AB = 0
    inv_BB = 0

    for k in range(1, p-1):
        if inv_map[k+1] < inv_map[k]:
            if k in A and k+1 in A:
                inv_AA += 1
            elif k in A and k+1 in B:
                inv_AB += 1
            elif k in B and k+1 in B:
                inv_BB += 1

    total_inv = inv_AA + inv_AB + inv_BB

    print(f"\nInversions:")
    print(f"  In A: {inv_AA} out of {pairs_AA}")
    print(f"  Cross: {inv_AB} out of {pairs_AB}")
    print(f"  In B: {inv_BB} out of {pairs_BB}")
    print(f"  Total: {total_inv}")
    print(f"  Required bound: > {p/4 - 1:.2f}")
    print(f"  Passes: {total_inv > p/4 - 1}")

    # KEY OBSERVATION: Let's see if inv_AA + inv_BB >= (p-3)/4
    print(f"\nKey inequality check:")
    print(f"  inv_AA + inv_BB = {inv_AA + inv_BB}")
    print(f"  (p-3)/4 = {(p-3)/4:.2f}")
    print(f"  Inequality holds: {inv_AA + inv_BB >= (p-3)/4}")

    # Another angle: what if we just count pairs both in A?
    # We have (p-1)/2 - 1 = (p-3)/2 consecutive pairs both in A
    # If at least 1/2 of them have inversions, we get (p-3)/4 inversions
    # Plus the crossing inversion gives (p-3)/4 + 1 = (p+1)/4
    # But we need > p/4 - 1

    # (p+1)/4 > p/4 - 1
    # p + 1 > p - 4
    # 1 > -4 ✓ Always true!

    print(f"\nSimplified bound check:")
    print(f"  If inv_cross >= 1 and (inv_AA + inv_BB) >= (p-3)/4:")
    print(f"    Total >= 1 + (p-3)/4 = (p+1)/4")
    print(f"    Need: > p/4 - 1")
    print(f"    Check: (p+1)/4 > p/4 - 1?")
    print(f"    => p + 1 > p - 4?")
    print(f"    => 5 > 0? YES!")

    return total_inv, p/4 - 1

# Test
for p in [7, 11, 13, 17, 19, 23, 29, 31, 37]:
    rigorous_count(p)

print("\n" + "="*70)
print("PROOF STRATEGY")
print("="*70)
print("""
To prove the bound, we need to show:
1. There is at least 1 crossing inversion
2. Among pairs in A and B, at least (p-3)/4 have inversions

This gives total >= 1 + (p-3)/4 = (p+1)/4 > p/4 - 1.

The question is: can we PROVE that (inv_AA + inv_BB) >= (p-3)/4?
""")
