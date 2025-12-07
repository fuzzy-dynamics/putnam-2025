"""
Clean proof approach for Putnam 2025 B5.

MAIN IDEA:
Partition {1, ..., p-1} into two halves at p/2.
For each consecutive pair (k, k+1), analyze when I(k+1) < I(k).

KEY INSIGHT:
If both I(k) and I(k+1) are on the SAME side of p/2, then we can reason
about when we get an inversion.

Let A = {1, ..., floor((p-1)/2)} and B = {ceil((p+1)/2), ..., p-1}.
"""

def mod_inverse(k, p):
    return pow(k, p - 2, p)

def clean_analysis(p):
    """
    Clean analysis using halves A and B.
    """
    I = {k: mod_inverse(k, p) for k in range(1, p)}

    # Define A and B
    mid = p / 2
    A = set(k for k in range(1, p) if k < mid)
    B = set(k for k in range(1, p) if k > mid)

    print(f"\n{'='*70}")
    print(f"p = {p}, mid = {mid}")
    print(f"A = {{1, ..., {max(A)}}}, |A| = {len(A)}")
    print(f"B = {{{min(B)}, ..., {max(B)}}}, |B| = {len(B)}")
    print(f"{'='*70}")

    # Since I is a bijection, exactly |A| elements map to A and |B| map to B
    # Verify this
    I_A_count = sum(1 for k in range(1, p) if I[k] in A)
    I_B_count = sum(1 for k in range(1, p) if I[k] in B)

    print(f"\nImage counts:")
    print(f"  |I^{{-1}}(A)| = {I_A_count}, should be {len(A)}")
    print(f"  |I^{{-1}}(B)| = {I_B_count}, should be {len(B)}")

    # Count inversions based on where k and I(k) lie
    categories = {
        'k_in_A_Ik_in_A': [],
        'k_in_A_Ik_in_B': [],
        'k_in_B_Ik_in_A': [],
        'k_in_B_Ik_in_B': [],
    }

    for k in range(1, p):
        k_in_A = k in A
        Ik_in_A = I[k] in A

        if k_in_A and Ik_in_A:
            categories['k_in_A_Ik_in_A'].append(k)
        elif k_in_A and not Ik_in_A:
            categories['k_in_A_Ik_in_B'].append(k)
        elif not k_in_A and Ik_in_A:
            categories['k_in_B_Ik_in_A'].append(k)
        else:
            categories['k_in_B_Ik_in_B'].append(k)

    print(f"\nCategories:")
    for name, elems in categories.items():
        print(f"  {name}: {len(elems)}")

    # Now count inversions
    inversions = []
    for k in range(1, p - 1):
        if I[k+1] < I(k):
            inversions.append(k)

    print(f"\nTotal inversions: {len(inversions)} out of {p-2}")
    print(f"Required bound: > {p/4 - 1:.2f}")
    print(f"Passes: {len(inversions) > p/4 - 1}")

    # Key question: Among elements k in A with I(k) also in A,
    # how many consecutive pairs (k, k+1) both have this property?

    AA_consecutive = []  # Both k and k+1 have I(k), I(k+1) in A
    for k in range(1, p - 1):
        if k in categories['k_in_A_Ik_in_A'] and (k+1) in categories['k_in_A_Ik_in_A']:
            AA_consecutive.append(k)

    BB_consecutive = []  # Both k and k+1 have I(k), I(k+1) in B
    for k in range(1, p - 1):
        if k in categories['k_in_B_Ik_in_B'] and (k+1) in categories['k_in_B_Ik_in_B']:
            BB_consecutive.append(k)

    print(f"\nConsecutive pairs with images both in A: {len(AA_consecutive)}")
    print(f"Consecutive pairs with images both in B: {len(BB_consecutive)}")

    # Among AA_consecutive, count inversions
    AA_inv = [k for k in AA_consecutive if I[k+1] < I[k]]
    BB_inv = [k for k in BB_consecutive if I[k+1] < I[k]]

    print(f"  Inversions among AA: {len(AA_inv)}")
    print(f"  Inversions among BB: {len(BB_inv)}")

    # KEY INSIGHT: If both I(k) and I(k+1) are in A (the lower half),
    # then since they're both less than p/2, the inversion I(k+1) < I(k)
    # is a "natural" inversion in the lower half.

    # Similarly for B (upper half).

    # The question is: can we lower-bound the number of such pairs?

    return {
        'p': p,
        'total_inv': len(inversions),
        'AA_inv': len(AA_inv),
        'BB_inv': len(BB_inv),
        'bound': p/4 - 1
    }

# Test
results = []
for p in [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53]:
    r = clean_analysis(p)
    results.append(r)

print("\n" + "="*70)
print("SUMMARY")
print("="*70)
print(f"{'p':<6} {'AA_inv':<8} {'BB_inv':<8} {'AA+BB':<8} {'total':<8} {'bound':<10} {'pass'}")
print("-" * 70)
for r in results:
    total_pair_inv = r['AA_inv'] + r['BB_inv']
    passes = "YES" if r['total_inv'] > r['bound'] else "NO"
    print(f"{r['p']:<6} {r['AA_inv']:<8} {r['BB_inv']:<8} {total_pair_inv:<8} {r['total_inv']:<8} {r['bound']:<10.2f} {passes}")

print("\n" + "="*70)
print("CONJECTURE")
print("="*70)
print("""
It seems that AA_inv + BB_inv is NOT the full count of inversions.
There must be inversions that occur when I(k) and I(k+1) are in DIFFERENT halves.

Let me reconsider the problem from scratch.
""")
