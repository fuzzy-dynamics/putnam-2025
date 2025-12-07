"""
Final proof approach for Putnam 2025 B5.

KEY OBSERVATION from computational exploration:
All inversions occur when k and k+1 are BOTH in the same half!

This suggests a proof strategy based on partitioning.

Proof outline:
1. Partition {1, ..., p-1} into S = {1, ..., m} and L = {m+1, ..., p-1}
   where m = floor((p-1)/2)
2. Consider consecutive pairs (k, k+1) that are both in S or both in L
3. For each such pair, analyze when I(k+1) < I(k)

Let's verify this observation more carefully and develop the proof.
"""

def mod_inverse(k, p):
    return pow(k, p - 2, p)

def detailed_analysis(p):
    """Detailed analysis to understand the structure."""
    I = {k: mod_inverse(k, p) for k in range(1, p)}

    # Use m = floor((p-1)/2) as the split point
    m = (p - 1) // 2

    S = set(range(1, m + 1))
    L = set(range(m + 1, p))

    print(f"\n{'='*70}")
    print(f"p = {p}, m = {m}")
    print(f"S = {{1, ..., {m}}}, |S| = {len(S)}")
    print(f"L = {{{m+1}, ..., {p-1}}}, |L| = {len(L)}")
    print(f"{'='*70}")

    # Count consecutive pairs in each category
    pairs_in_S = [k for k in range(1, p-1) if k in S and k+1 in S]
    pairs_cross = [k for k in range(1, p-1) if k in S and k+1 in L]
    pairs_in_L = [k for k in range(1, p-1) if k in L and k+1 in L]

    print(f"\nConsecutive pairs (k, k+1):")
    print(f"  Both in S: {len(pairs_in_S)} pairs")
    print(f"  Cross S→L: {len(pairs_cross)} pairs (should be 1)")
    print(f"  Both in L: {len(pairs_in_L)} pairs")

    # Count inversions in each category
    inv_in_S = [k for k in pairs_in_S if I[k+1] < I[k]]
    inv_cross = [k for k in pairs_cross if I[k+1] < I[k]]
    inv_in_L = [k for k in pairs_in_L if I[k+1] < I[k]]

    print(f"\nInversions (I(k+1) < I(k)):")
    print(f"  In S: {len(inv_in_S)} out of {len(pairs_in_S)}")
    print(f"  Cross: {len(inv_cross)} out of {len(pairs_cross)}")
    print(f"  In L: {len(inv_in_L)} out of {len(pairs_in_L)}")
    print(f"  Total: {len(inv_in_S) + len(inv_cross) + len(inv_in_L)}")

    # Key question: For pairs both in S, how many have BOTH images in S?
    # And how many have images in different halves?

    print(f"\nFor pairs in S (both k and k+1 in S):")
    for k in pairs_in_S[:10]:  # Show first 10
        i_k = I[k]
        i_k1 = I[k+1]
        in_S_k = "S" if i_k in S else "L"
        in_S_k1 = "S" if i_k1 in S else "L"
        is_inv = "INV" if i_k1 < i_k else "   "
        print(f"  k={k:2d}, k+1={k+1:2d} -> I(k)={i_k:2d} ({in_S_k}), I(k+1)={i_k1:2d} ({in_S_k1}) {is_inv}")

    # Count how many pairs (k, k+1) in S have I(k), I(k+1) in different halves
    pairs_S_images_split = 0
    pairs_S_images_both_S = 0
    pairs_S_images_both_L = 0

    for k in pairs_in_S:
        i_k_in_S = I[k] in S
        i_k1_in_S = I[k+1] in S
        if i_k_in_S and i_k1_in_S:
            pairs_S_images_both_S += 1
        elif not i_k_in_S and not i_k1_in_S:
            pairs_S_images_both_L += 1
        else:
            pairs_S_images_split += 1

    print(f"\n  Images both in S: {pairs_S_images_both_S}")
    print(f"  Images both in L: {pairs_S_images_both_L}")
    print(f"  Images split: {pairs_S_images_split}")

    return {
        'p': p,
        'm': m,
        'pairs_in_S': len(pairs_in_S),
        'pairs_in_L': len(pairs_in_L),
        'inv_in_S': len(inv_in_S),
        'inv_in_L': len(inv_in_L),
        'total_inv': len(inv_in_S) + len(inv_cross) + len(inv_in_L),
        'bound': p/4 - 1
    }

# Analyze and collect data
results = []
for p in [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]:
    result = detailed_analysis(p)
    results.append(result)

print("\n" + "="*70)
print("SUMMARY")
print("="*70)
print(f"{'p':<6} {'m':<6} {'|S|':<6} {'|L|':<6} {'inv_S':<8} {'inv_L':<8} {'total':<8} {'bound':<10} {'pass'}")
print("-" * 70)
for r in results:
    passes = "YES" if r['total_inv'] > r['bound'] else "NO"
    print(f"{r['p']:<6} {r['m']:<6} {r['pairs_in_S']:<6} {r['pairs_in_L']:<6} {r['inv_in_S']:<8} {r['inv_in_L']:<8} {r['total_inv']:<8} {r['bound']:<10.2f} {passes}")
