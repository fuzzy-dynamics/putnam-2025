"""
Proof strategy for Putnam 2025 B5.

Key Insight:
We want to count k in {1, ..., p-2} such that I(k+1) < I(k),
where I(k) is the modular inverse of k mod p.

Strategy 1: Partition argument
- Partition {1, ..., p-1} into "small" S = {1, ..., (p-1)/2} and "large" L = {(p+1)/2, ..., p-1}
- Since I is a permutation, |I(S)| = |S| = (p-1)/2

Strategy 2: Consecutive pairs analysis
- For k, k+1 consecutive, when is I(k+1) < I(k)?
- This is related to whether the inverse map "inverts" the consecutive pair

Strategy 3: Count using quadratic residues
- Note that I(k) ≡ k^{p-2} ≡ k^{-1} (mod p)
- For I(k+1) < I(k), we need (k+1)^{-1} < k^{-1} as integers in [1, p-1]

Let me try a different approach based on what I observed:
The key is to look at pairs (k, k+1) and see how many have I(k) > I(k+1).

Observation from data:
- The number of inversions seems to be roughly (p-2)/2 ± O(sqrt(p))
- This is MUCH larger than p/4 - 1, so there's room to prove a tighter bound

Let's try a partition-based counting argument.
"""

def mod_inverse(k, p):
    return pow(k, p - 2, p)

def partition_analysis(p):
    """
    Partition-based counting argument.

    Idea: Split {1, ..., p-1} into two halves.
    For pairs (k, k+1) that cross the boundary or stay within,
    analyze when we get inversions.
    """
    I = {k: mod_inverse(k, p) for k in range(1, p)}

    # Define the two halves
    half = (p - 1) // 2
    S = set(range(1, half + 2))  # Small half: {1, ..., ceil((p-1)/2)}
    L = set(range(half + 2, p))   # Large half: {ceil((p-1)/2)+1, ..., p-1}

    print(f"\n{'='*70}")
    print(f"p = {p}, half = {half}")
    print(f"S = {{1, ..., {half+1}}}, |S| = {len(S)}")
    print(f"L = {{{half+2}, ..., {p-1}}}, |L| = {len(L)}")
    print(f"{'='*70}")

    # Count inversions by category
    inversions = {
        'both_in_S': [],       # k, k+1 both in S
        'cross_SL': [],        # k in S, k+1 in L
        'both_in_L': [],       # k, k+1 both in L
    }

    for k in range(1, p - 1):
        if I[k+1] < I[k]:  # Inversion at k
            if k in S and k+1 in S:
                inversions['both_in_S'].append(k)
            elif k in S and k+1 in L:
                inversions['cross_SL'].append(k)
            elif k in L and k+1 in L:
                inversions['both_in_L'].append(k)

    total_inv = sum(len(v) for v in inversions.values())

    print(f"\nInversions breakdown:")
    print(f"  Both in S: {len(inversions['both_in_S'])}")
    print(f"  Cross S/L: {len(inversions['cross_SL'])}")
    print(f"  Both in L: {len(inversions['both_in_L'])}")
    print(f"  Total: {total_inv}")
    print(f"  Required: > {p/4 - 1:.2f}")
    print(f"  Passes: {total_inv > p/4 - 1}")

    # Now let's look at the IMAGE side
    # How many elements of I(S) are in S vs L?
    I_S_in_S = sum(1 for k in S if I[k] in S)
    I_S_in_L = sum(1 for k in S if I[k] in L)
    I_L_in_S = sum(1 for k in L if I[k] in S)
    I_L_in_L = sum(1 for k in L if I[k] in L)

    print(f"\nImage analysis:")
    print(f"  I(S) ∩ S: {I_S_in_S}")
    print(f"  I(S) ∩ L: {I_S_in_L}")
    print(f"  I(L) ∩ S: {I_L_in_S}")
    print(f"  I(L) ∩ L: {I_L_in_L}")

    return inversions

# Test the partition analysis
for p in [7, 11, 13, 17, 19, 23, 29, 31, 37, 41]:
    partition_analysis(p)


print("\n" + "="*70)
print("KEY OBSERVATION FOR PROOF")
print("="*70)
print("""
From the data, we see that the number of inversions is typically
around (p-2)/2, which is much larger than p/4 - 1.

The proof strategy should exploit:
1. I is a permutation of {1, ..., p-1}
2. For consecutive pairs (k, k+1), their inverses (I(k), I(k+1)) form a
   permutation of pairs
3. We need to show at least p/4 - 1 of these pairs have I(k+1) < I(k)

A key insight: If we partition {1, ..., p-1} into two halves S and L,
then exactly half of the elements map to S and half to L under I.

For pairs (k, k+1) where both are in one half, we can count inversions.
""")
