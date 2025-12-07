"""
KEY INSIGHT for Putnam 2025 B5

After computational exploration, I notice:
1. When we split at m = (p-1)/2, we get roughly equal inversions in S and L
2. The CROSSING pair (m, m+1) often has I(m+1) < I(m) (an inversion!)

Let me try a different partition: split at (p+1)/2 instead.

Actually, the key insight should be about COUNTING inversions using
properties of the inverse permutation.

Let me think about this more carefully:
- We have p-2 consecutive pairs: (1,2), (2,3), ..., (p-2, p-1)
- We want to show that at least p/4 - 1 of them have I(k+1) < I(k)

Strategy: Use a symmetry/pairing argument.

For each k in {1, ..., p-1}, consider:
- Its "partner" p - k (also in {1, ..., p-1} if k != 0)
- We have I(p-k) ≡ (p-k)^{-1} ≡ -k^{-1} ≡ p - k^{-1} ≡ p - I(k) (mod p)

So I(p-k) = p - I(k) when we take representatives in {1, ..., p-1}.

This is a KEY symmetry!
"""

def mod_inverse(k, p):
    return pow(k, p - 2, p)

def verify_symmetry(p):
    """Verify the symmetry I(p-k) = p - I(k)."""
    I = {k: mod_inverse(k, p) for k in range(1, p)}

    print(f"\n{'='*70}")
    print(f"Symmetry verification for p = {p}")
    print(f"{'='*70}")

    symmetric = True
    for k in range(1, p):
        expected = (p - I[k]) % p
        if expected == 0:
            expected = p
        actual = I[(p - k) % p] if (p - k) % p != 0 else I[p - k]

        # Handle the case where p - k might be 0 or p
        pk = p - k
        if pk <= 0:
            pk += p
        if pk >= p:
            pk -= p

        if pk in I:
            actual = I[pk]
            matches = (actual == expected)
            if k <= 10:  # Print first few
                print(f"  k={k:2d}: I(k)={I[k]:2d}, p-k={pk:2d}, I(p-k)={actual:2d}, p-I(k)={expected:2d}, match={matches}")
            if not matches:
                symmetric = False

    print(f"\nSymmetry I(p-k) = p - I(k) holds: {symmetric}")
    return symmetric

def analyze_using_symmetry(p):
    """Analyze inversions using the symmetry."""
    I = {k: mod_inverse(k, p) for k in range(1, p)}

    print(f"\n{'='*70}")
    print(f"Inversion analysis using symmetry for p = {p}")
    print(f"{'='*70}")

    # Count inversions
    inversions = []
    for k in range(1, p - 1):
        if I[k+1] < I[k]:
            inversions.append(k)

    # Use symmetry: if k has an inversion, what about p-1-k?
    # Actually, let's think about pairs (k, p-1-k)

    # For p = 11: pairs are (1,9), (2,8), (3,7), (4,6), (5,5)
    # For p = 13: pairs are (1,11), (2,10), (3,9), (4,8), (5,7), (6,6)

    print(f"\nTotal inversions: {len(inversions)}")
    print(f"Required: > {p/4 - 1:.2f}")

    # Let's try a DIFFERENT approach:
    # Count how many k in {1, ..., (p-1)/2} have I(k+1) < I(k)
    # and how many k in {(p+1)/2, ..., p-2} have I(k+1) < I(k)

    mid = (p - 1) // 2
    inv_lower = [k for k in inversions if k <= mid]
    inv_upper = [k for k in inversions if k > mid]

    print(f"\nInversions in lower half k <= {mid}: {len(inv_lower)}")
    print(f"Inversions in upper half k > {mid}: {len(inv_upper)}")

    return inversions

# Test symmetry
for p in [7, 11, 13, 17]:
    verify_symmetry(p)

# Analyze using symmetry
for p in [7, 11, 13, 17, 19, 23]:
    analyze_using_symmetry(p)


print("\n" + "="*70)
print("ALTERNATIVE APPROACH: Direct counting")
print("="*70)
print("""
Let's try a more direct approach.

Define S = {1, ..., (p-1)/2} and L = {(p+1)/2, ..., p-1}.
Since I is a bijection, exactly (p-1)/2 elements of S map to S,
and exactly (p-1)/2 elements of S map to L.

Similarly for L.

For consecutive pairs (k, k+1) both in S:
- If both I(k), I(k+1) are in L, then...
- If both I(k), I(k+1) are in S, then...
- If they're split, then...

Actually, this is getting complicated. Let me try a probabilistic argument.
""")
