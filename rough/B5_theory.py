"""
Theoretical analysis of when I(k+1) < I(k).

Key insight: I(k+1) < I(k) as integers in {1, ..., p-1}
means (k+1)^{-1} < k^{-1} as integers.

Let's think about this differently. Define:
- S = {k : I(k+1) < I(k)} (the set of inversions)
- T = {k : I(k+1) > I(k)} (the non-inversions)

We want to show |S| > p/4 - 1.

Another approach: Look at pairs (k, k+1) and their inverses (I(k), I(k+1)).

Key observation: If we look at the map k -> I(k), we're looking at
the inverse permutation on {1, ..., p-1}.

Let's think about I(k) - I(k+1). When is this positive?
I(k) - I(k+1) = k^{-1} - (k+1)^{-1}
              = [k+1 - k] / [k(k+1)]  (in mod p arithmetic)
              = 1 / [k(k+1)]
              = [k(k+1)]^{-1}

So I(k) > I(k+1) iff k^{-1} > (k+1)^{-1} as integers in {1,...,p-1}.

Actually, let me think about this from a different angle.
Consider the set {1, 2, ..., p-1}. For each k, we have I(k) * k ≡ 1 (mod p).

The question is: when is I(k+1) < I(k)?
This happens iff (k+1)^{-1} < k^{-1} as representatives in {1, ..., p-1}.
"""

def mod_inverse(k, p):
    return pow(k, p - 2, p)

def analyze_key_insight(p):
    """
    Key insight: Let's count differently.

    For k in {1, ..., p-2}, we have an inversion at k iff I(k+1) < I(k).

    Equivalently: (k+1)^{-1} < k^{-1} as integers in [1, p-1].

    Let's think about which pairs (a, b) with b = a+1 have a^{-1} > b^{-1}.
    """
    I = {k: mod_inverse(k, p) for k in range(1, p)}

    print(f"\n{'='*70}")
    print(f"p = {p}")
    print(f"{'='*70}")

    # Count inversions by a different method
    # For each pair (k, k+1), check if their inverses are "inverted"

    inversions = []
    for k in range(1, p - 1):
        if I[k+1] < I[k]:
            inversions.append(k)

    print(f"Number of inversions: {len(inversions)}")
    print(f"Required bound: p/4 - 1 = {p/4 - 1:.2f}")
    print(f"Passes: {len(inversions) > p/4 - 1}")

    # Let's look at a complementary question:
    # Among all pairs (k, k+1), how are they distributed?

    # Partition {1, ..., p-1} into two sets:
    # A = {k : k < (p+1)/2}
    # B = {k : k > (p+1)/2}

    mid = (p + 1) / 2

    count_both_small = 0  # k < mid and I(k) < mid
    count_both_large = 0  # k >= mid and I(k) >= mid
    count_mixed = 0       # one small, one large

    for k in range(1, p):
        if (k < mid and I[k] < mid) or (k >= mid and I[k] >= mid):
            if k < mid and I[k] < mid:
                count_both_small += 1
            else:
                count_both_large += 1
        else:
            count_mixed += 1

    print(f"\nPartition analysis (mid = {mid:.1f}):")
    print(f"  Both small: {count_both_small}")
    print(f"  Both large: {count_both_large}")
    print(f"  Mixed: {count_mixed}")

    # Another idea: consecutive pairs in the inverse sequence
    # For each k, we go from I(k) to I(k+1)
    # This creates a "path" through {1, ..., p-1}

    # Count how many times we "go down" (I(k+1) < I(k))
    # vs "go up" (I(k+1) > I(k))

    ups = sum(1 for k in range(1, p-1) if I[k+1] > I[k])
    downs = len(inversions)

    print(f"\nPath analysis:")
    print(f"  Ups (I(k+1) > I(k)): {ups}")
    print(f"  Downs (I(k+1) < I(k)): {downs}")
    print(f"  Total transitions: {ups + downs}")

    return inversions, I

# Analyze several primes
for p in [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]:
    analyze_key_insight(p)
