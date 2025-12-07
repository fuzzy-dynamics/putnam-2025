"""
Simple counting for Putnam 2025 B5 inversions.
"""

def mod_inverse(k, p):
    return pow(k, p - 2, p)

def count_inversions_by_half(p):
    """Count inversions, partitioning by halves."""
    # Compute all inverses
    inv_map = {k: mod_inverse(k, p) for k in range(1, p)}

    # Partition at p/2
    mid = p / 2
    A = set(k for k in range(1, p) if k < mid)
    B = set(k for k in range(1, p) if k > mid)

    # Count all inversions
    all_inversions = []
    for k in range(1, p - 1):
        if inv_map[k + 1] < inv_map[k]:
            all_inversions.append(k)

    # Categorize inversions
    inv_both_A = []  # k, k+1 both in A
    inv_both_B = []  # k, k+1 both in B
    inv_cross = []   # k in A, k+1 in B (or vice versa)

    for k in all_inversions:
        k_in_A = k in A
        k1_in_A = (k + 1) in A
        k_in_B = k in B
        k1_in_B = (k + 1) in B

        if k_in_A and k1_in_A:
            inv_both_A.append(k)
        elif k_in_B and k1_in_B:
            inv_both_B.append(k)
        else:
            inv_cross.append(k)

    print(f"p = {p}:")
    print(f"  Total inversions: {len(all_inversions)}")
    print(f"  Both in A: {len(inv_both_A)}")
    print(f"  Both in B: {len(inv_both_B)}")
    print(f"  Cross: {len(inv_cross)}")
    print(f"  Bound p/4 - 1 = {p/4 - 1:.2f}")
    print(f"  Passes: {len(all_inversions) > p/4 - 1}")
    print()

    return len(all_inversions), p/4 - 1

# Test for various primes
for p in [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]:
    count_inversions_by_half(p)
