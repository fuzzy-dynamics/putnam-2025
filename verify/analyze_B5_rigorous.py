#!/usr/bin/env python3
"""
Rigorous analysis of Putnam 2025 B5 - finding the mathematical argument.

Key insight to explore:
- We have sum of I(k) = p(p-1)/2
- Inversions relate to how the permutation "jumps around"
- Need to analyze the structure more carefully
"""

def modinv(k, p):
    """Modular inverse of k mod p"""
    return pow(k, -1, p)

def count_inversions_detailed(p):
    """Count inversions with detailed analysis"""
    I = [0] + [modinv(k, p) for k in range(1, p)]  # I[k] for k=1,...,p-1

    inversions = []
    for k in range(1, p-1):  # k in {1, ..., p-2}
        if I[k+1] < I[k]:
            inversions.append(k)

    print(f"\n=== p = {p} ===")
    print(f"I values: {I[1:]}")
    print(f"Inversions at positions: {inversions}")
    print(f"Total inversions: {len(inversions)}")
    print(f"Bound p/4 - 1 = {p/4 - 1}")
    print(f"Margin: {len(inversions) - (p/4 - 1)}")

    # Analyze pairs
    mid = (p-1)//2
    pairs_analysis = []

    # Check middle position
    if mid in inversions:
        print(f"Middle position {mid} has inversion: I({mid+1})={I[mid+1]} < I({mid})={I[mid]}")

    # Check paired positions
    paired_inversions = 0
    for k in range(1, mid):
        k_prime = p - 1 - k
        k_inv = k in inversions
        kp_inv = k_prime in inversions
        if k_inv and kp_inv:
            paired_inversions += 1
            pairs_analysis.append((k, k_prime, 'both'))
        elif k_inv or kp_inv:
            pairs_analysis.append((k, k_prime, 'ERROR - should be symmetric!'))
        else:
            pairs_analysis.append((k, k_prime, 'neither'))

    print(f"\nPaired positions with inversions: {paired_inversions}")
    print(f"B = {paired_inversions}")
    print(f"Expected: 2B + 1 = {2*paired_inversions + 1}, Actual: {len(inversions)}")

    return len(inversions), paired_inversions

def analyze_sum_property(p):
    """Analyze using sum of I(k)"""
    I = [0] + [modinv(k, p) for k in range(1, p)]

    # Sum of all I(k) for k=1,...,p-1
    total_sum = sum(I[1:])
    expected_sum = p * (p-1) // 2

    print(f"\n=== Sum Analysis for p={p} ===")
    print(f"Sum of I(k): {total_sum}, Expected: {expected_sum}")
    print(f"Average I(k): {total_sum / (p-1)}")

    # Look at consecutive differences
    diffs = [I[k+1] - I[k] for k in range(1, p-1)]
    negative_diffs = sum(1 for d in diffs if d < 0)

    print(f"Negative differences (inversions): {negative_diffs}")
    print(f"Sum of differences: {sum(diffs)} = I({p-1}) - I(1) = {I[p-1]} - {I[1]}")

    # Key insight: sum of absolute jumps
    abs_sum = sum(abs(d) for d in diffs)
    print(f"Sum of absolute differences: {abs_sum}")

    return diffs

def explore_lower_bound_argument(p):
    """
    Try to find a rigorous lower bound argument.

    Key ideas to explore:
    1. The permutation must "cross" from low to high values
    2. Total variation is bounded
    3. Pigeonhole principle on ranges
    """
    I = [0] + [modinv(k, p) for k in range(1, p)]

    print(f"\n=== Lower Bound Exploration for p={p} ===")

    # Count how many times we cross the median
    median = (p+1) // 2
    crossings = 0
    for k in range(1, p-1):
        # Did we cross the median?
        if (I[k] < median and I[k+1] > median) or (I[k] > median and I[k+1] < median):
            crossings += 1

    print(f"Median crossings: {crossings}")

    # Analyze quadrants
    # Split {1,...,p-1} into lower half and upper half
    lower_half = set(range(1, median+1))
    upper_half = set(range(median+1, p))

    # Count transitions
    low_to_high = sum(1 for k in range(1, p-1) if I[k] in lower_half and I[k+1] in upper_half)
    high_to_low = sum(1 for k in range(1, p-1) if I[k] in upper_half and I[k+1] in lower_half)

    print(f"Low->High transitions: {low_to_high}")
    print(f"High->Low transitions: {high_to_low}")
    print(f"Net transitions: |{low_to_high} - {high_to_low}| = {abs(low_to_high - high_to_low)}")

    # These transitions must include inversions!
    inversions_count = sum(1 for k in range(1, p-1) if I[k+1] < I[k])
    print(f"Actual inversions: {inversions_count}")

# Run analysis
for p in [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]:
    count_inversions_detailed(p)
    analyze_sum_property(p)
    explore_lower_bound_argument(p)
    print("\n" + "="*60)
