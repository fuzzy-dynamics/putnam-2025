#!/usr/bin/env python3
"""
Find a rigorous argument that doesn't rely on computation.

Key insight: Use properties of the permutation I itself.
"""

def modinv(k, p):
    return pow(k, -1, p)

def analyze_permutation_structure(p):
    """Analyze the structure of the modular inverse permutation"""
    I = [0] + [modinv(k, p) for k in range(1, p)]

    print(f"\n{'='*60}")
    print(f"p = {p}")
    print(f"{'='*60}")

    # Fixed points: I(k) = k means k^2 = 1 (mod p)
    # So k = 1 or k = p-1
    fixed_points = [k for k in range(1, p) if I[k] == k]
    print(f"Fixed points: {fixed_points}")  # Should be [1, p-1]

    # 2-cycles: I(I(k)) = k but I(k) != k
    two_cycles = []
    for k in range(1, p):
        if I[k] != k and I[I[k]] == k:
            pair = tuple(sorted([k, I[k]]))
            if pair not in two_cycles:
                two_cycles.append(pair)

    print(f"2-cycles: {two_cycles}")

    # Note: I is an involution! I(I(k)) = k for all k
    # Proof: k * I(k) = 1, so I(k) * I(I(k)) = 1, so I(I(k)) = I(k)^{-1} = k

    # Key observation: positions near boundaries
    print(f"\nBoundary analysis:")
    print(f"I(1) = {I[1]}, I(2) = {I[2]}")
    print(f"I(p-2) = {I[p-2]}, I(p-1) = {I[p-1]}")

    # Middle position
    mid = (p-1)//2
    print(f"\nMiddle: I({mid}) = {I[mid]}, I({mid+1}) = {I[mid+1]}")

    # Count inversions
    inversions = sum(1 for k in range(1, p-1) if I[k+1] < I[k])
    print(f"\nTotal inversions: {inversions}")
    print(f"Bound p/4-1 = {p/4-1}")

    # Key question: how many k have I(k) > (p-1)/2?
    upper_half = sum(1 for k in range(1, p) if I[k] > (p-1)/2)
    lower_half = sum(1 for k in range(1, p) if I[k] <= (p-1)/2)
    print(f"\nValues in upper half: {upper_half}, lower half: {lower_half}")

    # Analyze positions 1 to (p-3)/2
    first_quarter = (p-3)//4 + 1
    large_in_first_quarter = sum(1 for k in range(1, first_quarter+1) if I[k] > (p-1)/2)
    print(f"In positions 1..{first_quarter}, how many I(k) > {(p-1)/2}? {large_in_first_quarter}")

    return inversions

# Test on several primes
for p in [5, 7, 11, 13, 17, 19, 23, 29, 31]:
    analyze_permutation_structure(p)

print("\n" + "="*60)
print("INSIGHT SEARCH")
print("="*60)

# Let's look at a specific structural argument
def structural_argument(p):
    """
    Try to find a structural lower bound.

    Key fact: I is an involution with fixed points at 1 and p-1.
    The sequence I(1), I(2), ..., I(p-1) is a permutation of 1,...,p-1.

    We know:
    - I(1) = 1
    - I(p-1) = p-1
    - I((p+1)/2) = 2
    - I((p-1)/2) = p-2

    Consider the first (p-1)/2 positions: {1, 2, ..., (p-1)/2}
    Their images must cover all of {1, ..., p-1}
    """
    I = [0] + [modinv(k, p) for k in range(1, p)]

    mid = (p-1)//2

    # In the first half {1, ..., mid}, how many have I(k) in the second half?
    first_half_to_second = sum(1 for k in range(1, mid+1) if I[k] > mid)

    # By involution property, same number in second half map to first
    second_half_to_first = sum(1 for k in range(mid+1, p) if I[k] <= mid)

    print(f"\np = {p}")
    print(f"First half -> Second half: {first_half_to_second}")
    print(f"Second half -> First half: {second_half_to_first}")
    print(f"These must be equal: {first_half_to_second == second_half_to_first}")

    # Now, among positions 1 to p-2, consider transitions
    # A transition from first half to second half OR vice versa might cause inversions

    # Actually, let's count more carefully
    # An inversion at k means I(k+1) < I(k)
    # This is a "descent" in the permutation

    descents = sum(1 for k in range(1, p-1) if I[k+1] < I[k])
    ascents = sum(1 for k in range(1, p-1) if I[k+1] > I[k])

    print(f"Descents (inversions): {descents}")
    print(f"Ascents: {ascents}")
    print(f"Total: {descents + ascents} (should be {p-2})")

for p in [5, 7, 11, 13, 17, 19, 23]:
    structural_argument(p)
