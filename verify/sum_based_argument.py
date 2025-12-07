#!/usr/bin/env python3
"""
Sum-based argument for B5.

Key insight: Use the total variation of the permutation.

The sequence I(1), I(2), ..., I(p-1) is a permutation.
The sum of absolute differences |I(k+1) - I(k)| measures total variation.

For a permutation, there are constraints on this sum.
"""

def modinv(k, p):
    return pow(k, -1, p)

def analyze_total_variation(p):
    I = [0] + [modinv(k, p) for k in range(1, p)]

    # Total variation
    total_var = sum(abs(I[k+1] - I[k]) for k in range(1, p-1))

    # Split into up moves and down moves
    up_moves = sum(I[k+1] - I[k] for k in range(1, p-1) if I[k+1] > I[k])
    down_moves = sum(I[k] - I[k+1] for k in range(1, p-1) if I[k+1] < I[k])

    inversions = sum(1 for k in range(1, p-1) if I[k+1] < I[k])

    print(f"\np = {p}")
    print(f"Total variation: {total_var}")
    print(f"Up moves sum: {up_moves}")
    print(f"Down moves sum: {down_moves}")
    print(f"Net: up - down = {up_moves - down_moves} = I(p-1) - I(1) = {I[p-1] - I[1]}")
    print(f"Number of descents (inversions): {inversions}")
    print(f"Average descent size: {down_moves / inversions if inversions > 0 else 0:.2f}")

    # Key observation: if there are few inversions, they must be large
    # If inversions <= p/4 - 1, then we need large down moves

    bound = p/4 - 1
    if inversions <= bound:
        print(f"  ** HYPOTHETICALLY if inversions <= {bound:.2f}:")
        print(f"     Then down_moves must account for all decreases")
        print(f"     down_moves >= (something large)")
        print(f"     But up_moves - down_moves = {I[p-1] - I[1]} = {p-2}")
        print(f"     So up_moves = down_moves + {p-2}")

for p in [5, 7, 11, 13, 17, 19, 23, 29, 31, 37]:
    analyze_total_variation(p)

print("\n" + "="*60)
print("OBSERVATION:")
print("="*60)

# Key insight: Let's think about this differently
# Among positions 1 to p-2, how many transitions cross the median?

def crossing_argument(p):
    I = [0] + [modinv(k, p) for k in range(1, p)]

    median = (p-1) / 2

    # Count transitions from below median to above median
    below_to_above = sum(1 for k in range(1, p-1) if I[k] < median and I[k+1] > median)
    above_to_below = sum(1 for k in range(1, p-1) if I[k] > median and I[k+1] < median)

    inversions = sum(1 for k in range(1, p-1) if I[k+1] < I[k])

    print(f"\np = {p}")
    print(f"Transitions below->above: {below_to_above}")
    print(f"Transitions above->below: {above_to_below}")
    print(f"Total crossings: {below_to_above + above_to_below}")
    print(f"Inversions: {inversions}")

    # Observation: every below->above transition could potentially have an inversion
    # if the jump is from something in the lower half to something in the upper half

    # Actually, let's count more carefully
    # An inversion at position k means I(k+1) < I(k)
    # If I(k) is in upper half and I(k+1) is in lower half, that's definitely an inversion
    # But we could also have both in upper half or both in lower half

    upper_to_lower_inv = sum(1 for k in range(1, p-1)
                              if I[k] > median and I[k+1] < median)

    print(f"Inversions from upper to lower half: {upper_to_lower_inv}")
    print(f"This gives a lower bound: {upper_to_lower_inv} <= inversions")

    # But this isn't tight enough...

for p in [5, 7, 11, 13, 17, 19, 23]:
    crossing_argument(p)
