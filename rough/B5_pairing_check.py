"""
Check the pairing argument for inversions.

For k in {1, ..., p-2}, pair k with (p-1-k).

At k: check if I(k+1) < I(k)
At p-1-k: check if I(p-k) < I(p-1-k)

Using I(p-j) = p - I(j):
At p-1-k: check if (p - I(k)) < (p - I(k+1))
         which is equivalent to I(k) > I(k+1)

So if k has an inversion, then p-1-k has a non-inversion!
"""

def mod_inverse(k, p):
    return pow(k, p - 2, p)

def check_pairing(p):
    """Verify the pairing argument."""
    inv_map = {k: mod_inverse(k, p) for k in range(1, p)}

    print(f"\n{'='*70}")
    print(f"p = {p}")
    print(f"{'='*70}")

    # Verify symmetry
    print("\nVerifying symmetry I(p-k) = p - I(k):")
    symmetric = True
    for k in range(1, p):
        expected = (p - inv_map[k])
        if expected == 0:
            expected = p
        if expected >= p:
            expected -= p

        pk = (p - k)
        if pk == 0:
            pk = p
        if pk >= p:
            pk -= p

        actual = inv_map[pk] if pk in inv_map else None
        if actual != expected:
            symmetric = False
            if k <= 5:
                print(f"  k={k}: expected={expected}, actual={actual}, MISMATCH!")

    print(f"  Symmetry holds: {symmetric}")

    # Now check the pairing
    print(f"\nPairing analysis:")
    print(f"Total pairs to check: {p-2}")

    inversions = {}
    for k in range(1, p-1):
        inversions[k] = (inv_map[k+1] < inv_map[k])

    # Pair up
    paired = {}
    unpaired = []

    for k in range(1, p-1):
        partner = p - 1 - k
        if partner in range(1, p-1) and partner not in paired and k not in paired:
            paired[k] = partner
            paired[partner] = k

    # Find unpaired (should be at most 1 element)
    for k in range(1, p-1):
        if k not in paired:
            unpaired.append(k)

    print(f"  Paired: {len(paired)//2} pairs")
    print(f"  Unpaired: {unpaired}")

    # For each pair, check the inversion pattern
    inv_both = 0
    inv_neither = 0
    inv_exactly_one = 0

    checked_pairs = set()
    for k in range(1, p-1):
        if k in paired and (k, paired[k]) not in checked_pairs and (paired[k], k) not in checked_pairs:
            partner = paired[k]
            checked_pairs.add((k, partner))
            checked_pairs.add((partner, k))

            k_inv = inversions[k]
            p_inv = inversions[partner]

            if k_inv and p_inv:
                inv_both += 1
            elif not k_inv and not p_inv:
                inv_neither += 1
            else:
                inv_exactly_one += 1

            if k <= 5 or k >= p-6:  # Show first and last few
                print(f"    Pair ({k}, {partner}): k has inv={k_inv}, partner has inv={p_inv}")

    print(f"\n  Pairs where both have inversions: {inv_both}")
    print(f"  Pairs where neither has inversion: {inv_neither}")
    print(f"  Pairs where exactly one has inversion: {inv_exactly_one}")

    # Count total inversions
    total_inv = sum(1 for k in range(1, p-1) if inversions[k])
    total_non_inv = sum(1 for k in range(1, p-1) if not inversions[k])

    print(f"\n  Total inversions: {total_inv}")
    print(f"  Total non-inversions: {total_non_inv}")
    print(f"  Required bound: > {p/4 - 1:.2f}")
    print(f"  Passes: {total_inv > p/4 - 1}")

# Test
for p in [7, 11, 13, 17, 19, 23]:
    check_pairing(p)
