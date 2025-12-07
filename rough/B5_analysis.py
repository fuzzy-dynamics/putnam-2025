"""
Deeper analysis of the inversion structure.
"""

def mod_inverse(k, p):
    """Compute modular inverse of k mod p."""
    return pow(k, p - 2, p)

def analyze_inversions(p):
    """Analyze the condition I(k+1) < I(k) more carefully."""
    I = {k: mod_inverse(k, p) for k in range(1, p)}

    print(f"\n{'='*60}")
    print(f"Analysis for p = {p}")
    print(f"{'='*60}\n")

    # Key insight: I(k+1) < I(k) iff (k+1)^{-1} < k^{-1}
    # This is equivalent to k < k+1 when we multiply by k(k+1)
    # But in modular arithmetic, we need to be more careful.

    # I(k+1) < I(k) means (k+1)^{-1} < k^{-1} (mod p)
    # Multiply both sides by k(k+1): k < k+1, which seems always true!
    # But we're in mod p arithmetic, so this needs more thought.

    # Let's check: I(k+1) < I(k) iff what?
    # (k+1)^{-1} < k^{-1} as integers in {1, ..., p-1}

    inversions = []
    non_inversions = []

    for k in range(1, p - 1):
        if I[k + 1] < I[k]:
            inversions.append(k)
        else:
            non_inversions.append(k)

    print(f"Total inversions: {len(inversions)} out of {p-2}")
    print(f"Bound p/4 - 1 = {p/4 - 1:.2f}")
    print(f"Satisfies bound: {len(inversions) > p/4 - 1}\n")

    # Let's look at the relationship between k and I(k)
    print("Relationship analysis:")
    print(f"{'k':<6} {'I(k)':<6} {'k*I(k) mod p':<12} {'I(k+1)':<8} {'I(k+1)<I(k)'}")
    print("-" * 50)
    for k in range(1, min(p, 15)):
        if k < p:
            inv_k = I[k]
            product = (k * inv_k) % p
            if k < p - 1:
                inv_k1 = I[k + 1]
                is_inversion = "YES" if inv_k1 < inv_k else "NO"
                print(f"{k:<6} {inv_k:<6} {product:<12} {inv_k1:<8} {is_inversion}")
            else:
                print(f"{k:<6} {inv_k:<6} {product:<12} {'-':<8} {'-'}")

    # Key observation: Let's partition based on whether k < p/2 or k > p/2
    inv_small = [k for k in inversions if k < p/2]
    inv_large = [k for k in inversions if k >= p/2]

    print(f"\nInversions with k < p/2: {len(inv_small)}")
    print(f"Inversions with k >= p/2: {len(inv_large)}")

    # Another angle: look at I(k) values
    inv_I_small = [k for k in inversions if I[k] < p/2]
    inv_I_large = [k for k in inversions if I[k] >= p/2]

    print(f"\nInversions with I(k) < p/2: {len(inv_I_small)}")
    print(f"Inversions with I(k) >= p/2: {len(inv_I_large)}")

    return inversions, I

# Test for a few primes
for p in [7, 11, 13, 17, 23]:
    analyze_inversions(p)
