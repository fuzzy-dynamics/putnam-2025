"""
Compute modular inverses and count inversions for small primes.
"""

def mod_inverse(k, p):
    """Compute modular inverse of k mod p using Fermat's Little Theorem."""
    return pow(k, p - 2, p)

def count_inversions(p):
    """Count how many k in {1, ..., p-2} have I(k+1) < I(k)."""
    # Compute all inverses
    I = {}
    for k in range(1, p):
        I[k] = mod_inverse(k, p)

    # Count inversions
    inversions = 0
    inversion_positions = []
    for k in range(1, p - 1):
        if I[k + 1] < I[k]:
            inversions += 1
            inversion_positions.append(k)

    return inversions, inversion_positions, I

# Test for small primes
primes = [5, 7, 11, 13, 17, 19, 23, 29, 31]

print("Testing small primes:\n")
for p in primes:
    inv_count, positions, I = count_inversions(p)
    bound = p / 4 - 1

    print(f"p = {p}:")
    print(f"  Inverse sequence: {[I[k] for k in range(1, p)]}")
    print(f"  Number of inversions: {inv_count}")
    print(f"  Required bound (p/4 - 1): {bound:.2f}")
    print(f"  Satisfies bound: {inv_count > bound}")
    print(f"  Inversion positions: {positions}")
    print()
