"""
Analyze the middle crossing pair more carefully.

The middle pair is k = (p-1)/2 and k+1 = (p+1)/2.

From the data, this pair ALWAYS seems to have an inversion!
"""

def mod_inverse(k, p):
    return pow(k, p - 2, p)

def check_middle_pair(p):
    """Check if the middle pair has an inversion."""
    inv_map = {k: mod_inverse(k, p) for k in range(1, p)}

    mid_k = (p - 1) // 2
    mid_k_plus_1 = mid_k + 1

    I_mid = inv_map[mid_k]
    I_mid_plus_1 = inv_map[mid_k_plus_1]

    has_inversion = I_mid_plus_1 < I_mid

    print(f"p = {p}:")
    print(f"  Middle pair: k = {mid_k}, k+1 = {mid_k_plus_1}")
    print(f"  I({mid_k}) = {I_mid}, I({mid_k_plus_1}) = {I_mid_plus_1}")
    print(f"  Has inversion: {has_inversion}")
    print()

    return has_inversion

# Test for many primes
primes = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73]

always_true = True
for p in primes:
    if not check_middle_pair(p):
        always_true = False
        print(f"COUNTEREXAMPLE FOUND at p = {p}!")

if always_true:
    print("="*70)
    print("OBSERVATION: The middle pair ALWAYS has an inversion!")
    print("="*70)
    print()
    print("This is a key fact that can likely be proven using the symmetry I(p-k) = p - I(k).")
    print()
    print("If we can prove this, plus show that among the remaining pairs,")
    print("at least some fraction have inversions, we'd be done!")
