"""
Testing the key lemma: if gcd(a, b) = 1 and both a, b are odd,
then gcd(2a+1, 2b+1) divides gcd(2m_k+1, 2n_k+1) for the parent iteration

Actually, let me think about this differently.

The key is to understand what happens to the GCD under the transformation.
"""

from math import gcd

def analyze_gcd_transformation():
    """
    Analyze what happens to gcd(2a+1, 2b+1) compared to d when:
    - d = gcd(2m+1, 2n+1) > 1
    - 2m+1 = da, 2n+1 = db with gcd(a,b) = 1
    """
    print("Analyzing GCD transformation:")
    print(f"{'m':<8} {'n':<8} {'d':<8} {'a':<8} {'b':<8} {'gcd(2a+1,2b+1)':<20} {'Ratio d/gcd(2a+1,2b+1)'}")
    print("-" * 90)

    for m in range(1, 50):
        for n in range(m+1, 50):
            d = gcd(2*m + 1, 2*n + 1)
            if d > 1:
                a = (2*m + 1) // d
                b = (2*n + 1) // d
                g_next = gcd(2*a + 1, 2*b + 1)

                if g_next > 1:
                    ratio = d // g_next if g_next > 0 else "undefined"
                    print(f"{m:<8} {n:<8} {d:<8} {a:<8} {b:<8} {g_next:<20} {ratio}")

analyze_gcd_transformation()

print("\n" + "=" * 90)
print("KEY OBSERVATION")
print("=" * 90)
print("\nFrom the output above, we should see that gcd(2a+1, 2b+1) = 1 in most cases.")
print("If there are any cases where gcd(2a+1, 2b+1) > 1, we should see a pattern.")
print("\nLet's also check: when does gcd(2a+1, 2b+1) > 1 for coprime odd a, b?")

def find_coprime_odd_with_large_gcd():
    """
    Find cases where gcd(a,b) = 1, both a,b odd, but gcd(2a+1, 2b+1) > 1
    """
    print("\n" + "=" * 90)
    print("Finding coprime odd pairs (a,b) where gcd(2a+1, 2b+1) > 1:")
    print("=" * 90)
    print(f"{'a':<8} {'b':<8} {'2a+1':<10} {'2b+1':<10} {'gcd(2a+1,2b+1)':<20}")
    print("-" * 60)

    found = []
    for a in range(1, 100, 2):  # odd numbers only
        for b in range(a+2, 100, 2):  # odd numbers only
            if gcd(a, b) == 1:
                g = gcd(2*a + 1, 2*b + 1)
                if g > 1:
                    found.append((a, b, g))
                    if len(found) <= 20:
                        print(f"{a:<8} {b:<8} {2*a+1:<10} {2*b+1:<10} {g:<20}")

    if not found:
        print("NO EXAMPLES FOUND!")
        print("\nThis means: if gcd(a,b) = 1 and both a, b are odd, then gcd(2a+1, 2b+1) = 1!")
    else:
        print(f"\nFound {len(found)} examples.")

find_coprime_odd_with_large_gcd()

print("\n" + "=" * 90)
print("VERIFYING THE CLAIM")
print("=" * 90)

# The claim: if a, b are odd and coprime, then 2a+1 and 2b+1 are coprime

def verify_claim(max_n=200):
    """
    Verify that gcd(a,b) = 1 with a,b odd implies gcd(2a+1, 2b+1) = 1
    """
    counterexamples = []
    count = 0

    for a in range(1, max_n, 2):
        for b in range(a+2, max_n, 2):
            if gcd(a, b) == 1:
                count += 1
                g = gcd(2*a + 1, 2*b + 1)
                if g > 1:
                    counterexamples.append((a, b, g))

    print(f"Tested {count} pairs of coprime odd numbers.")

    if counterexamples:
        print(f"Found {len(counterexamples)} counterexamples:")
        for a, b, g in counterexamples[:10]:
            print(f"  a={a}, b={b}: gcd({2*a+1}, {2*b+1}) = {g}")
        return False
    else:
        print("NO COUNTEREXAMPLES FOUND!")
        print("\nThis strongly suggests:")
        print("  If gcd(a,b) = 1 and both a, b are odd, then gcd(2a+1, 2b+1) = 1.")
        return True

claim_verified = verify_claim(300)

if claim_verified:
    print("\n" + "=" * 90)
    print("PROOF SKETCH (assuming the claim is true)")
    print("=" * 90)
    print("""
If the claim 'gcd(a,b) = 1 and a,b odd => gcd(2a+1, 2b+1) = 1' is true, then:

1. Start with m_0, n_0 with gcd(m_0, n_0) = 1
2. Let d_k = gcd(2m_k+1, 2n_k+1)
3. If d_k > 1, write 2m_k+1 = d_k * a, 2n_k+1 = d_k * b with gcd(a,b) = 1
4. Then m_{k+1} = a, n_{k+1} = b
5. Since 2m_k+1 and 2n_k+1 are odd and gcd(a,b) = 1, both a and b must be odd
6. By our claim, gcd(2a+1, 2b+1) = 1
7. Therefore d_{k+1} = gcd(2m_{k+1}+1, 2n_{k+1}+1) = 1

This proves: if d_k > 1, then d_{k+1} = 1.

Since the gcd sequence can only decrease (in the sense that once it hits 1, it stays at 1),
and it reaches 1 within at most one step after being > 1, we conclude:

    gcd(2m_k+1, 2n_k+1) = 1 for all but finitely many k.

QED (modulo proving the claim!)
""")
