"""
Analyze the inversion sequence using runs (ascending/descending sequences).

A "run" is a maximal sequence where I(k) < I(k+1) < ... (ascending)
or I(k) > I(k+1) > ... (descending).

The number of inversions is related to the number of descending steps.
"""

def mod_inverse(k, p):
    return pow(k, p - 2, p)

def analyze_runs(p):
    """Analyze ascending and descending runs."""
    inv_map = {k: mod_inverse(k, p) for k in range(1, p)}

    print(f"\n{'='*70}")
    print(f"p = {p}")
    print(f"Sequence: {[inv_map[k] for k in range(1, p)]}")
    print(f"{'='*70}")

    # Count ups and downs
    ups = 0
    downs = 0

    for k in range(1, p-1):
        if inv_map[k+1] > inv_map[k]:
            ups += 1
        else:
            downs += 1

    print(f"\nTransitions:")
    print(f"  Ups (I(k+1) > I(k)): {ups}")
    print(f"  Downs (I(k+1) < I(k)): {downs}")
    print(f"  Total: {ups + downs} (should be {p-2})")

    # Since we start at I(1) and end at I(p-1), and the sequence is a permutation,
    # we can think about the "vertical distance" traveled.

    # If we always went up, we'd go from I(1) to I(p-1).
    # Each "down" counteracts an "up".

    # Let's think about it differently: the sequence I(1), ..., I(p-1)
    # has some number of "peaks" and "valleys".

    # A peak at k means I(k-1) < I(k) > I(k+1)
    # A valley at k means I(k-1) > I(k) < I(k+1)

    peaks = []
    valleys = []

    for k in range(2, p-1):
        if inv_map[k-1] < inv_map[k] > inv_map[k+1]:
            peaks.append(k)
        elif inv_map[k-1] > inv_map[k] < inv_map[k+1]:
            valleys.append(k)

    print(f"\nPeaks and valleys:")
    print(f"  Peaks: {len(peaks)}")
    print(f"  Valleys: {len(valleys)}")

    # The number of runs can be computed from peaks and valleys
    # Number of runs = peaks + valleys + 1 (approximately)

    print(f"\nBound check:")
    print(f"  Downs (inversions): {downs}")
    print(f"  Required: > {p/4 - 1:.2f}")
    print(f"  Passes: {downs > p/4 - 1}")

    # Key observation: For a random permutation, ups ≈ downs ≈ (p-2)/2
    # We need to show downs > p/4 - 1, i.e., downs >= p/4
    # Since ups + downs = p - 2, if downs >= p/4, then ups <= 3p/4 - 2

    return ups, downs

# Test
results = []
for p in [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]:
    ups, downs = analyze_runs(p)
    results.append((p, ups, downs))

print("\n" + "="*70)
print("SUMMARY")
print("="*70)
print(f"{'p':<6} {'ups':<8} {'downs':<8} {'up-down':<10} {'bound':<10} {'pass'}")
print("-" * 70)
for p, ups, downs in results:
    diff = ups - downs
    bound = p/4 - 1
    passes = "YES" if downs > bound else "NO"
    print(f"{p:<6} {ups:<8} {downs:<8} {diff:<10} {bound:<10.2f} {passes}")

print("\n" + "="*70)
print("OBSERVATION")
print("="*70)
print("""
The difference (ups - downs) varies, but downs is always > p/4 - 1.

For p=7: ups=4, downs=1, difference=3
For p=11: ups=4, downs=5, difference=-1
For p=23: ups=10, downs=11, difference=-1

It seems that for larger p, downs ≈ (p-2)/2, which is much larger than p/4 - 1.

The challenge is to PROVE this rigorously without just relying on computation.
""")
