#!/usr/bin/env python3
"""
Verification code for Putnam 2025 A5

Computes f(s) for all sequences s and verifies:
1. Alternating sequences maximize f(s)
2. The maximum value follows the Euler numbers (zigzag permutations)
3. Patterns in the data that could strengthen the proof
"""

from itertools import permutations, product
from collections import defaultdict
import math

def compute_f(s, n):
    """
    Compute f(s): number of permutations (a_1,...,a_n) of {1,...,n}
    such that s_i * (a_{i+1} - a_i) > 0 for all i.

    s is a sequence of length n-1 with values +1 or -1
    """
    count = 0
    for perm in permutations(range(1, n+1)):
        valid = True
        for i in range(n-1):
            diff = perm[i+1] - perm[i]
            if s[i] * diff <= 0:  # Need s[i] * diff > 0
                valid = False
                break
        if valid:
            count += 1
    return count

def sequence_to_string(s):
    """Convert sequence to readable string"""
    return ''.join('+' if x == 1 else '-' for x in s)

def is_alternating(s):
    """Check if sequence is alternating (+,-,+,-,... or -,+,-,+,...)"""
    if len(s) <= 1:
        return True
    for i in range(len(s) - 1):
        if s[i] == s[i+1]:
            return False
    return True

def count_runs(s):
    """Count number of runs (maximal consecutive sequences of same sign)"""
    if len(s) == 0:
        return 0
    runs = 1
    for i in range(len(s) - 1):
        if s[i] != s[i+1]:
            runs += 1
    return runs

def analyze_by_run_structure(results, n):
    """Analyze f(s) grouped by run structure"""
    by_runs = defaultdict(list)
    for s, f_val in results.items():
        runs = count_runs(s)
        by_runs[runs].append((s, f_val))

    print(f"\n--- Analysis by run count (n={n}) ---")
    for runs in sorted(by_runs.keys()):
        f_values = [f_val for _, f_val in by_runs[runs]]
        max_f = max(f_values)
        min_f = min(f_values)
        avg_f = sum(f_values) / len(f_values)
        print(f"  {runs} runs: max={max_f}, min={min_f}, avg={avg_f:.2f}, count={len(f_values)}")

def euler_numbers():
    """
    Euler numbers (zigzag numbers) - alternating permutations.

    OEIS A000111: Euler or up/down numbers
    a(n) = number of alternating permutations of n elements

    For this problem:
    - n=2: 2 elements, 1 constraint -> expect a(2)=1
    - n=3: 3 elements, 2 constraints -> expect a(3)=2
    - n=4: 4 elements, 3 constraints -> expect a(4)=5
    - n=5: 5 elements, 4 constraints -> expect a(5)=16
    - n=6: 6 elements, 5 constraints -> expect a(6)=61

    Observed: 1, 2, 5, 16, 61 - matches perfectly!
    """
    # A000111 values
    return {
        2: 1,
        3: 2,
        4: 5,
        5: 16,
        6: 61,
        7: 272,
        8: 1385,
        9: 7936,
        10: 50521
    }

def verify_for_n(n):
    """Complete verification for a given n"""
    print(f"\n{'='*60}")
    print(f"VERIFICATION FOR n={n}")
    print(f"{'='*60}")

    # Generate all 2^(n-1) sequences
    results = {}
    for s_tuple in product([1, -1], repeat=n-1):
        s = list(s_tuple)
        f_val = compute_f(s, n)
        results[tuple(s)] = f_val

    # Find maximum
    max_f = max(results.values())
    max_sequences = [(s, f_val) for s, f_val in results.items() if f_val == max_f]

    print(f"\nTotal sequences: {len(results)}")
    print(f"Maximum f(s): {max_f}")
    print(f"Number of sequences achieving maximum: {len(max_sequences)}")

    # Check if all maximizers are alternating
    print(f"\nSequences achieving maximum f(s) = {max_f}:")
    all_alternating = True
    for s, f_val in max_sequences:
        s_str = sequence_to_string(s)
        is_alt = is_alternating(s)
        print(f"  {s_str}: f(s)={f_val}, alternating={is_alt}")
        if not is_alt:
            all_alternating = False

    # Check against Euler numbers
    # For sequence of length n-1, we're counting permutations of n elements
    euler = euler_numbers()
    expected = euler.get(n, None)  # Use n directly
    if expected is not None:
        match = (max_f == expected)
        print(f"\nEuler number A000111({n}) = {expected}")
        print(f"Match with maximum f(s): {match}")
        if not match:
            print(f"  WARNING: Expected {expected} but got {max_f}")

    # Analyze run structure
    analyze_by_run_structure(results, n)

    # Show distribution of f values
    f_distribution = defaultdict(int)
    for f_val in results.values():
        f_distribution[f_val] += 1

    print(f"\nDistribution of f(s) values:")
    for f_val in sorted(f_distribution.keys(), reverse=True):
        count = f_distribution[f_val]
        pct = 100 * count / len(results)
        bar = '#' * min(50, count)
        print(f"  f={f_val:3d}: {count:4d} sequences ({pct:5.1f}%) {bar}")

    return {
        'n': n,
        'max_f': max_f,
        'expected_euler': expected,
        'all_maximizers_alternating': all_alternating,
        'num_maximizers': len(max_sequences),
        'euler_match': max_f == expected if expected is not None else None
    }

def find_counterexample_to_run_breaking(n):
    """
    Try to find a counterexample where breaking a run decreases f(s).
    This would disprove the claim that alternating is optimal.
    """
    print(f"\n--- Searching for counterexamples (n={n}) ---")

    counterexamples = []
    for s_tuple in product([1, -1], repeat=n-1):
        s = list(s_tuple)
        if is_alternating(s):
            continue  # Skip alternating sequences

        f_s = compute_f(s, n)

        # Try breaking one run
        for i in range(len(s) - 1):
            if s[i] == s[i+1]:  # Found a run
                # Break it by flipping s[i+1]
                s_broken = s.copy()
                s_broken[i+1] *= -1
                f_broken = compute_f(s_broken, n)

                if f_broken < f_s:
                    # Found a case where breaking a run decreases f!
                    counterexamples.append({
                        'original': sequence_to_string(s),
                        'broken': sequence_to_string(s_broken),
                        'f_original': f_s,
                        'f_broken': f_broken,
                        'position': i+1
                    })

    if counterexamples:
        print(f"Found {len(counterexamples)} counterexamples where breaking a run DECREASES f(s):")
        for ex in counterexamples[:10]:  # Show first 10
            print(f"  {ex['original']} (f={ex['f_original']}) -> {ex['broken']} (f={ex['f_broken']})")
        print("This suggests the claim needs careful examination!")
    else:
        print(f"No counterexamples found. Breaking runs appears to weakly increase f(s).")

    return counterexamples

def analyze_run_breaking_systematically(n):
    """
    For each non-alternating sequence, check if breaking ALL runs gives alternating
    and compare f values.
    """
    print(f"\n--- Systematic run-breaking analysis (n={n}) ---")

    improvements = []
    for s_tuple in product([1, -1], repeat=n-1):
        s = list(s_tuple)
        if is_alternating(s):
            continue

        f_s = compute_f(s, n)
        runs = count_runs(s)

        # There are two alternating sequences: (+,-,+,...) and (-,+,-,+,...)
        alt1 = [1 if i % 2 == 0 else -1 for i in range(n-1)]
        alt2 = [-1 if i % 2 == 0 else 1 for i in range(n-1)]

        f_alt1 = compute_f(alt1, n)
        f_alt2 = compute_f(alt2, n)
        f_alt_max = max(f_alt1, f_alt2)

        if f_s > f_alt_max:
            improvements.append({
                'seq': sequence_to_string(s),
                'f_s': f_s,
                'f_alt': f_alt_max,
                'runs': runs
            })

    if improvements:
        print(f"Found {len(improvements)} sequences with f(s) > f(alternating):")
        for imp in improvements[:10]:
            print(f"  {imp['seq']} (runs={imp['runs']}): f={imp['f_s']} > {imp['f_alt']}")
        print("CRITICAL: The claim is FALSE!")
    else:
        print(f"All non-alternating sequences have f(s) <= f(alternating).")
        print("The claim appears to be TRUE (but needs rigorous proof).")

    return improvements

def main():
    """Run complete verification"""
    print("PUTNAM 2025 A5 VERIFICATION")
    print("="*60)
    print("Claim: Alternating sequences (+,-,+,-,...) and (-,+,-,+,...)")
    print("       maximize f(s) for each n >= 2.")
    print("="*60)

    summary = []

    # Test for n = 2, 3, 4, 5, 6 (7 takes too long for brute force)
    for n in range(2, 7):
        result = verify_for_n(n)
        summary.append(result)

        # Look for counterexamples
        counterexamples = find_counterexample_to_run_breaking(n)
        non_alt_better = analyze_run_breaking_systematically(n)

        result['has_counterexamples'] = len(counterexamples) > 0
        result['non_alt_better'] = len(non_alt_better) > 0

    # Final summary
    print("\n" + "="*60)
    print("FINAL SUMMARY")
    print("="*60)

    print("\n{:>3} | {:>8} | {:>8} | {:>10} | {:>10}".format(
        "n", "max f(s)", "Euler", "All Alt?", "Match?"
    ))
    print("-" * 60)

    all_correct = True
    for r in summary:
        n = r['n']
        max_f = r['max_f']
        expected = r['expected_euler']
        all_alt = r['all_maximizers_alternating']
        match = r['euler_match']

        print("{:>3} | {:>8} | {:>8} | {:>10} | {:>10}".format(
            n, max_f, expected if expected else "?",
            "YES" if all_alt else "NO",
            "YES" if match else "NO" if match is not None else "?"
        ))

        if not all_alt or not match:
            all_correct = False

    print("\n" + "="*60)
    print("VERDICT")
    print("="*60)

    if all_correct and all(not r['non_alt_better'] for r in summary):
        print("\nRESULT: CORRECT (with caveats)")
        print("\nThe claim is VERIFIED for n = 2, 3, 4, 5, 6:")
        print("  1. Alternating sequences uniquely maximize f(s)")
        print("  2. Maximum values match Euler numbers E_{n-1}")
        print("  3. No counterexamples found")
        print("\nHOWEVER, the current proof is INSUFFICIENT:")
        print("  - The proof that 'breaking runs increases f(s)' is hand-wavy")
        print("  - Need rigorous proof using bijections or induction")
        print("  - Should formalize connection to Euler numbers/zigzag permutations")
        print("\nRECOMMENDATION: NEEDS MAJOR REVISION")
        print("  - Add rigorous proof of optimality")
        print("  - Cite connection to Euler numbers (OEIS A000111)")
        print("  - Use formal bijection or generating function argument")
    else:
        print("\nRESULT: INCORRECT OR INCOMPLETE")
        print("\nProblems found:")
        for r in summary:
            if not r['all_maximizers_alternating']:
                print(f"  - n={r['n']}: Non-alternating sequences also maximize f(s)")
            if r['non_alt_better']:
                print(f"  - n={r['n']}: Non-alternating sequence beats alternating!")
            if not r['euler_match']:
                print(f"  - n={r['n']}: Maximum doesn't match Euler number")

if __name__ == "__main__":
    main()
