#!/usr/bin/env python3
"""
Deeper structural analysis of Putnam 2025 A5

Goal: Understand WHY alternating sequences maximize f(s)
by analyzing the combinatorial structure.
"""

from itertools import permutations, product
from collections import defaultdict

def compute_f(s, n):
    """Compute f(s) by brute force"""
    count = 0
    valid_perms = []
    for perm in permutations(range(1, n+1)):
        valid = True
        for i in range(n-1):
            diff = perm[i+1] - perm[i]
            if s[i] * diff <= 0:
                valid = False
                break
        if valid:
            count += 1
            valid_perms.append(perm)
    return count, valid_perms

def sequence_to_string(s):
    """Convert sequence to readable string"""
    return ''.join('+' if x == 1 else '-' for x in s)

def classify_permutation(perm):
    """
    Classify a permutation by its pattern of rises (+) and falls (-)
    Returns the signature sequence
    """
    sig = []
    for i in range(len(perm) - 1):
        if perm[i+1] > perm[i]:
            sig.append(1)
        else:
            sig.append(-1)
    return tuple(sig)

def analyze_permutation_sharing(n):
    """
    Analyze which permutations are counted by which sequences.
    Key insight: Each permutation contributes to exactly ONE sequence s.
    """
    print(f"\n{'='*60}")
    print(f"PERMUTATION SHARING ANALYSIS (n={n})")
    print(f"{'='*60}")

    # For each permutation, find which sequence(s) count it
    perm_to_sequences = defaultdict(list)

    for s_tuple in product([1, -1], repeat=n-1):
        s = list(s_tuple)
        _, valid_perms = compute_f(s, n)

        s_str = sequence_to_string(s)
        for perm in valid_perms:
            perm_to_sequences[perm].append(s_str)

    # Check if permutations are uniquely assigned
    unique_assignment = True
    for perm, seq_list in perm_to_sequences.items():
        if len(seq_list) != 1:
            print(f"Permutation {perm} counted by {len(seq_list)} sequences: {seq_list}")
            unique_assignment = False

    if unique_assignment:
        print("CRUCIAL INSIGHT: Each permutation is counted by exactly ONE sequence s!")
        print("This means the sequences partition the set of all n! permutations.")
        print(f"\nTotal permutations: {len(perm_to_sequences)} = {n}!")

        # Verify partition
        total_count = 0
        for s_tuple in product([1, -1], repeat=n-1):
            s = list(s_tuple)
            count, _ = compute_f(s, n)
            total_count += count

        print(f"Sum of all f(s): {total_count}")
        print(f"This should equal {n}! = {factorial(n)}")
        print(f"Match: {total_count == factorial(n)}")

def factorial(n):
    result = 1
    for i in range(1, n+1):
        result *= i
    return result

def analyze_bijection_structure(n):
    """
    Analyze the bijection between sequences s and permutations.
    For each permutation, s is determined by its signature (rise/fall pattern).
    """
    print(f"\n{'='*60}")
    print(f"BIJECTION STRUCTURE (n={n})")
    print(f"{'='*60}")

    sig_to_count = defaultdict(int)
    sig_to_perms = defaultdict(list)

    for perm in permutations(range(1, n+1)):
        sig = classify_permutation(perm)
        sig_to_count[sig] += 1
        sig_to_perms[sig].append(perm)

    print(f"\nNumber of distinct signatures: {len(sig_to_count)}")
    print(f"This should equal 2^{n-1} = {2**(n-1)}")

    # Show top signatures
    print(f"\nTop 10 signatures by count:")
    sorted_sigs = sorted(sig_to_count.items(), key=lambda x: x[1], reverse=True)
    for i, (sig, count) in enumerate(sorted_sigs[:10]):
        sig_str = sequence_to_string(sig)
        is_alt = all(sig[i] != sig[i+1] for i in range(len(sig)-1)) if len(sig) > 1 else True
        print(f"  {i+1}. {sig_str}: {count} permutations (alternating: {is_alt})")

    # Verify this matches our f(s) computation
    print(f"\nVerifying consistency:")
    for sig, count in sorted_sigs[:5]:
        s = list(sig)
        f_val, _ = compute_f(s, n)
        match = "✓" if count == f_val else "✗"
        print(f"  {sequence_to_string(sig)}: sig_count={count}, f(s)={f_val} {match}")

def analyze_run_effects(n):
    """
    Systematically analyze the effect of run structure on f(s).
    """
    print(f"\n{'='*60}")
    print(f"RUN STRUCTURE EFFECTS (n={n})")
    print(f"{'='*60}")

    # Group by number of runs
    by_runs = defaultdict(list)
    for s_tuple in product([1, -1], repeat=n-1):
        s = list(s_tuple)
        runs = count_runs(s)
        count, _ = compute_f(s, n)
        by_runs[runs].append((s, count))

    print(f"\nEffect of run count on f(s):")
    for runs in sorted(by_runs.keys()):
        f_values = [count for _, count in by_runs[runs]]
        max_f = max(f_values)
        min_f = min(f_values)
        avg_f = sum(f_values) / len(f_values)
        print(f"  {runs} runs: max={max_f}, min={min_f}, avg={avg_f:.2f}")

    # The key insight: more runs -> higher f(s)
    print(f"\nKey observation:")
    for runs in sorted(by_runs.keys()):
        f_values = [count for _, count in by_runs[runs]]
        print(f"  {runs} runs: max f(s) = {max(f_values)}")

def count_runs(s):
    """Count number of runs"""
    if len(s) == 0:
        return 0
    runs = 1
    for i in range(len(s) - 1):
        if s[i] != s[i+1]:
            runs += 1
    return runs

def analyze_specific_transition(n, s1, s2):
    """
    Analyze what happens when we transform sequence s1 to s2.
    Show which permutations are gained/lost.
    """
    print(f"\n{'='*60}")
    print(f"TRANSITION ANALYSIS: {sequence_to_string(s1)} -> {sequence_to_string(s2)}")
    print(f"{'='*60}")

    f1, perms1 = compute_f(s1, n)
    f2, perms2 = compute_f(s2, n)

    perms1_set = set(perms1)
    perms2_set = set(perms2)

    gained = perms2_set - perms1_set
    lost = perms1_set - perms2_set

    print(f"\nf(s1) = {f1}")
    print(f"f(s2) = {f2}")
    print(f"Change: {f2 - f1:+d}")

    print(f"\nPermutations lost ({len(lost)}):")
    for perm in sorted(lost)[:5]:
        print(f"  {perm}")

    print(f"\nPermutations gained ({len(gained)}):")
    for perm in sorted(gained)[:5]:
        print(f"  {perm}")

def prove_by_examples(n):
    """
    Generate concrete examples showing why alternating is better.
    """
    print(f"\n{'='*60}")
    print(f"CONCRETE EXAMPLES (n={n})")
    print(f"{'='*60}")

    # Compare a sequence with a run vs alternating
    if n >= 4:
        # Example: ++- vs +-+
        s_run = [1, 1, -1]
        s_alt = [1, -1, 1]

        if len(s_run) == n-1:
            analyze_specific_transition(n, s_run, s_alt)

def main():
    """Run all analyses"""
    for n in [3, 4, 5]:
        analyze_permutation_sharing(n)
        analyze_bijection_structure(n)
        analyze_run_effects(n)
        if n == 4:
            prove_by_examples(n)

    # Additional insight
    print("\n" + "="*60)
    print("THEORETICAL INSIGHTS")
    print("="*60)
    print("""
Key findings:

1. PARTITION PROPERTY:
   Each permutation of [n] has a unique signature (rise/fall pattern).
   This signature IS the sequence s that counts it.
   Therefore: sum of all f(s) = n!

2. MAXIMIZATION:
   f(s) counts permutations with signature s.
   Alternating sequences count "zigzag" or "alternating" permutations.
   These are known as Euler numbers (OEIS A000111).

3. WHY ALTERNATING IS MAXIMAL:
   An alternating permutation has maximum "flexibility" - it uses
   the full range of values optimally. Non-alternating patterns
   impose additional constraints that reduce the count.

4. RIGOROUS PROOF NEEDED:
   To prove alternating is maximal, we need to show:
   - Any non-alternating s has a run (consecutive same signs)
   - Breaking that run increases f(s) (or keeps it same)
   - Therefore, alternating sequences (no runs) are maximal

   The challenge: "breaking a run increases f(s)" is NOT always true!
   We found counterexamples where breaking DECREASES f(s).

   The correct statement: "fully alternating achieves maximum" can be
   proven by showing alternating permutations are counted correctly
   and any other pattern counts fewer (or equal).
    """)

if __name__ == "__main__":
    main()
