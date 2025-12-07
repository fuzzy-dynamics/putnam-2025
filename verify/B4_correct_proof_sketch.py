#!/usr/bin/env python3
"""
Find the correct proof for S <= (n+2)N/3.

KEY INSIGHT:
The bound is NOT about average depth of nonzero entries.
Instead, it's about the relationship between S and N.

Let me try a different approach: INDUCTION on the matrix structure.

ALTERNATIVE INSIGHT:
Maybe we should think about this differently:
- We know a_{i,j} <= i+j-n (depth)
- But when a_{i,j} is close to the depth bound, it must have "support"
- High values require many smaller values below them

Let's verify: For each nonzero entry, how much "support" does it need?
"""

import numpy as np
from verify_B4 import generate_all_valid_matrices, compute_S_N

def compute_support_structure(A: np.ndarray):
    """
    For each nonzero entry at position (i,j), compute how many nonzero
    entries are needed to "support" it (i.e., are on paths from boundary).
    """
    n = len(A)

    # For each nonzero entry, find all positions it depends on
    dependencies = {}

    for i in range(n):
        for j in range(n):
            if A[i][j] > 0:
                # BFS to find all positions this depends on
                deps = set()
                queue = [(i, j)]
                visited = set()

                while queue:
                    ci, cj = queue.pop(0)
                    if (ci, cj) in visited:
                        continue
                    visited.add((ci, cj))

                    # Check if at boundary
                    if (ci+1) + (cj+1) == n + 1:
                        # At boundary, can only have value 0 or 1
                        continue

                    # Add predecessors that must be nonzero
                    # if value > 1, at least one predecessor must be nonzero
                    if A[ci][cj] > 1:
                        # Check predecessors
                        if ci > 0 and A[ci-1][cj] > 0:
                            deps.add((ci-1, cj))
                            queue.append((ci-1, cj))
                        if cj > 0 and A[ci][cj-1] > 0:
                            deps.add((ci, cj-1))
                            queue.append((ci, cj-1))

                dependencies[(i, j)] = deps

    return dependencies

def analyze_sum_vs_count_tradeoff(n: int):
    """
    Analyze: When we have N nonzero entries, what's the maximum S?

    Key question: Is there a "budget" where we trade off between:
    - Having many entries (large N)
    - Having high-value entries (large S/N)
    """
    print(f"\n{'='*60}")
    print(f"Sum vs Count Tradeoff (n={n})")
    print(f"{'='*60}")

    matrices = generate_all_valid_matrices(n)

    # Group by N, find max S for each N
    max_S_by_N = {}

    for A in matrices:
        S, N = compute_S_N(A)
        if N not in max_S_by_N:
            max_S_by_N[N] = []
        max_S_by_N[N].append((S, A.copy()))

    # For each N, find the maximum S
    print(f"\nFor each N, maximum S and whether bound holds:")
    print(f"{'N':>3} {'max(S)':>7} {'bound':>7} {'S/N':>7} {'bound/N':>7} {'status':>10}")
    print("-" * 60)

    for N in sorted(max_S_by_N.keys()):
        if N == 0:
            continue

        max_S = max(S for S, _ in max_S_by_N[N])
        bound = (n + 2) * N / 3
        ratio = max_S / N
        bound_ratio = (n + 2) / 3

        status = "TIGHT" if abs(max_S - bound) < 1e-9 else "slack"

        print(f"{N:3d} {max_S:7.1f} {bound:7.3f} {ratio:7.3f} {bound_ratio:7.3f} {status:>10}")

        # Show the matrix achieving max S for this N
        max_matrix = [A for S, A in max_S_by_N[N] if S == max_S][0]

        if abs(max_S - bound) < 1e-9:
            print(f"  Matrix achieving maximum S for N={N}:")
            print(f"{np.array2string(max_matrix, prefix='  ')}")

def compute_path_length_to_boundary(A: np.ndarray):
    """
    For each nonzero entry, compute the minimum number of steps to reach
    the boundary of the nonzero region.
    """
    n = len(A)
    distances = {}

    for i in range(n):
        for j in range(n):
            depth = (i+1) + (j+1) - n
            if depth > 0 and A[i][j] > 0:
                # Minimum steps to boundary = depth
                distances[(i, j)] = depth

    return distances

def verify_clever_counting(n: int):
    """
    Try to find a clever counting argument.

    Idea: Sum S over all entries, but count each "unit of value"
    based on how far it is from the boundary.

    Each entry a_{i,j} contributes a_{i,j} to S.
    But maybe we can decompose this contribution based on depth?
    """
    print(f"\n{'='*60}")
    print(f"Clever Counting (n={n})")
    print(f"{'='*60}")

    matrices = generate_all_valid_matrices(n)

    # For the tight matrix (all filled), analyze the structure
    tight_matrices = []
    bound = (n + 2) / 3

    for A in matrices:
        S, N = compute_S_N(A)
        if N > 0 and abs(S/N - bound) < 1e-9:
            tight_matrices.append(A)

    if tight_matrices:
        A = tight_matrices[0]
        print(f"\nTight matrix:")
        print(A)

        S, N = compute_S_N(A)
        print(f"S = {S}, N = {N}, S/N = {S/N:.6f}")

        # Analyze structure
        print(f"\nEntries by depth:")
        for d in range(1, n+1):
            entries_at_d = []
            for i in range(n):
                for j in range(n):
                    if (i+1) + (j+1) - n == d and A[i][j] > 0:
                        entries_at_d.append(((i+1, j+1), A[i][j]))

            if entries_at_d:
                total_value = sum(v for _, v in entries_at_d)
                count = len(entries_at_d)
                print(f"  Depth {d}: {count} entries, total value = {total_value}, avg = {total_value/count:.2f}")

def main():
    for n in [2, 3]:
        analyze_sum_vs_count_tradeoff(n)
        verify_clever_counting(n)

if __name__ == "__main__":
    main()
