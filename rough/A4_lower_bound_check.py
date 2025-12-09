#!/usr/bin/env python3
"""
Verify the lower bound argument for A4.

The key claim is that the chromatic number (or orthogonal rank) of C_n
provides a lower bound on k.

For odd n: chromatic number = 3
For even n: chromatic number = 2

But the solution claims orthogonal rank = ceil(sqrt(n)) for odd n.
Let's verify this numerically.
"""

import numpy as np

def is_adjacent_cycle(i, j, n):
    """Check if i and j are adjacent in cycle C_n."""
    diff = abs(i - j)
    return diff == 1 or diff == n - 1

def max_independent_set_size(n):
    """
    Find maximum independent set in C_n.
    For a cycle, this is floor(n/2).
    """
    return n // 2

def find_independent_set(n, size):
    """
    Find an independent set of given size in C_n.

    An independent set means no two vertices are adjacent.
    For cycle C_n, vertices at distance >= 2 form independent set.
    """
    if size > n // 2:
        return None  # Impossible

    # Simple greedy: take every other vertex
    if size <= n // 2:
        return list(range(0, size * 2, 2))

    return None

def verify_independent_set(vertices, n):
    """Verify that vertices form an independent set in C_n."""
    for i in range(len(vertices)):
        for j in range(i + 1, len(vertices)):
            if is_adjacent_cycle(vertices[i], vertices[j], n):
                return False
    return True

def analyze_cycle(n):
    """Analyze properties of cycle C_n."""
    print(f"\nAnalyzing C_{n}:")
    print(f"  n = {n}")
    print(f"  sqrt(n) = {np.sqrt(n):.2f}")
    print(f"  ceil(sqrt(n)) = {int(np.ceil(np.sqrt(n)))}")

    # Maximum independent set
    max_indep = max_independent_set_size(n)
    print(f"  Maximum independent set size: {max_indep} = floor(n/2)")

    # Check if we can find an independent set of size ceil(sqrt(n))
    target_size = int(np.ceil(np.sqrt(n)))

    # Try to find independent set of this size
    # For cycle, spacing must be at least 2
    min_spacing = 2
    max_with_spacing = n // min_spacing

    print(f"  Target independent set size: {target_size}")
    print(f"  Max independent set with spacing >= 2: {max_with_spacing}")

    if target_size <= max_with_spacing:
        # Find vertices with spacing
        spacing = n // target_size
        vertices = [i * spacing for i in range(target_size)]

        if verify_independent_set(vertices, n):
            print(f"  Found independent set of size {target_size}:")
            print(f"    Vertices: {vertices[:10]}{'...' if len(vertices) > 10 else ''}")
            print(f"    Spacing: {spacing}")

            # Check pairwise distances
            min_dist = float('inf')
            for i in range(len(vertices)):
                for j in range(i + 1, len(vertices)):
                    dist = min(abs(vertices[i] - vertices[j]),
                              n - abs(vertices[i] - vertices[j]))
                    min_dist = min(min_dist, dist)
            print(f"    Minimum distance between vertices: {min_dist}")
            return True
        else:
            print(f"  Failed to verify independent set")
            return False
    else:
        print(f"  Cannot find independent set of size {target_size}")
        return False

# Test various n values
print("="*70)
print("ANALYZING CYCLE GRAPHS C_n")
print("="*70)

test_values = [
    4, 9, 16, 25, 36, 49, 64, 81, 100, 121, 144, 169, 196, 225,
    2025
]

print("\nChecking if independent set of size ceil(sqrt(n)) exists:")
print("-" * 70)

for n in test_values:
    found = analyze_cycle(n)

# Summary
print("\n" + "="*70)
print("CRITICAL OBSERVATION")
print("="*70)
print("""
The solution claims that having an independent set of size ceil(sqrt(n))
implies a lower bound k >= ceil(sqrt(n)).

However, for a CYCLE C_n:
- Maximum independent set size = floor(n/2)
- This is MUCH LARGER than ceil(sqrt(n))!

For n = 2025:
- Maximum independent set: floor(2025/2) = 1012
- ceil(sqrt(2025)) = 45

The argument that "45 pairwise non-commuting matrices requires k >= 45"
is based on orthogonal rank, which is a different concept.

Orthogonal rank is about representing the graph as orthogonality of vectors,
not about matrix commutativity patterns!
""")

print("\n" + "="*70)
print("QUESTION: What is the ACTUAL lower bound?")
print("="*70)
print("""
If we have n/2 pairwise non-commuting matrices, does that mean k >= n/2?

No! Two matrices can fail to commute even if k is small.

The lower bound must come from a different argument, possibly:
1. Spectral properties of the cycle graph
2. Representation theory constraints
3. Algebraic structure of commutator algebras

The claim k = ceil(sqrt(n)) needs stronger justification.
""")
