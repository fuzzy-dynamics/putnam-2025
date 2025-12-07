#!/usr/bin/env python3
"""
Visualize the game graph and pairing for Putnam 2025 A3.
"""

from typing import Tuple, List, Set
from itertools import product


def string_to_tuple(s: str) -> Tuple[int, ...]:
    return tuple(int(d) for d in s)


def tuple_to_string(t: Tuple[int, ...]) -> str:
    return ''.join(str(d) for d in t)


def pair_state(s: Tuple[int, ...]) -> Tuple[int, ...]:
    if all(d == 0 for d in s):
        return None

    for i, digit in enumerate(s):
        if digit != 0:
            paired = list(s)
            paired[i] = 3 - s[i]
            return tuple(paired)
    return None


def get_neighbors(s: Tuple[int, ...]) -> List[Tuple[int, ...]]:
    neighbors = []
    n = len(s)

    for i in range(n):
        if s[i] < 2:
            neighbor = list(s)
            neighbor[i] = s[i] + 1
            neighbors.append(tuple(neighbor))

        if s[i] > 0:
            neighbor = list(s)
            neighbor[i] = s[i] - 1
            neighbors.append(tuple(neighbor))

    return neighbors


def visualize_game_graph(n: int):
    """Print a textual representation of the game graph."""
    print(f"\n{'='*60}")
    print(f"Game Graph for n={n}")
    print(f"{'='*60}\n")

    # Generate all states
    all_states = list(product(range(3), repeat=n))
    all_states.sort()

    zero_state = tuple([0] * n)
    non_zero_states = [s for s in all_states if s != zero_state]

    print(f"Total states: {len(all_states)}")
    print(f"Non-zero states: {len(non_zero_states)}\n")

    # Print adjacency information
    print("State Adjacencies:")
    print("-" * 60)
    for state in all_states:
        neighbors = get_neighbors(state)
        state_str = tuple_to_string(state)
        neighbors_str = [tuple_to_string(nb) for nb in neighbors]
        print(f"{state_str}: neighbors = {neighbors_str}")

    print("\n" + "="*60)
    print("Pairing Information (Non-zero states only)")
    print("="*60 + "\n")

    pairs_shown = set()
    for state in non_zero_states:
        paired = pair_state(state)
        pair_key = tuple(sorted([state, paired]))

        if pair_key not in pairs_shown:
            pairs_shown.add(pair_key)
            s1_str = tuple_to_string(state)
            s2_str = tuple_to_string(paired)

            # Check if they're neighbors
            neighbors = get_neighbors(state)
            is_adjacent = paired in neighbors

            print(f"Pair: {s1_str} <-> {s2_str}")
            print(f"  Adjacent: {is_adjacent}")
            print(f"  First nonzero position: {next(i for i, d in enumerate(state) if d != 0) + 1}")
            print()


def trace_game_with_pairing(n: int):
    """Trace a complete game showing the pairing at each step."""
    print(f"\n{'='*60}")
    print(f"Game Trace with Pairing (n={n})")
    print(f"{'='*60}\n")

    zero_state = tuple([0] * n)
    visited = {zero_state}
    current_state = zero_state
    move_number = 0
    alice_turn = True

    print(f"Initial state: {tuple_to_string(zero_state)}")
    print(f"Visited: {{{tuple_to_string(zero_state)}}}\n")

    while True:
        player = "Alice" if alice_turn else "Bob"

        neighbors = get_neighbors(current_state)
        legal_moves = [nb for nb in neighbors if nb not in visited]

        if not legal_moves:
            winner = "Bob" if alice_turn else "Alice"
            print(f"{player} has no legal moves.")
            print(f"\nWINNER: {winner}")
            break

        if alice_turn:
            next_state = legal_moves[0]
            print(f"Move {move_number + 1}: Alice moves {tuple_to_string(current_state)} -> {tuple_to_string(next_state)}")
        else:
            paired_state = pair_state(current_state)
            next_state = paired_state
            print(f"Move {move_number + 1}: Bob moves {tuple_to_string(current_state)} -> {tuple_to_string(next_state)} [pair({tuple_to_string(current_state)})]")

        move_number += 1
        visited.add(next_state)
        current_state = next_state
        alice_turn = not alice_turn

        # Show visited states organized by pairs
        visited_nonzero = [s for s in visited if s != zero_state]
        if visited_nonzero:
            pairs = []
            singles = []
            accounted = set()

            for s in visited_nonzero:
                if s in accounted:
                    continue
                paired = pair_state(s)
                if paired in visited_nonzero:
                    pairs.append((s, paired))
                    accounted.add(s)
                    accounted.add(paired)
                else:
                    singles.append(s)

            print(f"  Visited pairs: {[f'{{{tuple_to_string(a)}, {tuple_to_string(b)}}}' for a, b in pairs]}")
            if singles:
                print(f"  Unpaired visited: {[tuple_to_string(s) for s in singles]}")
        print()


def main():
    for n in [1, 2]:
        visualize_game_graph(n)
        trace_game_with_pairing(n)

    print("\n" + "="*60)
    print("Summary of Pairing Strategy")
    print("="*60)
    print("\nKey observations:")
    print("1. All non-zero states are partitioned into pairs")
    print("2. Each pair consists of adjacent states (one move apart)")
    print("3. Bob's strategy: respond to Alice's move by completing the pair")
    print("4. After each Bob move, all visited non-zero states form complete pairs")
    print("5. When Alice moves to an unvisited state, its pair is also unvisited")
    print("6. Bob can always move to the pair, which is adjacent and unvisited")
    print("7. Eventually all pairs are visited, Alice has no moves, Bob wins")


if __name__ == "__main__":
    main()
