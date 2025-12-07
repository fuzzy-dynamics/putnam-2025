# Verification Report: Putnam 2025 A3

## Problem Statement

Alice and Bob play a game with a string of $n$ digits, each of which is restricted to be $0, 1,$ or $2$. Initially all the digits are $0$. A legal move is to add or subtract $1$ from one digit to create a new string that has not appeared before. A player with no legal moves loses. Alice goes first.

For each $n \geq 1$, determine which player has a strategy to win.

## Claimed Solution

**Answer:** Bob wins for all $n \geq 1$.

**Strategy:** Bob uses a pairing strategy where for any non-zero string $s$, he defines $\mathrm{pair}(s)$ by finding the first non-zero digit and swapping it between $1 \leftrightarrow 2$ (i.e., replacing it with $3 - s_i$). Whenever Alice moves to state $u$, Bob responds by moving to $\mathrm{pair}(u)$.

## Verification Results

### 1. Pairing Properties

All claimed properties of the pairing function have been verified:

#### Property 1: Well-Defined
- **Claim:** The pairing is well-defined on all non-zero strings.
- **Verification:** PASSED for $n = 1, 2, 3$
- **Reason:** Every non-zero string has at least one non-zero digit.

#### Property 2: No Fixed Points
- **Claim:** $\mathrm{pair}(s) \neq s$ for all $s \neq 0^n$.
- **Verification:** PASSED for $n = 1, 2, 3$
- **Reason:** At the first non-zero position $i$, we have $s_i \in \{1, 2\}$ and $3 - s_i \in \{2, 1\}$, so $s_i \neq 3 - s_i$.

#### Property 3: Never Maps to Zero
- **Claim:** $\mathrm{pair}(s) \neq 0^n$ for all $s \neq 0^n$.
- **Verification:** PASSED for $n = 1, 2, 3$
- **Reason:** Position $i$ in $\mathrm{pair}(s)$ contains $3 - s_i \in \{1, 2\} \neq 0$.

#### Property 4: Involution
- **Claim:** $\mathrm{pair}(\mathrm{pair}(s)) = s$ for all non-zero $s$.
- **Verification:** PASSED for $n = 1, 2, 3$
- **Reason:** The first non-zero position is preserved, and $3 - (3 - s_i) = s_i$.

#### Property 5: Partition into Pairs
- **Claim:** The pairing partitions the $3^n - 1$ non-zero strings into $(3^n - 1)/2$ pairs.
- **Verification:** PASSED for $n = 1, 2, 3$
- **Counts:**
  - $n = 1$: $2$ non-zero states, $1$ pair
  - $n = 2$: $8$ non-zero states, $4$ pairs
  - $n = 3$: $26$ non-zero states, $13$ pairs

#### Property 6 (CRUCIAL): Adjacency
- **Claim:** $s$ and $\mathrm{pair}(s)$ are neighbors in the game graph (differ by $\pm 1$ in exactly one position).
- **Verification:** PASSED for $n = 1, 2, 3$
- **Reason:** The strings differ only at position $i$, where $|s_i - (3 - s_i)| = |2s_i - 3| = 1$.

### 2. Pairing Examples

#### For $n = 1$:
| String | First nonzero pos | pair(String) |
|--------|-------------------|--------------|
| 1      | 1                 | 2            |
| 2      | 1                 | 1            |

#### For $n = 2$:
| String | First nonzero pos | pair(String) |
|--------|-------------------|--------------|
| 01     | 2                 | 02           |
| 02     | 2                 | 01           |
| 10     | 1                 | 20           |
| 11     | 1                 | 21           |
| 12     | 1                 | 22           |
| 20     | 1                 | 10           |
| 21     | 1                 | 11           |
| 22     | 1                 | 12           |

### 3. Game Simulations

#### $n = 1$ Game Trace:
```
Move 1: Alice moves 0 -> 1
Move 2: Bob moves 1 -> 2
Alice has no legal moves.
WINNER: Bob
```

#### $n = 2$ Game Trace:
```
Move 1: Alice moves 00 -> 10
Move 2: Bob moves 10 -> 20
Move 3: Alice moves 20 -> 21
Move 4: Bob moves 21 -> 11
Move 5: Alice moves 11 -> 01
Move 6: Bob moves 01 -> 02
Move 7: Alice moves 02 -> 12
Move 8: Bob moves 12 -> 22
Alice has no legal moves.
WINNER: Bob
```

#### $n = 3$ Game Trace:
```
Move 1: Alice moves 000 -> 100
Move 2: Bob moves 100 -> 200
Move 3: Alice moves 200 -> 210
Move 4: Bob moves 210 -> 110
...
Move 25: Alice moves 022 -> 122
Move 26: Bob moves 122 -> 222
Alice has no legal moves.
WINNER: Bob
```

All $3^n - 1$ non-zero states are visited, confirming the game exhausts the entire state space.

### 4. Exhaustive Game Tree Search

For $n = 1, 2$, we performed exhaustive search through the game tree to verify that Bob can force a win regardless of Alice's strategy.

**Result:** VERIFIED for $n = 1, 2$

The search confirms that no matter which legal move Alice chooses at any point, Bob can always respond with the pairing strategy and eventually force Alice into a position with no legal moves.

### 5. Proof Completeness Analysis

The solution's proof is structured as follows:

#### Key Invariant
"After each of Bob's moves (and at the start), the set of visited non-zero states consists entirely of complete pairs."

#### Proof Structure
1. **Base case:** Initially only $0^n$ is visited (no non-zero states visited). Invariant holds vacuously.

2. **Inductive step:** Assume invariant holds after Bob's $k$-th move. When Alice makes her $(k+1)$-th move to state $u$:
   - $u$ is unvisited (legal move condition)
   - $u \neq 0^n$ (Alice moved away from a visited state)
   - **Claim:** $\mathrm{pair}(u)$ is unvisited
     - **Proof by contradiction:** If $\mathrm{pair}(u)$ is visited, then by the invariant, all visited non-zero states come in complete pairs. Since $\mathrm{pair}(u)$ is visited, its pair $\mathrm{pair}(\mathrm{pair}(u)) = u$ must also be visited. But $u$ is unvisited. Contradiction.
   - By Property 6, $\mathrm{pair}(u)$ is adjacent to $u$
   - Bob can legally move to $\mathrm{pair}(u)$
   - After Bob's move, visited non-zero states include the pair $\{u, \mathrm{pair}(u)\}$. Invariant restored.

3. **Termination:** The game must end since there are only $3^n$ states and no state can be revisited.

4. **Winner:** Since Bob can always respond to Alice's moves, it must be Alice who eventually runs out of legal moves. Thus Bob wins.

#### Verification of Proof Steps
- [x] Count of states is correct: $3^n$ total, $3^n - 1$ non-zero
- [x] Pairing partitions correctly: $(3^n - 1)/2$ pairs
- [x] Parity argument is sound: $3^n$ is odd, so $3^n - 1$ is even
- [x] Invariant is well-defined and meaningful
- [x] Base case holds
- [x] Inductive step logic is correct
- [x] Contradiction argument is valid
- [x] Bob's response is always legal (Property 6)
- [x] Game terminates (finite state space)
- [x] Winner determination is correct

### 6. Potential Issues Checked

We verified that the solution handles:

1. **Edge cases:**
   - [x] $n = 1$ (minimal case)
   - [x] Zero state is never paired (only non-zero states)
   - [x] First move from $0^n$ is always Alice's

2. **Pairing consistency:**
   - [x] First non-zero position is well-defined for all non-zero strings
   - [x] Swapping $1 \leftrightarrow 2$ always produces a valid digit
   - [x] Pairing preserves all other positions

3. **Strategy validity:**
   - [x] Bob's response is always to an adjacent state
   - [x] Bob's response is always to an unvisited state
   - [x] Bob never gets stuck with no legal move before Alice

## Conclusion

**VERDICT: The solution is CORRECT.**

The solution provides a complete, rigorous proof using a pairing strategy. All mathematical claims have been verified through:

1. Direct computation for small $n$
2. Exhaustive game tree search for $n = 1, 2$
3. Verification of all pairing properties for $n = 1, 2, 3$
4. Simulation of complete games for $n = 1, 2, 3$

The proof is elegant, using a simple pairing function that partitions the non-zero states into pairs of adjacent states. The invariant-based argument cleanly shows that Bob can always respond to Alice's moves, forcing Alice to eventually run out of legal moves.

**No revisions needed.** The solution meets Putnam standards for correctness and rigor.
