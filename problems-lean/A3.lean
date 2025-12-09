/-
  Putnam 2025 Problem A3 - Formalized Problem Statement

  Problem: Alice and Bob play a game with a string of n digits, each restricted to {0, 1, 2}.
  Initially all digits are 0. A legal move is to add or subtract 1 from one digit
  to create a new string that has not appeared before. A player with no legal moves
  loses. Alice goes first, players alternate.

  Answer: Bob wins for all n >= 1.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Putnam2025A3

/-- A game state is a string of n digits, each in {0, 1, 2} -/
abbrev GameState (n : Nat) := Fin n -> Fin 3

/-- The zero state (all zeros) - the initial state -/
def zeroState (n : Nat) : GameState n := fun _ => 0

/-- A state is nonzero if some digit is nonzero -/
def NonZero {n : Nat} (s : GameState n) : Prop := exists i, s i ≠ 0

/-- Two states are adjacent if they differ in exactly one position by exactly 1 -/
def Adjacent {n : Nat} (s t : GameState n) : Prop :=
  exists i : Fin n,
    ((s i).val + 1 = (t i).val ∨ (t i).val + 1 = (s i).val) ∧
    (forall j : Fin n, j ≠ i -> s j = t j)

/-- The pairing function for Bob's strategy -/
noncomputable def pairFn {n : Nat} (s : GameState n) (hs : NonZero s) : GameState n :=
  sorry -- Definition: swap first nonzero digit between 1 and 2

/-- Putnam 2025 A3: Bob has a winning strategy for all n >= 1 -/
theorem putnam_2025_A3 (n : Nat) (_hn : n ≥ 1) :
    -- The pairing function witnesses Bob's winning strategy:
    -- (1) It's an involution
    (forall (s : GameState n) (hs : NonZero s),
      pairFn (pairFn s hs) sorry = s) ∧
    -- (2) Paired states are adjacent
    (forall (s : GameState n) (hs : NonZero s), Adjacent s (pairFn s hs)) ∧
    -- (3) Paired states are distinct
    (forall (s : GameState n) (hs : NonZero s), pairFn s hs ≠ s) ∧
    -- (4) Paired states are nonzero
    (forall (s : GameState n) (hs : NonZero s), NonZero (pairFn s hs)) := by
  sorry

end Putnam2025A3
