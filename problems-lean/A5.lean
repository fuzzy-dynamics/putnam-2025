/-
  Putnam 2025 Problem A5 - Formalized Problem Statement

  Problem: For a positive integer n >= 3, define a sign sequence to be a sequence
  s_1, s_2, ..., s_{n-1} where each s_i is either + or -.

  For a permutation (a_1, a_2, ..., a_n) of (1, 2, ..., n), the permutation satisfies
  the sign sequence if:
  - s_i = + implies a_{i+1} > a_i
  - s_i = - implies a_{i+1} < a_i

  Let f(s) denote the number of permutations satisfying the sign sequence s.

  Prove: for n >= 3, the alternating sequences (+, -, +, -, ...) and (-, +, -, +, ...)
  are the UNIQUE maximizers of f among all sign sequences of length n-1.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic

namespace Putnam2025A5

open Finset BigOperators Classical

/-! ## Core Definitions -/

/-- A sign sequence of length n-1 (for permutations of n elements) -/
def SignSeq (n : Nat) := Fin (n - 1) → Bool

/-- The alternating sequence starting with + (ascent): true, false, true, false, ... -/
def altPlus (n : Nat) : SignSeq n := fun i => i.val % 2 = 0

/-- The alternating sequence starting with - (descent): false, true, false, true, ... -/
def altMinus (n : Nat) : SignSeq n := fun i => i.val % 2 = 1

/-- Negation of a sign sequence -/
def negSignSeq {n : Nat} (s : SignSeq n) : SignSeq n := fun i => !s i

/-- A permutation satisfies a sign sequence if consecutive comparisons match -/
def Satisfies {n : Nat} (perm : Equiv.Perm (Fin n)) (s : SignSeq n) : Prop :=
  ∀ (i : Fin (n - 1)),
    let i_curr : Fin n := ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩
    let i_next : Fin n := ⟨i.val + 1, Nat.lt_pred_iff.mp i.isLt⟩
    (s i = true → (perm i_next).val > (perm i_curr).val) ∧
    (s i = false → (perm i_next).val < (perm i_curr).val)

/-- Decidability of Satisfies -/
instance {n : Nat} (perm : Equiv.Perm (Fin n)) (s : SignSeq n) : Decidable (Satisfies perm s) := by
  unfold Satisfies; infer_instance

/-- The set of permutations satisfying a sign sequence -/
def SatisfyingPerms {n : Nat} (s : SignSeq n) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun perm => Satisfies perm s)

/-- f(s) = number of permutations satisfying s -/
noncomputable def f {n : Nat} (s : SignSeq n) : Nat := (SatisfyingPerms s).card

/-! ## Main Theorem Statement -/

/-- Putnam 2025 A5: The alternating sequences uniquely maximize f -/
theorem putnam_2025_A5 (n : Nat) (hn : n ≥ 3) (s : SignSeq n)
    (hs_plus : s ≠ altPlus n) (hs_minus : s ≠ altMinus n) :
    f s < f (altPlus n) := by
  sorry

/-- Corollary: The maximizers are exactly altPlus and altMinus -/
theorem putnam_2025_A5_characterization (n : Nat) (hn : n ≥ 3) (s : SignSeq n)
    (hmax : ∀ t : SignSeq n, f t ≤ f s) :
    s = altPlus n ∨ s = altMinus n := by
  sorry

end Putnam2025A5
