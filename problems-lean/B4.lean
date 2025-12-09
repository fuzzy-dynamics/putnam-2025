/-
  Putnam 2025 Problem B4 - Formalized Problem Statement

  Problem: For n >= 2, let A be an n x n matrix of nonnegative integers satisfying:
  (a) a_{i,j} = 0 when i + j <= n (1-indexed)
  (b) a_{i+1,j} in {a_{i,j}, a_{i,j}+1}
  (c) a_{i,j+1} in {a_{i,j}, a_{i,j}+1}

  Prove 3S <= (n+2)N where S = sum of entries and N = count of nonzeros.
-/

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card

open Finset BigOperators

/-- Original problem structure with exact conditions (non-decreasing). -/
structure PutnamB4Matrix (n : Nat) where
  a : Fin n → Fin n → Nat
  zero_region : ∀ i j : Fin n, i.val + j.val + 2 ≤ n → a i j = 0
  vert_nondec : ∀ i j : Fin n, (hi : i.val + 1 < n) →
    let i' : Fin n := ⟨i.val + 1, hi⟩
    a i j ≤ a i' j ∧ a i' j ≤ a i j + 1
  horiz_nondec : ∀ i j : Fin n, (hj : j.val + 1 < n) →
    let j' : Fin n := ⟨j.val + 1, hj⟩
    a i j ≤ a i j' ∧ a i j' ≤ a i j + 1

variable {n : Nat}

/--
Putnam 2025 B4: For matrices satisfying the given conditions, 3S <= (n+2)N.
-/
theorem putnam_2025_B4 (hn : n ≥ 2) (A : PutnamB4Matrix n) :
    3 * (∑ i : Fin n, ∑ j : Fin n, A.a i j) ≤
    (n + 2) * (∑ i : Fin n, (univ.filter (fun j : Fin n => A.a i j ≠ 0)).card) := by
  sorry
