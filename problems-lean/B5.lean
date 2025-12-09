/-
  Putnam 2025 Problem B5 - Formalized Problem Statement

  Problem: For prime p > 3, let I(k) be the modular inverse of k mod p (in {1,...,p-1}).
  Define D = #{k in {1,...,p-2} : I(k+1) < I(k)}.
  Prove: D > p/4 - 1
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Putnam2025B5

open Finset BigOperators

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- The modular inverse of k mod p, as a natural number in {0, ..., p-1} -/
noncomputable def I (k : ℕ) : ℕ := ((k : ZMod p)⁻¹).val

/-- Count of descents: positions k in {1, ..., p-2} where I(k+1) < I(k) -/
noncomputable def D : ℕ :=
  (filter (fun k => I p (k + 1) < I p k) (Icc 1 (p - 2))).card

/-- Putnam 2025 B5: For prime p > 3, the descent count D > p/4 - 1 -/
theorem putnam_2025_B5 (hp : p > 3) : (p : ℚ) / 4 - 1 < D p := by
  sorry

end Putnam2025B5
