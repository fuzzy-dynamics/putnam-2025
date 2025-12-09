/-
  Putnam 2025 Problem B6 - Formalized Problem Statement

  Problem: Let N = {1, 2, 3, ...}. Find the largest real constant r such that
  there exists a function g: N -> N such that
    g(n+1) - g(n) >= (g(g(n)))^r for all n in N.

  Answer: r = 1/4, achieved by g(n) = n^2
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Putnam2025B6

open Real

/-- A function g: N -> N satisfies the constraint with exponent r if:
    1. g(n) >= 1 for all n >= 1 (maps to positive integers)
    2. g(n+1) - g(n) >= (g(g(n)))^r for all n >= 1 -/
def SatisfiesConstraint (g : ℕ → ℕ) (r : ℝ) : Prop :=
  (∀ n : ℕ, n ≥ 1 → g n ≥ 1) ∧
  (∀ n : ℕ, n ≥ 1 → (g (n + 1) : ℝ) - g n ≥ (g (g n) : ℝ) ^ r)

/-- Putnam 2025 B6: r = 1/4 is achievable (g(n) = n^2 works), and r > 1/4 is not. -/
theorem putnam_2025_B6 :
    (∃ g : ℕ → ℕ, SatisfiesConstraint g (1/4)) ∧
    (∀ r : ℝ, r > 1/4 → ¬∃ g : ℕ → ℕ, SatisfiesConstraint g r) := by
  sorry

end Putnam2025B6
