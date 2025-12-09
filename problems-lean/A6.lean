/-
  Putnam 2025 Problem A6 - Formalized Problem Statement

  Problem: Let b_0 = 0 and, for n >= 0, define b_{n+1} = 2*b_n^2 + b_n + 1.

  For each k >= 1, show that b_{2^{k+1}} - 2*b_{2^k} is divisible by 2^{2k+2}
  but not by 2^{2k+3}.
-/

import Mathlib

namespace Putnam2025A6

/-! ## Core Definitions -/

/-- The sequence b_n defined by b_0 = 0 and b_{n+1} = 2*b_n^2 + b_n + 1 -/
def b : ℕ → ℤ
  | 0 => 0
  | n + 1 => 2 * (b n) ^ 2 + b n + 1

-- Computational verification of first values
example : b 0 = 0 := rfl
example : b 1 = 1 := rfl
example : b 2 = 4 := rfl
example : b 3 = 37 := rfl
example : b 4 = 2776 := rfl

/-! ## Main Theorem Statement -/

/-- Putnam 2025 A6: b_{2^{k+1}} - 2*b_{2^k} is divisible by 2^{2k+2} but not 2^{2k+3} -/
theorem putnam_2025_A6 (k : ℕ) (hk : 1 ≤ k) :
    (2 ^ (2 * k + 2) : ℤ) ∣ (b (2 ^ (k + 1)) - 2 * b (2 ^ k)) ∧
    ¬((2 ^ (2 * k + 3) : ℤ) ∣ (b (2 ^ (k + 1)) - 2 * b (2 ^ k))) := by
  sorry

end Putnam2025A6
