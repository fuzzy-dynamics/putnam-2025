/-
  Putnam 2025 Problem B1 - Formalized Problem Statement

  Problem: Suppose that each point in the plane is colored either red or green,
  subject to the following condition: For every three noncollinear points A, B, C
  of the same color, the center of the circle passing through A, B, and C is also
  this color.

  Prove that all points of the plane are the same color.
-/

import Mathlib.Tactic

namespace Putnam2025B1

open Set Real

abbrev Point := ℝ × ℝ

def Coloring := Point → Bool

/-- Three points are noncollinear (not on a single line) -/
def Noncollinear (A B C : Point) : Prop :=
  A ≠ B ∧ B ≠ C ∧ A ≠ C ∧ ¬∃ (t : ℝ), C - A = t • (B - A)

/-- The circumcenter of three points -/
noncomputable def circumcenter (A B C : Point) : Point :=
  let d := 2 * (A.1 * (B.2 - C.2) + B.1 * (C.2 - A.2) + C.1 * (A.2 - B.2))
  let ux := ((A.1^2 + A.2^2) * (B.2 - C.2) + (B.1^2 + B.2^2) * (C.2 - A.2) +
             (C.1^2 + C.2^2) * (A.2 - B.2)) / d
  let uy := ((A.1^2 + A.2^2) * (C.1 - B.1) + (B.1^2 + B.2^2) * (A.1 - C.1) +
             (C.1^2 + C.2^2) * (B.1 - A.1)) / d
  (ux, uy)

/-- The coloring condition: circumcenters of same-color triples have that color -/
def ColoringCondition (c : Coloring) : Prop :=
  ∀ A B C : Point, Noncollinear A B C →
    c A = c B → c B = c C →
    c (circumcenter A B C) = c A

/-- Putnam 2025 B1: Under the coloring condition, all points have the same color -/
theorem putnam_2025_B1 (c : Coloring) (hc : ColoringCondition c) :
    (∀ p : Point, c p = true) ∨ (∀ p : Point, c p = false) := by
  sorry

end Putnam2025B1
