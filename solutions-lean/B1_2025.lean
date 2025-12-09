/-
  Putnam 2025 Problem B1 - Complete Formalization

  PROBLEM:
  Suppose that each point in the plane is colored either red or green, subject to
  the following condition: For every three noncollinear points A, B, C of the same
  color, the center of the circle passing through A, B, and C is also this color.
  Prove that all points of the plane are the same color.

  SOLUTION APPROACH:
  Key Lemma: If X has color c, any circle centered at X has at most 2 opposite-color points.
  Main Theorem: Direct counting argument with circle intersections leads to contradiction.

  This proof uses NO axioms and NO sorry statements.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace Putnam2025B1

open Set Real

set_option maxHeartbeats 4000000

/-! ## Core Definitions -/

abbrev Point := ℝ × ℝ

def Coloring := Point → Bool

/-- Squared Euclidean distance -/
def distSq (P Q : Point) : ℝ := (P.1 - Q.1)^2 + (P.2 - Q.2)^2

/-- A point lies on a circle centered at X with radius r -/
def OnCircle (P X : Point) (r : ℝ) : Prop := distSq P X = r^2

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

/-! ## Basic Distance Lemmas -/

lemma distSq_nonneg (P Q : Point) : distSq P Q ≥ 0 := by
  unfold distSq
  nlinarith [sq_nonneg (P.1 - Q.1), sq_nonneg (P.2 - Q.2)]

lemma distSq_eq_zero_iff (P Q : Point) : distSq P Q = 0 ↔ P = Q := by
  unfold distSq
  constructor
  · intro h
    have h1 : (P.1 - Q.1)^2 ≥ 0 := sq_nonneg _
    have h2 : (P.2 - Q.2)^2 ≥ 0 := sq_nonneg _
    have hx : (P.1 - Q.1)^2 = 0 := by nlinarith
    have hy : (P.2 - Q.2)^2 = 0 := by nlinarith
    have hx' : P.1 = Q.1 := by nlinarith [sq_nonneg (P.1 - Q.1)]
    have hy' : P.2 = Q.2 := by nlinarith [sq_nonneg (P.2 - Q.2)]
    exact Prod.ext hx' hy'
  · intro h; simp [h]

lemma distSq_pos_of_ne (P Q : Point) (h : P ≠ Q) : distSq P Q > 0 := by
  have hge := distSq_nonneg P Q
  have hne : distSq P Q ≠ 0 := fun heq => h (distSq_eq_zero_iff P Q |>.mp heq)
  rcases hge.lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd heq.symm hne

/-! ## Line-Circle Intersection: at most 2 points (PROVEN) -/

lemma line_circle_at_most_two (X A B : Point) (r : ℝ) (hr : r > 0)
    (hA : OnCircle A X r) (hB : OnCircle B X r) (hAB : A ≠ B)
    (t : ℝ) (ht : distSq (A.1 + t * (B.1 - A.1), A.2 + t * (B.2 - A.2)) X = r^2) :
    t = 0 ∨ t = 1 := by
  unfold OnCircle at hA hB
  unfold distSq at hA hB ht

  set a₁ := A.1 - X.1 with ha1_def
  set a₂ := A.2 - X.2 with ha2_def
  set b₁ := B.1 - A.1 with hb1_def
  set b₂ := B.2 - A.2 with hb2_def

  have hexpand : (A.1 + t * (B.1 - A.1) - X.1)^2 + (A.2 + t * (B.2 - A.2) - X.2)^2 =
                 (a₁ + t * b₁)^2 + (a₂ + t * b₂)^2 := by ring

  rw [hexpand] at ht

  have hquad : (a₁ + t * b₁)^2 + (a₂ + t * b₂)^2 =
               a₁^2 + a₂^2 + 2*t*(a₁*b₁ + a₂*b₂) + t^2*(b₁^2 + b₂^2) := by ring

  rw [hquad] at ht

  have hA' : a₁^2 + a₂^2 = r^2 := by
    simp only [ha1_def, ha2_def]
    convert hA using 2 <;> ring

  have hB' : (a₁ + b₁)^2 + (a₂ + b₂)^2 = r^2 := by
    simp only [ha1_def, ha2_def, hb1_def, hb2_def]
    convert hB using 2 <;> ring

  have hB'' : a₁^2 + a₂^2 + 2*(a₁*b₁ + a₂*b₂) + (b₁^2 + b₂^2) = r^2 := by
    calc a₁^2 + a₂^2 + 2*(a₁*b₁ + a₂*b₂) + (b₁^2 + b₂^2)
        = (a₁ + b₁)^2 + (a₂ + b₂)^2 := by ring
      _ = r^2 := hB'

  have hsum : 2*(a₁*b₁ + a₂*b₂) + (b₁^2 + b₂^2) = 0 := by linarith

  have hcoef_pos : b₁^2 + b₂^2 > 0 := by
    have : distSq B A > 0 := distSq_pos_of_ne B A (ne_comm.mpr hAB)
    unfold distSq at this
    simp only [hb1_def, hb2_def]
    convert this using 2 <;> ring

  have hdot : 2*(a₁*b₁ + a₂*b₂) = -(b₁^2 + b₂^2) := by linarith

  -- We have: a₁^2 + a₂^2 = r^2 (hA')
  -- We have: 2*(a₁*b₁ + a₂*b₂) = -(b₁^2 + b₂^2) (hdot)
  -- We have: a₁^2 + a₂^2 + 2*t*(a₁*b₁ + a₂*b₂) + t^2*(b₁^2 + b₂^2) = r^2 (ht)
  -- Subtracting hA' from ht: 2*t*(a₁*b₁ + a₂*b₂) + t^2*(b₁^2 + b₂^2) = 0
  -- Substituting hdot: t*(-(b₁^2 + b₂^2)) + t^2*(b₁^2 + b₂^2) = 0
  -- Factor: (b₁^2 + b₂^2)*(t^2 - t) = 0
  have hsubst : 2*t*(a₁*b₁ + a₂*b₂) + t^2*(b₁^2 + b₂^2) = 0 := by linarith

  have hmul : t * (t - 1) = 0 := by
    -- Substitute: 2*(a₁*b₁ + a₂*b₂) = -(b₁^2 + b₂^2)
    -- So: t*(-(b₁^2 + b₂^2)) + t^2*(b₁^2 + b₂^2) = 0
    -- Which gives: (b₁^2 + b₂^2)*(t^2 - t) = 0
    have hdot' : a₁*b₁ + a₂*b₂ = -(b₁^2 + b₂^2) / 2 := by linarith
    have h1 : t * (-(b₁^2 + b₂^2)) + t^2 * (b₁^2 + b₂^2) = 0 := by
      have : 2*t*(a₁*b₁ + a₂*b₂) = 2*t*(-(b₁^2 + b₂^2) / 2) := by rw [hdot']
      have h2 : 2*t*(-(b₁^2 + b₂^2) / 2) = t * (-(b₁^2 + b₂^2)) := by ring
      linarith
    have h2 : (b₁^2 + b₂^2) * (t^2 - t) = 0 := by linarith
    have hne : b₁^2 + b₂^2 ≠ 0 := by linarith
    have h3 : t^2 - t = 0 := by
      by_contra hcontra
      have : (b₁^2 + b₂^2) = 0 := by
        have := mul_eq_zero.mp h2
        rcases this with hL | hR
        · exact hL
        · exact absurd hR hcontra
      linarith
    linarith
  rcases mul_eq_zero.mp hmul with h | h
  · left; exact h
  · right; linarith

/-! ## Three distinct points on a circle are noncollinear (PROVEN) -/

lemma circle_points_noncollinear (X : Point) (r : ℝ) (hr : r > 0)
    (A B C : Point) (hA : OnCircle A X r) (hB : OnCircle B X r) (hC : OnCircle C X r)
    (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C) : Noncollinear A B C := by
  unfold Noncollinear
  refine ⟨hAB, hBC, hAC, ?_⟩
  intro ⟨t, ht⟩
  -- C - A = t * (B - A) means C = A + t * (B - A)
  have hC_param : C = (A.1 + t * (B.1 - A.1), A.2 + t * (B.2 - A.2)) := by
    have hx := congrArg Prod.fst ht
    have hy := congrArg Prod.snd ht
    simp only [Prod.fst_sub, Prod.snd_sub] at hx hy
    have hx' : C.1 - A.1 = t * (B.1 - A.1) := by
      simp only [Prod.smul_fst, smul_eq_mul] at hx
      exact hx
    have hy' : C.2 - A.2 = t * (B.2 - A.2) := by
      simp only [Prod.smul_snd, smul_eq_mul] at hy
      exact hy
    ext
    · linarith
    · linarith

  have hC' : distSq (A.1 + t * (B.1 - A.1), A.2 + t * (B.2 - A.2)) X = r^2 := by
    rw [← hC_param]; exact hC

  rcases line_circle_at_most_two X A B r hr hA hB hAB t hC' with h | h
  · rw [h] at hC_param
    simp at hC_param
    exact hAC hC_param.symm
  · rw [h] at hC_param
    simp at hC_param
    exact hBC hC_param.symm

/-! ## Circumcenter properties (PROVEN) -/

lemma circumcenter_equidistant (A B C : Point) (hnoncollin : Noncollinear A B C) :
    distSq A (circumcenter A B C) = distSq B (circumcenter A B C) ∧
    distSq B (circumcenter A B C) = distSq C (circumcenter A B C) := by
  unfold circumcenter distSq Noncollinear at *
  obtain ⟨hAB, hBC, hAC, hnotline⟩ := hnoncollin
  set d := 2 * (A.1 * (B.2 - C.2) + B.1 * (C.2 - A.2) + C.1 * (A.2 - B.2)) with hd_def

  have hd_ne : d ≠ 0 := by
    intro hd_zero
    push_neg at hnotline
    simp only [hd_def] at hd_zero
    have harea : A.1 * (B.2 - C.2) + B.1 * (C.2 - A.2) + C.1 * (A.2 - B.2) = 0 := by linarith
    by_cases hx : B.1 = A.1
    · have hy : B.2 ≠ A.2 := by
        intro hy
        apply hAB
        exact Prod.ext hx.symm hy.symm
      have hBA_ne : B.2 - A.2 ≠ 0 := sub_ne_zero.mpr hy
      -- With B.1 = A.1, the area formula simplifies:
      -- A.1*(B.2-C.2) + A.1*(C.2-A.2) + C.1*(A.2-B.2) = 0
      -- = A.1*(B.2 - A.2) + C.1*(A.2 - B.2) = 0
      -- = (A.1 - C.1)*(B.2 - A.2) = 0
      -- With hx: B.1 = A.1, substitute B.1 → A.1 in harea
      have hsimp : (A.1 - C.1) * (B.2 - A.2) = 0 := by
        have h1 : A.1 * (B.2 - C.2) + A.1 * (C.2 - A.2) + C.1 * (A.2 - B.2) = 0 := by
          calc A.1 * (B.2 - C.2) + A.1 * (C.2 - A.2) + C.1 * (A.2 - B.2)
              = B.1 * (B.2 - C.2) + B.1 * (C.2 - A.2) + C.1 * (A.2 - B.2) := by rw [← hx]
            _ = A.1 * (B.2 - C.2) + B.1 * (C.2 - A.2) + C.1 * (A.2 - B.2) := by rw [hx]
            _ = 0 := harea
        have h2 : A.1 * (B.2 - A.2) + C.1 * (A.2 - B.2) = 0 := by linarith
        linarith
      have hC1 : C.1 = A.1 := by
        rcases mul_eq_zero.mp hsimp with hL | hR
        · linarith
        · exact absurd hR hBA_ne
      specialize hnotline ((C.2 - A.2) / (B.2 - A.2))
      apply hnotline
      ext
      · simp only [Prod.fst_sub, Prod.smul_fst, smul_eq_mul]
        rw [hC1, hx]; ring
      · simp only [Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
        field_simp [hBA_ne]
    · -- B.1 ≠ A.1 case
      push_neg at hx
      have hBA_ne : B.1 - A.1 ≠ 0 := sub_ne_zero.mpr hx
      have hkey : (C.2 - A.2) * (B.1 - A.1) = (C.1 - A.1) * (B.2 - A.2) := by
        have hexp : A.1*B.2 - A.1*C.2 + B.1*C.2 - B.1*A.2 + C.1*A.2 - C.1*B.2 = 0 := by linarith
        linarith
      specialize hnotline ((C.1 - A.1) / (B.1 - A.1))
      apply hnotline
      ext
      · simp only [Prod.fst_sub, Prod.smul_fst, smul_eq_mul]
        field_simp [hBA_ne]
      · simp only [Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
        field_simp [hBA_ne]; linarith

  constructor <;> {
    field_simp
    ring
  }

lemma equidistant_is_circumcenter (A B C X : Point) (hnoncollin : Noncollinear A B C)
    (hXA_XB : distSq A X = distSq B X) (hXB_XC : distSq B X = distSq C X) :
    X = circumcenter A B C := by
  unfold distSq circumcenter at *
  unfold Noncollinear at hnoncollin
  obtain ⟨hAB, hBC, hAC, hnotline⟩ := hnoncollin

  have eq1 : 2*(B.1 - A.1)*X.1 + 2*(B.2 - A.2)*X.2 = B.1^2 + B.2^2 - A.1^2 - A.2^2 := by nlinarith
  have eq2 : 2*(C.1 - B.1)*X.1 + 2*(C.2 - B.2)*X.2 = C.1^2 + C.2^2 - B.1^2 - B.2^2 := by nlinarith

  set d := 2 * (A.1 * (B.2 - C.2) + B.1 * (C.2 - A.2) + C.1 * (A.2 - B.2)) with hd_def

  have hd_ne : d ≠ 0 := by
    intro hd_zero
    push_neg at hnotline
    simp only [hd_def] at hd_zero
    have harea : A.1 * (B.2 - C.2) + B.1 * (C.2 - A.2) + C.1 * (A.2 - B.2) = 0 := by linarith
    by_cases hx : B.1 = A.1
    · have hy : B.2 ≠ A.2 := by
        intro hy
        apply hAB
        exact Prod.ext hx.symm hy.symm
      have hBA_ne : B.2 - A.2 ≠ 0 := sub_ne_zero.mpr hy
      have hsimp : (A.1 - C.1) * (B.2 - A.2) = 0 := by
        have h1 : A.1 * (B.2 - C.2) + A.1 * (C.2 - A.2) + C.1 * (A.2 - B.2) = 0 := by
          calc A.1 * (B.2 - C.2) + A.1 * (C.2 - A.2) + C.1 * (A.2 - B.2)
              = B.1 * (B.2 - C.2) + B.1 * (C.2 - A.2) + C.1 * (A.2 - B.2) := by rw [← hx]
            _ = A.1 * (B.2 - C.2) + B.1 * (C.2 - A.2) + C.1 * (A.2 - B.2) := by rw [hx]
            _ = 0 := harea
        have h2 : A.1 * (B.2 - A.2) + C.1 * (A.2 - B.2) = 0 := by linarith
        linarith
      have hC1 : C.1 = A.1 := by
        rcases mul_eq_zero.mp hsimp with hL | hR
        · linarith
        · exact absurd hR hBA_ne
      specialize hnotline ((C.2 - A.2) / (B.2 - A.2))
      apply hnotline
      ext
      · simp only [Prod.fst_sub, Prod.smul_fst, smul_eq_mul]
        rw [hC1, hx]; ring
      · simp only [Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
        field_simp [hBA_ne]
    · push_neg at hx
      have hBA_ne : B.1 - A.1 ≠ 0 := sub_ne_zero.mpr hx
      have hkey : (C.2 - A.2) * (B.1 - A.1) = (C.1 - A.1) * (B.2 - A.2) := by
        have hexp : A.1*B.2 - A.1*C.2 + B.1*C.2 - B.1*A.2 + C.1*A.2 - C.1*B.2 = 0 := by linarith
        linarith
      specialize hnotline ((C.1 - A.1) / (B.1 - A.1))
      apply hnotline
      ext
      · simp only [Prod.fst_sub, Prod.smul_fst, smul_eq_mul]
        field_simp [hBA_ne]
      · simp only [Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
        field_simp [hBA_ne]; linarith

  have hdet : 4*((B.1-A.1)*(C.2-B.2) - (B.2-A.2)*(C.1-B.1)) = 2*d := by
    simp only [hd_def]; ring

  have hdet_ne : (B.1-A.1)*(C.2-B.2) - (B.2-A.2)*(C.1-B.1) ≠ 0 := by
    intro h
    have h2d : 2*d = 0 := by simp only [hd_def] at hdet ⊢; linarith
    have hd' : d = 0 := by linarith
    exact hd_ne hd'

  set rhs1 := B.1^2 + B.2^2 - A.1^2 - A.2^2 with hrhs1_def
  set rhs2 := C.1^2 + C.2^2 - B.1^2 - B.2^2 with hrhs2_def
  set det := 4*((B.1-A.1)*(C.2-B.2) - (B.2-A.2)*(C.1-B.1)) with hdet_def

  -- Use Cramer's rule: solve 2x2 linear system
  -- eq1: 2(B.1-A.1)X.1 + 2(B.2-A.2)X.2 = rhs1
  -- eq2: 2(C.1-B.1)X.1 + 2(C.2-B.2)X.2 = rhs2
  -- The determinant is 4*((B.1-A.1)(C.2-B.2) - (B.2-A.2)(C.1-B.1)) = det = 2d

  -- Multiply eq1 by (C.2-B.2) and eq2 by (B.2-A.2), then subtract
  have hX1_eq : X.1 * det = 2 * (rhs1*(C.2-B.2) - rhs2*(B.2-A.2)) := by
    have hmul1 : (2*(B.1 - A.1)*X.1 + 2*(B.2 - A.2)*X.2)*(C.2-B.2) = rhs1*(C.2-B.2) := by
      rw [eq1]
    have hmul2 : (2*(C.1 - B.1)*X.1 + 2*(C.2 - B.2)*X.2)*(B.2-A.2) = rhs2*(B.2-A.2) := by
      rw [eq2]
    -- Expand and simplify
    have hexp1 : 2*(B.1 - A.1)*X.1*(C.2-B.2) + 2*(B.2 - A.2)*X.2*(C.2-B.2) = rhs1*(C.2-B.2) := by
      linarith
    have hexp2 : 2*(C.1 - B.1)*X.1*(B.2-A.2) + 2*(C.2 - B.2)*X.2*(B.2-A.2) = rhs2*(B.2-A.2) := by
      linarith
    -- Subtract to eliminate X.2
    have hsub : 2*(B.1 - A.1)*X.1*(C.2-B.2) - 2*(C.1 - B.1)*X.1*(B.2-A.2) =
                rhs1*(C.2-B.2) - rhs2*(B.2-A.2) := by linarith
    -- Factor out X.1
    have hfactor : X.1 * (2*(B.1 - A.1)*(C.2-B.2) - 2*(C.1 - B.1)*(B.2-A.2)) =
                   rhs1*(C.2-B.2) - rhs2*(B.2-A.2) := by linarith
    -- The coefficient of X.1 equals det/2
    simp only [hdet_def]
    linarith

  have hX1 : X.1 = (rhs1*(C.2-B.2) - rhs2*(B.2-A.2)) / (det/2) := by
    have hdet' : det ≠ 0 := by
      simp only [hdet_def]
      intro h
      have : (B.1 - A.1) * (C.2 - B.2) - (B.2 - A.2) * (C.1 - B.1) = 0 := by linarith
      exact hdet_ne this
    field_simp [hdet']
    linarith

  -- Similarly for X.2
  have hX2_eq : X.2 * det = 2 * ((B.1-A.1)*rhs2 - (C.1-B.1)*rhs1) := by
    have hmul1 : (2*(B.1 - A.1)*X.1 + 2*(B.2 - A.2)*X.2)*(C.1-B.1) = rhs1*(C.1-B.1) := by
      rw [eq1]
    have hmul2 : (2*(C.1 - B.1)*X.1 + 2*(C.2 - B.2)*X.2)*(B.1-A.1) = rhs2*(B.1-A.1) := by
      rw [eq2]
    have hexp1 : 2*(B.1 - A.1)*X.1*(C.1-B.1) + 2*(B.2 - A.2)*X.2*(C.1-B.1) = rhs1*(C.1-B.1) := by
      linarith
    have hexp2 : 2*(C.1 - B.1)*X.1*(B.1-A.1) + 2*(C.2 - B.2)*X.2*(B.1-A.1) = rhs2*(B.1-A.1) := by
      linarith
    have hsub : 2*(C.2 - B.2)*X.2*(B.1-A.1) - 2*(B.2 - A.2)*X.2*(C.1-B.1) =
                rhs2*(B.1-A.1) - rhs1*(C.1-B.1) := by linarith
    have hfactor : X.2 * (2*(C.2 - B.2)*(B.1-A.1) - 2*(B.2 - A.2)*(C.1-B.1)) =
                   rhs2*(B.1-A.1) - rhs1*(C.1-B.1) := by linarith
    simp only [hdet_def]
    linarith

  have hX2 : X.2 = ((B.1-A.1)*rhs2 - (C.1-B.1)*rhs1) / (det/2) := by
    have hdet' : det ≠ 0 := by
      simp only [hdet_def]
      intro h
      have : (B.1 - A.1) * (C.2 - B.2) - (B.2 - A.2) * (C.1 - B.1) = 0 := by linarith
      exact hdet_ne this
    field_simp [hdet']
    linarith

  have hd_ne' : d ≠ 0 := hd_ne

  ext
  · -- X.1 = circumcenter.1
    simp only [hX1, hrhs1_def, hrhs2_def, hdet_def, hd_def, circumcenter]
    have hne : 2 * (A.1 * (B.2 - C.2) + B.1 * (C.2 - A.2) + C.1 * (A.2 - B.2)) ≠ 0 := hd_ne
    have hne' : (B.1 - A.1) * (C.2 - B.2) - (B.2 - A.2) * (C.1 - B.1) ≠ 0 := hdet_ne
    field_simp [hne, hne']
    ring
  · -- X.2 = circumcenter.2
    simp only [hX2, hrhs1_def, hrhs2_def, hdet_def, hd_def, circumcenter]
    have hne : 2 * (A.1 * (B.2 - C.2) + B.1 * (C.2 - A.2) + C.1 * (A.2 - B.2)) ≠ 0 := hd_ne
    have hne' : (B.1 - A.1) * (C.2 - B.2) - (B.2 - A.2) * (C.1 - B.1) ≠ 0 := hdet_ne
    field_simp [hne, hne']
    ring

lemma circumcenter_is_center (X : Point) (r : ℝ) (hr : r > 0)
    (A B C : Point) (hA : OnCircle A X r) (hB : OnCircle B X r) (hC : OnCircle C X r)
    (hnoncollin : Noncollinear A B C) : circumcenter A B C = X := by
  unfold OnCircle at hA hB hC
  have hXA_XB : distSq A X = distSq B X := by rw [hA, hB]
  have hXB_XC : distSq B X = distSq C X := by rw [hB, hC]
  exact (equidistant_is_circumcenter A B C X hnoncollin hXA_XB hXB_XC).symm

/-! ## KEY LEMMA: At most 2 opposite-color points on any circle (PROVEN) -/

lemma at_most_two_opposite (c : Coloring) (hc : ColoringCondition c)
    (X : Point) (r : ℝ) (hr : r > 0)
    (A B D : Point) (hA : OnCircle A X r) (hB : OnCircle B X r) (hD : OnCircle D X r)
    (hAB : A ≠ B) (hBD : B ≠ D) (hAD : A ≠ D) :
    ¬(c A ≠ c X ∧ c B ≠ c X ∧ c D ≠ c X) := by
  intro ⟨hA_opp, hB_opp, hD_opp⟩
  have hnoncollin := circle_points_noncollinear X r hr A B D hA hB hD hAB hBD hAD
  have hcircum := circumcenter_is_center X r hr A B D hA hB hD hnoncollin
  have hAB_same : c A = c B := by cases hcA : c A <;> cases hcB : c B <;> cases hcX : c X <;> simp_all
  have hBD_same : c B = c D := by cases hcB : c B <;> cases hcD : c D <;> cases hcX : c X <;> simp_all
  have h := hc A B D hnoncollin hAB_same hBD_same
  rw [hcircum] at h
  cases hcA : c A <;> cases hcX : c X <;> simp_all

/-! ## Two circles intersection lemma (PROVEN) -/

noncomputable def dist' (P Q : Point) : ℝ := Real.sqrt (distSq P Q)

/-- Two circles with appropriate radii intersect in exactly 2 points -/
lemma two_circles_intersect (X Y : Point) (rX rY d : ℝ)
    (hrX : rX > 0) (hrY : rY > 0) (hd : d > 0)
    (hdist : distSq X Y = d^2)
    (hsum : rX + rY > d) (hdiff : |rX - rY| < d) :
    ∃ P Q : Point, P ≠ Q ∧ OnCircle P X rX ∧ OnCircle P Y rY ∧
                          OnCircle Q X rX ∧ OnCircle Q Y rY := by
  set x₀ := (d^2 + rX^2 - rY^2) / (2 * d) with hx0_def
  have hd_ne : d ≠ 0 := by linarith
  have h2d_ne : 2 * d ≠ 0 := by linarith

  -- Show y^2 > 0
  have hy_sq_pos : rX^2 - x₀^2 > 0 := by
    -- Substitute x₀ = (d^2 + rX^2 - rY^2) / (2d), then show
    -- rX^2 - x₀^2 = (rX + x₀)(rX - x₀) > 0
    -- After algebra: 4d^2(rX^2 - x₀^2) = (rY^2 - (d-rX)^2)((d+rX)^2 - rY^2)
    have hfact1 : rY^2 - (d - rX)^2 > 0 := by
      have h1 : rX - rY < d := by
        rcases abs_cases (rX - rY) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
      have h2 : rY - rX < d := by
        rcases abs_cases (rX - rY) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
      nlinarith [sq_nonneg (d - rX - rY), sq_nonneg (d - rX + rY)]
    have hfact2 : (d + rX)^2 - rY^2 > 0 := by
      have h2 : rY - rX < d := by
        rcases abs_cases (rX - rY) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
      nlinarith [sq_nonneg (d + rX - rY), sq_nonneg (d + rX + rY)]
    have h4d2_pos : 4 * d^2 > 0 := by nlinarith
    -- x₀ = (d^2 + rX^2 - rY^2) / (2d), so
    -- rX^2 - x₀^2 = rX^2 - ((d^2 + rX^2 - rY^2)/(2d))^2
    -- = (4d^2 rX^2 - (d^2 + rX^2 - rY^2)^2) / (4d^2)
    -- = ((2d rX + d^2 + rX^2 - rY^2)(2d rX - d^2 - rX^2 + rY^2)) / (4d^2)
    -- = ((d+rX)^2 - rY^2)(rY^2 - (d-rX)^2) / (4d^2)
    have hnum_pos : ((d + rX)^2 - rY^2) * (rY^2 - (d - rX)^2) > 0 := by nlinarith
    have hformula : rX^2 - x₀^2 = ((d + rX)^2 - rY^2) * (rY^2 - (d - rX)^2) / (4 * d^2) := by
      rw [hx0_def]
      have hd2_ne : d^2 ≠ 0 := by nlinarith
      have h4d2_ne : (4 : ℝ) * d^2 ≠ 0 := by nlinarith
      field_simp [hd_ne, h2d_ne, hd2_ne, h4d2_ne]
      ring
    rw [hformula]
    have h4d2_ne : (4 : ℝ) * d^2 ≠ 0 := by nlinarith
    positivity

  set y₀ := Real.sqrt (rX^2 - x₀^2) with hy0_def
  have hy0_pos : y₀ > 0 := Real.sqrt_pos.mpr hy_sq_pos

  -- Unit vector from X to Y and perpendicular
  set ux := (Y.1 - X.1) / d with hux_def
  set uy := (Y.2 - X.2) / d with huy_def
  set vx := -uy with hvx_def
  set vy := ux with hvy_def

  -- Intersection points
  set P := (X.1 + x₀ * ux + y₀ * vx, X.2 + x₀ * uy + y₀ * vy) with hP_def
  set Q := (X.1 + x₀ * ux - y₀ * vx, X.2 + x₀ * uy - y₀ * vy) with hQ_def

  use P, Q

  have hdistSq_XY : (Y.1 - X.1)^2 + (Y.2 - X.2)^2 = d^2 := by
    unfold distSq at hdist
    have h1 : (X.1 - Y.1)^2 = (Y.1 - X.1)^2 := by ring
    have h2 : (X.2 - Y.2)^2 = (Y.2 - X.2)^2 := by ring
    linarith

  have hunit : ux^2 + uy^2 = 1 := by
    have hne : d^2 ≠ 0 := by nlinarith
    -- ux = (Y.1 - X.1)/d, uy = (Y.2 - X.2)/d
    -- ux^2 + uy^2 = ((Y.1-X.1)^2 + (Y.2-X.2)^2)/d^2 = d^2/d^2 = 1
    have h1 : ux^2 = (Y.1 - X.1)^2 / d^2 := by
      have h : ux = (Y.1 - X.1) / d := rfl
      rw [h, div_pow, sq, sq]
    have h2 : uy^2 = (Y.2 - X.2)^2 / d^2 := by
      have h : uy = (Y.2 - X.2) / d := rfl
      rw [h, div_pow, sq, sq]
    rw [h1, h2]
    rw [← add_div]
    rw [hdistSq_XY]
    field_simp [hne]

  have hvunit : vx^2 + vy^2 = 1 := by
    simp only [hvx_def, hvy_def]
    have h : (-uy)^2 + ux^2 = ux^2 + uy^2 := by ring
    linarith [hunit]

  have hperp : ux * vx + uy * vy = 0 := by
    simp only [hvx_def, hvy_def]; ring

  have hy0_sq : y₀^2 = rX^2 - x₀^2 := Real.sq_sqrt (le_of_lt hy_sq_pos)

  constructor
  · -- P ≠ Q
    intro hPQ
    simp only [hP_def, hQ_def, Prod.mk.injEq] at hPQ
    have h1 : 2 * y₀ * vx = 0 := by linarith [hPQ.1]
    have h2 : 2 * y₀ * vy = 0 := by linarith [hPQ.2]
    have hy0_ne : y₀ ≠ 0 := by linarith
    have hvx0 : vx = 0 := by nlinarith
    have hvy0 : vy = 0 := by nlinarith
    have : vx^2 + vy^2 = 0 := by simp [hvx0, hvy0]
    linarith [hvunit]

  constructor
  · -- OnCircle P X rX
    unfold OnCircle distSq
    simp only [hP_def]
    calc (X.1 + x₀ * ux + y₀ * vx - X.1)^2 + (X.2 + x₀ * uy + y₀ * vy - X.2)^2
        = (x₀ * ux + y₀ * vx)^2 + (x₀ * uy + y₀ * vy)^2 := by ring
      _ = x₀^2 * (ux^2 + uy^2) + 2*x₀*y₀*(ux*vx + uy*vy) + y₀^2*(vx^2 + vy^2) := by ring
      _ = x₀^2 * 1 + 2*x₀*y₀*0 + y₀^2*1 := by rw [hunit, hperp, hvunit]
      _ = x₀^2 + y₀^2 := by ring
      _ = x₀^2 + (rX^2 - x₀^2) := by rw [hy0_sq]
      _ = rX^2 := by ring

  constructor
  · -- OnCircle P Y rY
    unfold OnCircle distSq
    simp only [hP_def]
    have hYX1 : Y.1 - X.1 = d * ux := by
      -- ux = (Y.1 - X.1) / d, so d * ux = Y.1 - X.1
      have h : ux = (Y.1 - X.1) / d := rfl
      rw [h, mul_div_cancel₀ (Y.1 - X.1) hd_ne]
    have hYX2 : Y.2 - X.2 = d * uy := by
      have h : uy = (Y.2 - X.2) / d := rfl
      rw [h, mul_div_cancel₀ (Y.2 - X.2) hd_ne]
    calc (X.1 + x₀ * ux + y₀ * vx - Y.1)^2 + (X.2 + x₀ * uy + y₀ * vy - Y.2)^2
        = ((x₀ - d) * ux + y₀ * vx)^2 + ((x₀ - d) * uy + y₀ * vy)^2 := by
            have h1 : X.1 + x₀ * ux + y₀ * vx - Y.1 = (x₀ - d) * ux + y₀ * vx := by linarith [hYX1]
            have h2 : X.2 + x₀ * uy + y₀ * vy - Y.2 = (x₀ - d) * uy + y₀ * vy := by linarith [hYX2]
            rw [h1, h2]
      _ = (x₀ - d)^2 * (ux^2 + uy^2) + 2*(x₀-d)*y₀*(ux*vx + uy*vy) + y₀^2*(vx^2 + vy^2) := by ring
      _ = (x₀ - d)^2 * 1 + 2*(x₀-d)*y₀*0 + y₀^2*1 := by rw [hunit, hperp, hvunit]
      _ = (x₀ - d)^2 + y₀^2 := by ring
      _ = (x₀ - d)^2 + (rX^2 - x₀^2) := by rw [hy0_sq]
      _ = rX^2 - 2*d*x₀ + d^2 := by ring
      _ = rX^2 - 2*d*((d^2 + rX^2 - rY^2) / (2 * d)) + d^2 := by rw [hx0_def]
      _ = rY^2 := by field_simp [hd_ne]; ring

  constructor
  · -- OnCircle Q X rX
    unfold OnCircle distSq
    simp only [hQ_def]
    calc (X.1 + x₀ * ux - y₀ * vx - X.1)^2 + (X.2 + x₀ * uy - y₀ * vy - X.2)^2
        = (x₀ * ux - y₀ * vx)^2 + (x₀ * uy - y₀ * vy)^2 := by ring
      _ = x₀^2 * (ux^2 + uy^2) - 2*x₀*y₀*(ux*vx + uy*vy) + y₀^2*(vx^2 + vy^2) := by ring
      _ = x₀^2 * 1 - 2*x₀*y₀*0 + y₀^2*1 := by rw [hunit, hperp, hvunit]
      _ = x₀^2 + y₀^2 := by ring
      _ = rX^2 := by rw [hy0_sq]; ring

  · -- OnCircle Q Y rY
    unfold OnCircle distSq
    simp only [hQ_def]
    have hYX1 : Y.1 - X.1 = d * ux := by
      have h : ux = (Y.1 - X.1) / d := rfl
      rw [h, mul_div_cancel₀ (Y.1 - X.1) hd_ne]
    have hYX2 : Y.2 - X.2 = d * uy := by
      have h : uy = (Y.2 - X.2) / d := rfl
      rw [h, mul_div_cancel₀ (Y.2 - X.2) hd_ne]
    calc (X.1 + x₀ * ux - y₀ * vx - Y.1)^2 + (X.2 + x₀ * uy - y₀ * vy - Y.2)^2
        = ((x₀ - d) * ux - y₀ * vx)^2 + ((x₀ - d) * uy - y₀ * vy)^2 := by
            have h1 : X.1 + x₀ * ux - y₀ * vx - Y.1 = (x₀ - d) * ux - y₀ * vx := by linarith [hYX1]
            have h2 : X.2 + x₀ * uy - y₀ * vy - Y.2 = (x₀ - d) * uy - y₀ * vy := by linarith [hYX2]
            rw [h1, h2]
      _ = (x₀ - d)^2 * (ux^2 + uy^2) - 2*(x₀-d)*y₀*(ux*vx + uy*vy) + y₀^2*(vx^2 + vy^2) := by ring
      _ = (x₀ - d)^2 * 1 - 2*(x₀-d)*y₀*0 + y₀^2*1 := by rw [hunit, hperp, hvunit]
      _ = (x₀ - d)^2 + y₀^2 := by ring
      _ = rY^2 := by rw [hy0_sq, hx0_def]; field_simp [hd_ne]; ring

/-! ## Distinct radius implies distinct point -/

lemma diff_radius_diff_point (X : Point) (r₁ r₂ : ℝ)
    (hr1_pos : r₁ > 0) (hr2_pos : r₂ > 0) (hr : r₁ ≠ r₂)
    (P : Point) (h1 : OnCircle P X r₁) (h2 : OnCircle P X r₂) : False := by
  unfold OnCircle at h1 h2
  have hsq : r₁^2 = r₂^2 := by linarith
  -- r₁^2 = r₂^2 means (r₁-r₂)(r₁+r₂) = 0
  have hdiff : (r₁ - r₂) * (r₁ + r₂) = 0 := by nlinarith [sq_nonneg r₁, sq_nonneg r₂]
  rcases mul_eq_zero.mp hdiff with h | h
  · exact hr (sub_eq_zero.mp h)
  · -- r₁ + r₂ = 0, but both are positive, contradiction
    linarith

/-! ## Main Theorem: Counting Argument -/

theorem no_opposite_colors (c : Coloring) (hc : ColoringCondition c)
    (X Y : Point) (hXY : X ≠ Y) (hcX : c X = true) (hcY : c Y = false) : False := by
  -- Let d = |XY| > 0
  set d := dist' X Y with hd_def
  have hd_pos : d > 0 := by
    unfold dist' at hd_def
    rw [hd_def]
    exact Real.sqrt_pos.mpr (distSq_pos_of_ne X Y hXY)

  have hdist : distSq X Y = d^2 := by
    unfold dist' at hd_def
    rw [hd_def]
    exact (Real.sq_sqrt (distSq_nonneg X Y)).symm

  -- Choose radii for circles P₁ (at X), P₂ (at X), and Q₁, Q₂, Q₃ (at Y)
  set r₁ := 5 * d / 8 with hr1_def
  set r₂ := 2 * d / 3 with hr2_def
  set s₁ := 11 * d / 18 with hs1_def
  set s₂ := 9 * d / 14 with hs2_def
  set s₃ := 3 * d / 5 with hs3_def

  have hr1_pos : r₁ > 0 := by simp only [hr1_def]; linarith
  have hr2_pos : r₂ > 0 := by simp only [hr2_def]; linarith
  have hs1_pos : s₁ > 0 := by simp only [hs1_def]; linarith
  have hs2_pos : s₂ > 0 := by simp only [hs2_def]; linarith
  have hs3_pos : s₃ > 0 := by simp only [hs3_def]; linarith

  have hr12 : r₁ ≠ r₂ := by simp only [hr1_def, hr2_def]; linarith
  have hs12 : s₁ ≠ s₂ := by simp only [hs1_def, hs2_def]; linarith
  have hs13 : s₁ ≠ s₃ := by simp only [hs1_def, hs3_def]; linarith
  have hs23 : s₂ ≠ s₃ := by simp only [hs2_def, hs3_def]; linarith

  -- Intersection conditions
  have hsum_11 : r₁ + s₁ > d := by simp only [hr1_def, hs1_def]; linarith
  have hsum_12 : r₁ + s₂ > d := by simp only [hr1_def, hs2_def]; linarith
  have hsum_13 : r₁ + s₃ > d := by simp only [hr1_def, hs3_def]; linarith
  have hsum_21 : r₂ + s₁ > d := by simp only [hr2_def, hs1_def]; linarith
  have hsum_22 : r₂ + s₂ > d := by simp only [hr2_def, hs2_def]; linarith

  have hdiff_11 : |r₁ - s₁| < d := by simp only [hr1_def, hs1_def]; rw [abs_sub_lt_iff]; constructor <;> linarith
  have hdiff_12 : |r₁ - s₂| < d := by simp only [hr1_def, hs2_def]; rw [abs_sub_lt_iff]; constructor <;> linarith
  have hdiff_13 : |r₁ - s₃| < d := by simp only [hr1_def, hs3_def]; rw [abs_sub_lt_iff]; constructor <;> linarith
  have hdiff_21 : |r₂ - s₁| < d := by simp only [hr2_def, hs1_def]; rw [abs_sub_lt_iff]; constructor <;> linarith
  have hdiff_22 : |r₂ - s₂| < d := by simp only [hr2_def, hs2_def]; rw [abs_sub_lt_iff]; constructor <;> linarith

  -- Get intersection points: P₁ ∩ Q₁, P₁ ∩ Q₂, P₁ ∩ Q₃
  obtain ⟨P11a, P11b, hP11_ne, hP11a_X, hP11a_Y, hP11b_X, hP11b_Y⟩ :=
    two_circles_intersect X Y r₁ s₁ d hr1_pos hs1_pos hd_pos hdist hsum_11 hdiff_11
  obtain ⟨P12a, P12b, hP12_ne, hP12a_X, hP12a_Y, hP12b_X, hP12b_Y⟩ :=
    two_circles_intersect X Y r₁ s₂ d hr1_pos hs2_pos hd_pos hdist hsum_12 hdiff_12
  obtain ⟨P13a, P13b, hP13_ne, hP13a_X, hP13a_Y, hP13b_X, hP13b_Y⟩ :=
    two_circles_intersect X Y r₁ s₃ d hr1_pos hs3_pos hd_pos hdist hsum_13 hdiff_13

  -- Get intersection points: P₂ ∩ Q₁, P₂ ∩ Q₂
  obtain ⟨P21a, P21b, hP21_ne, hP21a_X, hP21a_Y, hP21b_X, hP21b_Y⟩ :=
    two_circles_intersect X Y r₂ s₁ d hr2_pos hs1_pos hd_pos hdist hsum_21 hdiff_21
  obtain ⟨P22a, P22b, hP22_ne, hP22a_X, hP22a_Y, hP22b_X, hP22b_Y⟩ :=
    two_circles_intersect X Y r₂ s₂ d hr2_pos hs2_pos hd_pos hdist hsum_22 hdiff_22

  -- Points on different Y-circles are distinct
  have hP11a_ne_P12a : P11a ≠ P12a := fun h => diff_radius_diff_point Y s₁ s₂ hs1_pos hs2_pos hs12 P12a (h ▸ hP11a_Y) hP12a_Y
  have hP11a_ne_P12b : P11a ≠ P12b := fun h => diff_radius_diff_point Y s₁ s₂ hs1_pos hs2_pos hs12 P12b (h ▸ hP11a_Y) hP12b_Y
  have hP11b_ne_P12a : P11b ≠ P12a := fun h => diff_radius_diff_point Y s₁ s₂ hs1_pos hs2_pos hs12 P12a (h ▸ hP11b_Y) hP12a_Y
  have hP11b_ne_P12b : P11b ≠ P12b := fun h => diff_radius_diff_point Y s₁ s₂ hs1_pos hs2_pos hs12 P12b (h ▸ hP11b_Y) hP12b_Y
  have hP11a_ne_P13a : P11a ≠ P13a := fun h => diff_radius_diff_point Y s₁ s₃ hs1_pos hs3_pos hs13 P13a (h ▸ hP11a_Y) hP13a_Y
  have hP11a_ne_P13b : P11a ≠ P13b := fun h => diff_radius_diff_point Y s₁ s₃ hs1_pos hs3_pos hs13 P13b (h ▸ hP11a_Y) hP13b_Y
  have hP11b_ne_P13a : P11b ≠ P13a := fun h => diff_radius_diff_point Y s₁ s₃ hs1_pos hs3_pos hs13 P13a (h ▸ hP11b_Y) hP13a_Y
  have hP11b_ne_P13b : P11b ≠ P13b := fun h => diff_radius_diff_point Y s₁ s₃ hs1_pos hs3_pos hs13 P13b (h ▸ hP11b_Y) hP13b_Y
  have hP12a_ne_P13a : P12a ≠ P13a := fun h => diff_radius_diff_point Y s₂ s₃ hs2_pos hs3_pos hs23 P13a (h ▸ hP12a_Y) hP13a_Y
  have hP12a_ne_P13b : P12a ≠ P13b := fun h => diff_radius_diff_point Y s₂ s₃ hs2_pos hs3_pos hs23 P13b (h ▸ hP12a_Y) hP13b_Y
  have hP12b_ne_P13a : P12b ≠ P13a := fun h => diff_radius_diff_point Y s₂ s₃ hs2_pos hs3_pos hs23 P13a (h ▸ hP12b_Y) hP13a_Y
  have hP12b_ne_P13b : P12b ≠ P13b := fun h => diff_radius_diff_point Y s₂ s₃ hs2_pos hs3_pos hs23 P13b (h ▸ hP12b_Y) hP13b_Y

  -- Points on different X-circles are distinct
  have hP21a_ne_P11a : P21a ≠ P11a := fun h => diff_radius_diff_point X r₂ r₁ hr2_pos hr1_pos (Ne.symm hr12) P11a (h ▸ hP21a_X) hP11a_X
  have hP21a_ne_P11b : P21a ≠ P11b := fun h => diff_radius_diff_point X r₂ r₁ hr2_pos hr1_pos (Ne.symm hr12) P11b (h ▸ hP21a_X) hP11b_X
  have hP21b_ne_P11a : P21b ≠ P11a := fun h => diff_radius_diff_point X r₂ r₁ hr2_pos hr1_pos (Ne.symm hr12) P11a (h ▸ hP21b_X) hP11a_X
  have hP21b_ne_P11b : P21b ≠ P11b := fun h => diff_radius_diff_point X r₂ r₁ hr2_pos hr1_pos (Ne.symm hr12) P11b (h ▸ hP21b_X) hP11b_X
  have hP22a_ne_P12a : P22a ≠ P12a := fun h => diff_radius_diff_point X r₂ r₁ hr2_pos hr1_pos (Ne.symm hr12) P12a (h ▸ hP22a_X) hP12a_X
  have hP22a_ne_P12b : P22a ≠ P12b := fun h => diff_radius_diff_point X r₂ r₁ hr2_pos hr1_pos (Ne.symm hr12) P12b (h ▸ hP22a_X) hP12b_X
  have hP22b_ne_P12a : P22b ≠ P12a := fun h => diff_radius_diff_point X r₂ r₁ hr2_pos hr1_pos (Ne.symm hr12) P12a (h ▸ hP22b_X) hP12a_X
  have hP22b_ne_P12b : P22b ≠ P12b := fun h => diff_radius_diff_point X r₂ r₁ hr2_pos hr1_pos (Ne.symm hr12) P12b (h ▸ hP22b_X) hP12b_X

  -- P₂ ∩ Q₁ and P₂ ∩ Q₂ are disjoint
  have hP21a_ne_P22a : P21a ≠ P22a := fun h => diff_radius_diff_point Y s₁ s₂ hs1_pos hs2_pos hs12 P22a (h ▸ hP21a_Y) hP22a_Y
  have hP21a_ne_P22b : P21a ≠ P22b := fun h => diff_radius_diff_point Y s₁ s₂ hs1_pos hs2_pos hs12 P22b (h ▸ hP21a_Y) hP22b_Y
  have hP21b_ne_P22a : P21b ≠ P22a := fun h => diff_radius_diff_point Y s₁ s₂ hs1_pos hs2_pos hs12 P22a (h ▸ hP21b_Y) hP22a_Y
  have hP21b_ne_P22b : P21b ≠ P22b := fun h => diff_radius_diff_point Y s₁ s₂ hs1_pos hs2_pos hs12 P22b (h ▸ hP21b_Y) hP22b_Y

  -- P₁ has 6 points from 3 Q-circles. X is red, so at most 2 green on P₁.
  -- With 6 points in 3 pairs, at most 2 green means at least one pair is all-red.

  -- If pair (P11a, P11b) on Q₁ is all-red:
  --   Q₁ has 2 red points. Y is green, so at most 2 red on Q₁.
  --   P₂ ∩ Q₁ = {P21a, P21b} must be green (else 3 red on Q₁).
  --
  -- Similarly if (P12a, P12b) is all-red, then P22a, P22b are green.
  --
  -- Key insight: If g₁ + g₂ + g₃ ≤ 2 (green counts on P₁), and gᵢ ≥ 0, then either
  --   some gᵢ = 0 (all-red pair), OR g₁ = g₂ = g₃ = 1 impossible with sum ≤ 2.
  -- Actually if g₁ ≥ 1, g₂ ≥ 1, g₃ ≥ 1, sum ≥ 3 > 2. Contradiction.
  -- So at least one gᵢ = 0.

  -- Count green on each pair
  set g₁ := (if c P11a = false then 1 else 0) + (if c P11b = false then 1 else 0) with hg1_def
  set g₂ := (if c P12a = false then 1 else 0) + (if c P12b = false then 1 else 0) with hg2_def
  set g₃ := (if c P13a = false then 1 else 0) + (if c P13b = false then 1 else 0) with hg3_def

  -- Total green on P₁ ≤ 2 (else 3 green give contradiction via at_most_two_opposite)
  have htotal_le2 : g₁ + g₂ + g₃ ≤ 2 := by
    by_contra hcontra
    push_neg at hcontra
    have hge3 : g₁ + g₂ + g₃ ≥ 3 := by omega
    -- Find 3 distinct green points and apply at_most_two_opposite
    have hg1_le2 : g₁ ≤ 2 := by simp only [hg1_def]; split_ifs <;> omega
    have hg2_le2 : g₂ ≤ 2 := by simp only [hg2_def]; split_ifs <;> omega
    have hg3_le2 : g₃ ≤ 2 := by simp only [hg3_def]; split_ifs <;> omega
    -- Since sum ≥ 3 and each ≤ 2, at least one must be ≥ 1 in two different pairs
    -- Actually we can find 3 green points across the 6 points
    -- Case analysis to find 3 distinct green points
    simp only [hg1_def, hg2_def, hg3_def] at hge3 hg1_le2 hg2_le2 hg3_le2
    -- Case split on which points are green (c P = false means green, opposite of X)
    -- After split, find 3 green points and apply at_most_two_opposite
    split_ifs at hge3 hg1_le2 hg2_le2 hg3_le2 with h11 h11b h12a h12b h13a h13b <;> try omega
    -- For remaining goals: we have g₁+g₂+g₃ ≥ 3, so at least 3 green points exist
    -- Use a helper to prove c P ≠ c X from c P = false and c X = true
    all_goals (
      have aux : ∀ P, c P = false → c P ≠ c X := fun P hP => by simp [hP, hcX]
      first
      | exact at_most_two_opposite c hc X r₁ hr1_pos P11a P11b P12a hP11a_X hP11b_X hP12a_X hP11_ne hP11b_ne_P12a hP11a_ne_P12a ⟨aux _ ‹_›, aux _ ‹_›, aux _ ‹_›⟩
      | exact at_most_two_opposite c hc X r₁ hr1_pos P11a P11b P12b hP11a_X hP11b_X hP12b_X hP11_ne hP11b_ne_P12b hP11a_ne_P12b ⟨aux _ ‹_›, aux _ ‹_›, aux _ ‹_›⟩
      | exact at_most_two_opposite c hc X r₁ hr1_pos P11a P11b P13a hP11a_X hP11b_X hP13a_X hP11_ne hP11b_ne_P13a hP11a_ne_P13a ⟨aux _ ‹_›, aux _ ‹_›, aux _ ‹_›⟩
      | exact at_most_two_opposite c hc X r₁ hr1_pos P11a P11b P13b hP11a_X hP11b_X hP13b_X hP11_ne hP11b_ne_P13b hP11a_ne_P13b ⟨aux _ ‹_›, aux _ ‹_›, aux _ ‹_›⟩
      | exact at_most_two_opposite c hc X r₁ hr1_pos P11a P12a P12b hP11a_X hP12a_X hP12b_X hP11a_ne_P12a hP12_ne hP11a_ne_P12b ⟨aux _ ‹_›, aux _ ‹_›, aux _ ‹_›⟩
      | exact at_most_two_opposite c hc X r₁ hr1_pos P11a P12a P13a hP11a_X hP12a_X hP13a_X hP11a_ne_P12a hP12a_ne_P13a hP11a_ne_P13a ⟨aux _ ‹_›, aux _ ‹_›, aux _ ‹_›⟩
      | exact at_most_two_opposite c hc X r₁ hr1_pos P11a P12a P13b hP11a_X hP12a_X hP13b_X hP11a_ne_P12a hP12a_ne_P13b hP11a_ne_P13b ⟨aux _ ‹_›, aux _ ‹_›, aux _ ‹_›⟩
      | exact at_most_two_opposite c hc X r₁ hr1_pos P11a P12b P13a hP11a_X hP12b_X hP13a_X hP11a_ne_P12b hP12b_ne_P13a hP11a_ne_P13a ⟨aux _ ‹_›, aux _ ‹_›, aux _ ‹_›⟩
      | exact at_most_two_opposite c hc X r₁ hr1_pos P11a P12b P13b hP11a_X hP12b_X hP13b_X hP11a_ne_P12b hP12b_ne_P13b hP11a_ne_P13b ⟨aux _ ‹_›, aux _ ‹_›, aux _ ‹_›⟩
      | exact at_most_two_opposite c hc X r₁ hr1_pos P11a P13a P13b hP11a_X hP13a_X hP13b_X hP11a_ne_P13a hP13_ne hP11a_ne_P13b ⟨aux _ ‹_›, aux _ ‹_›, aux _ ‹_›⟩
      | exact at_most_two_opposite c hc X r₁ hr1_pos P11b P12a P12b hP11b_X hP12a_X hP12b_X hP11b_ne_P12a hP12_ne hP11b_ne_P12b ⟨aux _ ‹_›, aux _ ‹_›, aux _ ‹_›⟩
      | exact at_most_two_opposite c hc X r₁ hr1_pos P11b P12a P13a hP11b_X hP12a_X hP13a_X hP11b_ne_P12a hP12a_ne_P13a hP11b_ne_P13a ⟨aux _ ‹_›, aux _ ‹_›, aux _ ‹_›⟩
      | exact at_most_two_opposite c hc X r₁ hr1_pos P11b P12a P13b hP11b_X hP12a_X hP13b_X hP11b_ne_P12a hP12a_ne_P13b hP11b_ne_P13b ⟨aux _ ‹_›, aux _ ‹_›, aux _ ‹_›⟩
      | exact at_most_two_opposite c hc X r₁ hr1_pos P11b P12b P13a hP11b_X hP12b_X hP13a_X hP11b_ne_P12b hP12b_ne_P13a hP11b_ne_P13a ⟨aux _ ‹_›, aux _ ‹_›, aux _ ‹_›⟩
      | exact at_most_two_opposite c hc X r₁ hr1_pos P11b P12b P13b hP11b_X hP12b_X hP13b_X hP11b_ne_P12b hP12b_ne_P13b hP11b_ne_P13b ⟨aux _ ‹_›, aux _ ‹_›, aux _ ‹_›⟩
      | exact at_most_two_opposite c hc X r₁ hr1_pos P11b P13a P13b hP11b_X hP13a_X hP13b_X hP11b_ne_P13a hP13_ne hP11b_ne_P13b ⟨aux _ ‹_›, aux _ ‹_›, aux _ ‹_›⟩
      | exact at_most_two_opposite c hc X r₁ hr1_pos P12a P12b P13a hP12a_X hP12b_X hP13a_X hP12_ne hP12b_ne_P13a hP12a_ne_P13a ⟨aux _ ‹_›, aux _ ‹_›, aux _ ‹_›⟩
      | exact at_most_two_opposite c hc X r₁ hr1_pos P12a P12b P13b hP12a_X hP12b_X hP13b_X hP12_ne hP12b_ne_P13b hP12a_ne_P13b ⟨aux _ ‹_›, aux _ ‹_›, aux _ ‹_›⟩
      | exact at_most_two_opposite c hc X r₁ hr1_pos P12a P13a P13b hP12a_X hP13a_X hP13b_X hP12a_ne_P13a hP13_ne hP12a_ne_P13b ⟨aux _ ‹_›, aux _ ‹_›, aux _ ‹_›⟩
      | exact at_most_two_opposite c hc X r₁ hr1_pos P12b P13a P13b hP12b_X hP13a_X hP13b_X hP12b_ne_P13a hP13_ne hP12b_ne_P13b ⟨aux _ ‹_›, aux _ ‹_›, aux _ ‹_›⟩
      | omega)

  -- With 3 pairs and sum ≤ 2, at least one pair is all-red (has 0 green)
  have hfind_red_pair : g₁ = 0 ∨ g₂ = 0 ∨ g₃ = 0 := by
    by_contra hall
    push_neg at hall
    omega

  -- For each case, we derive contradiction
  rcases hfind_red_pair with hg1_zero | hg2_zero | hg3_zero

  · -- Case: g₁ = 0 (pair P11a, P11b is all-red)
    have hP11a_red : c P11a = true := by
      simp only [hg1_def] at hg1_zero; split_ifs at hg1_zero
      all_goals first | omega | (cases hb : c P11a <;> simp_all)
    have hP11b_red : c P11b = true := by
      simp only [hg1_def] at hg1_zero; split_ifs at hg1_zero
      all_goals first | omega | (cases hb : c P11b <;> simp_all)

    -- Q₁ has P11a, P11b red. Y is green. So at most 2 red on Q₁.
    -- Thus P21a, P21b must be green.
    have hP21a_green : c P21a = false := by
      by_contra h
      have hP21a_red : c P21a = true := by cases hc' : c P21a <;> simp_all
      exact at_most_two_opposite c hc Y s₁ hs1_pos P11a P11b P21a hP11a_Y hP11b_Y hP21a_Y hP11_ne (Ne.symm hP21a_ne_P11b) (Ne.symm hP21a_ne_P11a) ⟨by simp [hP11a_red, hcY], by simp [hP11b_red, hcY], by simp [hP21a_red, hcY]⟩

    have hP21b_green : c P21b = false := by
      by_contra h
      have hP21b_red : c P21b = true := by cases hc' : c P21b <;> simp_all
      exact at_most_two_opposite c hc Y s₁ hs1_pos P11a P11b P21b hP11a_Y hP11b_Y hP21b_Y hP11_ne (Ne.symm hP21b_ne_P11b) (Ne.symm hP21b_ne_P11a) ⟨by simp [hP11a_red, hcY], by simp [hP11b_red, hcY], by simp [hP21b_red, hcY]⟩

    -- Now we have 2 green on P₂. We need a 3rd green to get contradiction.
    -- From g₁ + g₂ + g₃ ≤ 2 and g₁ = 0, we have g₂ + g₃ ≤ 2.
    -- If g₂ = 0 too, pair P12a, P12b is all-red, so P22a, P22b are green.

    by_cases hg2_zero' : g₂ = 0
    · -- g₂ = 0: P12a, P12b are red
      have hP12a_red : c P12a = true := by simp only [hg2_def] at hg2_zero'; split_ifs at hg2_zero'; all_goals first | omega | (cases hb : c _ <;> simp_all)
      have hP12b_red : c P12b = true := by simp only [hg2_def] at hg2_zero'; split_ifs at hg2_zero'; all_goals first | omega | (cases hb : c _ <;> simp_all)

      have hP22a_green : c P22a = false := by
        by_contra h
        have hP22a_red : c P22a = true := by cases hc' : c P22a <;> simp_all
        exact at_most_two_opposite c hc Y s₂ hs2_pos P12a P12b P22a hP12a_Y hP12b_Y hP22a_Y hP12_ne (Ne.symm hP22a_ne_P12b) (Ne.symm hP22a_ne_P12a) ⟨by simp [hP12a_red, hcY], by simp [hP12b_red, hcY], by simp [hP22a_red, hcY]⟩

      -- P₂ now has P21a, P21b, P22a all green
      exact at_most_two_opposite c hc X r₂ hr2_pos P21a P21b P22a hP21a_X hP21b_X hP22a_X hP21_ne hP21b_ne_P22a hP21a_ne_P22a ⟨by simp [hP21a_green, hcX], by simp [hP21b_green, hcX], by simp [hP22a_green, hcX]⟩

    · -- g₂ ≥ 1
      by_cases hg3_zero' : g₃ = 0
      · -- g₃ = 0: P13a, P13b are red. Need P₂ ∩ Q₃.
        have hsum_23 : r₂ + s₃ > d := by simp only [hr2_def, hs3_def]; linarith
        have hdiff_23 : |r₂ - s₃| < d := by simp only [hr2_def, hs3_def]; rw [abs_sub_lt_iff]; constructor <;> linarith

        obtain ⟨P23a, P23b, hP23_ne, hP23a_X, hP23a_Y, hP23b_X, hP23b_Y⟩ :=
          two_circles_intersect X Y r₂ s₃ d hr2_pos hs3_pos hd_pos hdist hsum_23 hdiff_23

        have hP13a_red : c P13a = true := by simp only [hg3_def] at hg3_zero'; split_ifs at hg3_zero'; all_goals first | omega | (cases hb : c _ <;> simp_all)
        have hP13b_red : c P13b = true := by simp only [hg3_def] at hg3_zero'; split_ifs at hg3_zero'; all_goals first | omega | (cases hb : c _ <;> simp_all)

        have hP23a_ne_P13a : P23a ≠ P13a := fun h => diff_radius_diff_point X r₂ r₁ hr2_pos hr1_pos (Ne.symm hr12) P13a (h ▸ hP23a_X) hP13a_X
        have hP23a_ne_P13b : P23a ≠ P13b := fun h => diff_radius_diff_point X r₂ r₁ hr2_pos hr1_pos (Ne.symm hr12) P13b (h ▸ hP23a_X) hP13b_X

        have hP23a_green : c P23a = false := by
          by_contra h
          have hP23a_red : c P23a = true := by cases hc' : c P23a <;> simp_all
          exact at_most_two_opposite c hc Y s₃ hs3_pos P13a P13b P23a hP13a_Y hP13b_Y hP23a_Y hP13_ne (Ne.symm hP23a_ne_P13b) (Ne.symm hP23a_ne_P13a) ⟨by simp [hP13a_red, hcY], by simp [hP13b_red, hcY], by simp [hP23a_red, hcY]⟩

        have hP21a_ne_P23a : P21a ≠ P23a := fun h => diff_radius_diff_point Y s₁ s₃ hs1_pos hs3_pos hs13 P23a (h ▸ hP21a_Y) hP23a_Y
        have hP21b_ne_P23a : P21b ≠ P23a := fun h => diff_radius_diff_point Y s₁ s₃ hs1_pos hs3_pos hs13 P23a (h ▸ hP21b_Y) hP23a_Y

        exact at_most_two_opposite c hc X r₂ hr2_pos P21a P21b P23a hP21a_X hP21b_X hP23a_X hP21_ne hP21b_ne_P23a hP21a_ne_P23a ⟨by simp [hP21a_green, hcX], by simp [hP21b_green, hcX], by simp [hP23a_green, hcX]⟩

      · -- g₂ ≥ 1 and g₃ ≥ 1. With g₁ = 0 and g₂ + g₃ ≤ 2, we have g₂ = g₃ = 1.
        -- Q₂ has 1 red from P₁. At most 2 red on Q₂. So at least 1 of P22a, P22b is green.
        have hg2_eq1 : g₂ = 1 := by omega
        have hP12_one_red : (c P12a = true ∧ c P12b = false) ∨ (c P12a = false ∧ c P12b = true) := by
          simp only [hg2_def] at hg2_eq1
          cases hb0 : c P12a <;> cases hb1 : c P12b <;> simp_all

        have hP22_one_green : c P22a = false ∨ c P22b = false := by
          rcases hP12_one_red with ⟨hP12a_red, _⟩ | ⟨_, hP12b_red⟩
          · by_contra h
            push_neg at h
            have hP22a_red : c P22a = true := by cases hc' : c P22a <;> simp_all
            have hP22b_red : c P22b = true := by cases hc' : c P22b <;> simp_all
            exact at_most_two_opposite c hc Y s₂ hs2_pos P12a P22a P22b hP12a_Y hP22a_Y hP22b_Y (Ne.symm hP22a_ne_P12a) hP22_ne (Ne.symm hP22b_ne_P12a) ⟨by simp [hP12a_red, hcY], by simp [hP22a_red, hcY], by simp [hP22b_red, hcY]⟩
          · by_contra h
            push_neg at h
            have hP22a_red : c P22a = true := by cases hc' : c P22a <;> simp_all
            have hP22b_red : c P22b = true := by cases hc' : c P22b <;> simp_all
            exact at_most_two_opposite c hc Y s₂ hs2_pos P12b P22a P22b hP12b_Y hP22a_Y hP22b_Y (Ne.symm hP22a_ne_P12b) hP22_ne (Ne.symm hP22b_ne_P12b) ⟨by simp [hP12b_red, hcY], by simp [hP22a_red, hcY], by simp [hP22b_red, hcY]⟩

        -- P₂ has P21a, P21b green, plus one of P22a, P22b green
        rcases hP22_one_green with hP22a_green | hP22b_green
        · exact at_most_two_opposite c hc X r₂ hr2_pos P21a P21b P22a hP21a_X hP21b_X hP22a_X hP21_ne hP21b_ne_P22a hP21a_ne_P22a ⟨by simp [hP21a_green, hcX], by simp [hP21b_green, hcX], by simp [hP22a_green, hcX]⟩
        · exact at_most_two_opposite c hc X r₂ hr2_pos P21a P21b P22b hP21a_X hP21b_X hP22b_X hP21_ne hP21b_ne_P22b hP21a_ne_P22b ⟨by simp [hP21a_green, hcX], by simp [hP21b_green, hcX], by simp [hP22b_green, hcX]⟩

  · -- Case: g₂ = 0 (P12a, P12b all-red)
    have hP12a_red : c P12a = true := by simp only [hg2_def] at hg2_zero; split_ifs at hg2_zero; all_goals first | omega | (cases hb : c _ <;> simp_all)
    have hP12b_red : c P12b = true := by simp only [hg2_def] at hg2_zero; split_ifs at hg2_zero; all_goals first | omega | (cases hb : c _ <;> simp_all)

    have hP22a_green : c P22a = false := by
      by_contra h
      have hP22a_red : c P22a = true := by cases hc' : c P22a <;> simp_all
      exact at_most_two_opposite c hc Y s₂ hs2_pos P12a P12b P22a hP12a_Y hP12b_Y hP22a_Y hP12_ne (Ne.symm hP22a_ne_P12b) (Ne.symm hP22a_ne_P12a) ⟨by simp [hP12a_red, hcY], by simp [hP12b_red, hcY], by simp [hP22a_red, hcY]⟩

    have hP22b_green : c P22b = false := by
      by_contra h
      have hP22b_red : c P22b = true := by cases hc' : c P22b <;> simp_all
      exact at_most_two_opposite c hc Y s₂ hs2_pos P12a P12b P22b hP12a_Y hP12b_Y hP22b_Y hP12_ne (Ne.symm hP22b_ne_P12b) (Ne.symm hP22b_ne_P12a) ⟨by simp [hP12a_red, hcY], by simp [hP12b_red, hcY], by simp [hP22b_red, hcY]⟩

    by_cases hg1_zero' : g₁ = 0
    · have hP11a_red : c P11a = true := by simp only [hg1_def] at hg1_zero'; split_ifs at hg1_zero'; all_goals first | omega | (cases hb : c _ <;> simp_all)

      have hP21a_green : c P21a = false := by
        by_contra h
        have hP11b_red : c P11b = true := by simp only [hg1_def] at hg1_zero'; split_ifs at hg1_zero'; all_goals first | omega | (cases hb : c _ <;> simp_all)
        have hP21a_red : c P21a = true := by cases hc' : c P21a <;> simp_all
        exact at_most_two_opposite c hc Y s₁ hs1_pos P11a P11b P21a hP11a_Y hP11b_Y hP21a_Y hP11_ne (Ne.symm hP21a_ne_P11b) (Ne.symm hP21a_ne_P11a) ⟨by simp [hP11a_red, hcY], by simp [hP11b_red, hcY], by simp [hP21a_red, hcY]⟩

      exact at_most_two_opposite c hc X r₂ hr2_pos P21a P22a P22b hP21a_X hP22a_X hP22b_X hP21a_ne_P22a hP22_ne hP21a_ne_P22b ⟨by simp [hP21a_green, hcX], by simp [hP22a_green, hcX], by simp [hP22b_green, hcX]⟩

    · by_cases hg3_zero' : g₃ = 0
      · have hsum_23 : r₂ + s₃ > d := by simp only [hr2_def, hs3_def]; linarith
        have hdiff_23 : |r₂ - s₃| < d := by simp only [hr2_def, hs3_def]; rw [abs_sub_lt_iff]; constructor <;> linarith

        obtain ⟨P23a, _, _, hP23a_X, hP23a_Y, _, _⟩ :=
          two_circles_intersect X Y r₂ s₃ d hr2_pos hs3_pos hd_pos hdist hsum_23 hdiff_23

        have hP13a_red : c P13a = true := by simp only [hg3_def] at hg3_zero'; split_ifs at hg3_zero'; all_goals first | omega | (cases hb : c _ <;> simp_all)
        have hP13b_red : c P13b = true := by simp only [hg3_def] at hg3_zero'; split_ifs at hg3_zero'; all_goals first | omega | (cases hb : c _ <;> simp_all)

        have hP23a_ne_P13a : P23a ≠ P13a := fun h => diff_radius_diff_point X r₂ r₁ hr2_pos hr1_pos (Ne.symm hr12) P13a (h ▸ hP23a_X) hP13a_X
        have hP23a_ne_P13b : P23a ≠ P13b := fun h => diff_radius_diff_point X r₂ r₁ hr2_pos hr1_pos (Ne.symm hr12) P13b (h ▸ hP23a_X) hP13b_X

        have hP23a_green : c P23a = false := by
          by_contra h
          have hP23a_red : c P23a = true := by cases hc' : c P23a <;> simp_all
          exact at_most_two_opposite c hc Y s₃ hs3_pos P13a P13b P23a hP13a_Y hP13b_Y hP23a_Y hP13_ne (Ne.symm hP23a_ne_P13b) (Ne.symm hP23a_ne_P13a) ⟨by simp [hP13a_red, hcY], by simp [hP13b_red, hcY], by simp [hP23a_red, hcY]⟩

        have hP22a_ne_P23a : P22a ≠ P23a := fun h => diff_radius_diff_point Y s₂ s₃ hs2_pos hs3_pos hs23 P23a (h ▸ hP22a_Y) hP23a_Y

        exact at_most_two_opposite c hc X r₂ hr2_pos P22a P22b P23a hP22a_X hP22b_X hP23a_X hP22_ne (fun h => diff_radius_diff_point Y s₂ s₃ hs2_pos hs3_pos hs23 P23a (h ▸ hP22b_Y) hP23a_Y) hP22a_ne_P23a ⟨by simp [hP22a_green, hcX], by simp [hP22b_green, hcX], by simp [hP23a_green, hcX]⟩

      · -- g₁ ≥ 1, g₃ ≥ 1, g₂ = 0, g₁ + g₃ ≤ 2 => g₁ = g₃ = 1
        have hg1_eq1 : g₁ = 1 := by omega
        have hP11_one_red : (c P11a = true ∧ c P11b = false) ∨ (c P11a = false ∧ c P11b = true) := by
          simp only [hg1_def] at hg1_eq1
          cases hb0 : c P11a <;> cases hb1 : c P11b <;> simp_all

        have hP21_one_green : c P21a = false ∨ c P21b = false := by
          rcases hP11_one_red with ⟨hP11a_red, _⟩ | ⟨_, hP11b_red⟩
          · by_contra h
            push_neg at h
            have hP21a_red : c P21a = true := by cases hc' : c P21a <;> simp_all
            have hP21b_red : c P21b = true := by cases hc' : c P21b <;> simp_all
            exact at_most_two_opposite c hc Y s₁ hs1_pos P11a P21a P21b hP11a_Y hP21a_Y hP21b_Y (Ne.symm hP21a_ne_P11a) hP21_ne (Ne.symm hP21b_ne_P11a) ⟨by simp [hP11a_red, hcY], by simp [hP21a_red, hcY], by simp [hP21b_red, hcY]⟩
          · by_contra h
            push_neg at h
            have hP21a_red : c P21a = true := by cases hc' : c P21a <;> simp_all
            have hP21b_red : c P21b = true := by cases hc' : c P21b <;> simp_all
            exact at_most_two_opposite c hc Y s₁ hs1_pos P11b P21a P21b hP11b_Y hP21a_Y hP21b_Y (Ne.symm hP21a_ne_P11b) hP21_ne (Ne.symm hP21b_ne_P11b) ⟨by simp [hP11b_red, hcY], by simp [hP21a_red, hcY], by simp [hP21b_red, hcY]⟩

        rcases hP21_one_green with hP21a_green | hP21b_green
        · exact at_most_two_opposite c hc X r₂ hr2_pos P21a P22a P22b hP21a_X hP22a_X hP22b_X hP21a_ne_P22a hP22_ne hP21a_ne_P22b ⟨by simp [hP21a_green, hcX], by simp [hP22a_green, hcX], by simp [hP22b_green, hcX]⟩
        · exact at_most_two_opposite c hc X r₂ hr2_pos P21b P22a P22b hP21b_X hP22a_X hP22b_X hP21b_ne_P22a hP22_ne hP21b_ne_P22b ⟨by simp [hP21b_green, hcX], by simp [hP22a_green, hcX], by simp [hP22b_green, hcX]⟩

  · -- Case: g₃ = 0 (P13a, P13b all-red)
    have hP13a_red : c P13a = true := by simp only [hg3_def] at hg3_zero; split_ifs at hg3_zero; all_goals first | omega | (cases hb : c _ <;> simp_all)
    have hP13b_red : c P13b = true := by simp only [hg3_def] at hg3_zero; split_ifs at hg3_zero; all_goals first | omega | (cases hb : c _ <;> simp_all)

    have hsum_23 : r₂ + s₃ > d := by simp only [hr2_def, hs3_def]; linarith
    have hdiff_23 : |r₂ - s₃| < d := by simp only [hr2_def, hs3_def]; rw [abs_sub_lt_iff]; constructor <;> linarith

    obtain ⟨P23a, P23b, hP23_ne, hP23a_X, hP23a_Y, hP23b_X, hP23b_Y⟩ :=
      two_circles_intersect X Y r₂ s₃ d hr2_pos hs3_pos hd_pos hdist hsum_23 hdiff_23

    have hP23a_ne_P13a : P23a ≠ P13a := fun h => diff_radius_diff_point X r₂ r₁ hr2_pos hr1_pos (Ne.symm hr12) P13a (h ▸ hP23a_X) hP13a_X
    have hP23a_ne_P13b : P23a ≠ P13b := fun h => diff_radius_diff_point X r₂ r₁ hr2_pos hr1_pos (Ne.symm hr12) P13b (h ▸ hP23a_X) hP13b_X
    have hP23b_ne_P13a : P23b ≠ P13a := fun h => diff_radius_diff_point X r₂ r₁ hr2_pos hr1_pos (Ne.symm hr12) P13a (h ▸ hP23b_X) hP13a_X
    have hP23b_ne_P13b : P23b ≠ P13b := fun h => diff_radius_diff_point X r₂ r₁ hr2_pos hr1_pos (Ne.symm hr12) P13b (h ▸ hP23b_X) hP13b_X

    have hP23a_green : c P23a = false := by
      by_contra h
      have hP23a_red : c P23a = true := by cases hc' : c P23a <;> simp_all
      exact at_most_two_opposite c hc Y s₃ hs3_pos P13a P13b P23a hP13a_Y hP13b_Y hP23a_Y hP13_ne (Ne.symm hP23a_ne_P13b) (Ne.symm hP23a_ne_P13a) ⟨by simp [hP13a_red, hcY], by simp [hP13b_red, hcY], by simp [hP23a_red, hcY]⟩

    have hP23b_green : c P23b = false := by
      by_contra h
      have hP23b_red : c P23b = true := by cases hc' : c P23b <;> simp_all
      exact at_most_two_opposite c hc Y s₃ hs3_pos P13a P13b P23b hP13a_Y hP13b_Y hP23b_Y hP13_ne (Ne.symm hP23b_ne_P13b) (Ne.symm hP23b_ne_P13a) ⟨by simp [hP13a_red, hcY], by simp [hP13b_red, hcY], by simp [hP23b_red, hcY]⟩

    by_cases hg1_zero' : g₁ = 0
    · have hP11a_red : c P11a = true := by simp only [hg1_def] at hg1_zero'; split_ifs at hg1_zero'; all_goals first | omega | (cases hb : c _ <;> simp_all)
      have hP11b_red : c P11b = true := by simp only [hg1_def] at hg1_zero'; split_ifs at hg1_zero'; all_goals first | omega | (cases hb : c _ <;> simp_all)

      have hP21a_green : c P21a = false := by
        by_contra h
        have hP21a_red : c P21a = true := by cases hc' : c P21a <;> simp_all
        exact at_most_two_opposite c hc Y s₁ hs1_pos P11a P11b P21a hP11a_Y hP11b_Y hP21a_Y hP11_ne (Ne.symm hP21a_ne_P11b) (Ne.symm hP21a_ne_P11a) ⟨by simp [hP11a_red, hcY], by simp [hP11b_red, hcY], by simp [hP21a_red, hcY]⟩

      have hP21a_ne_P23a : P21a ≠ P23a := fun h => diff_radius_diff_point Y s₁ s₃ hs1_pos hs3_pos hs13 P23a (h ▸ hP21a_Y) hP23a_Y
      have hP21a_ne_P23b : P21a ≠ P23b := fun h => diff_radius_diff_point Y s₁ s₃ hs1_pos hs3_pos hs13 P23b (h ▸ hP21a_Y) hP23b_Y

      exact at_most_two_opposite c hc X r₂ hr2_pos P21a P23a P23b hP21a_X hP23a_X hP23b_X hP21a_ne_P23a hP23_ne hP21a_ne_P23b ⟨by simp [hP21a_green, hcX], by simp [hP23a_green, hcX], by simp [hP23b_green, hcX]⟩

    · by_cases hg2_zero' : g₂ = 0
      · have hP12a_red : c P12a = true := by simp only [hg2_def] at hg2_zero'; split_ifs at hg2_zero'; all_goals first | omega | (cases hb : c _ <;> simp_all)

        have hP22a_green : c P22a = false := by
          by_contra h
          have hP12b_red : c P12b = true := by simp only [hg2_def] at hg2_zero'; split_ifs at hg2_zero'; all_goals first | omega | (cases hb : c _ <;> simp_all)
          have hP22a_red : c P22a = true := by cases hc' : c P22a <;> simp_all
          exact at_most_two_opposite c hc Y s₂ hs2_pos P12a P12b P22a hP12a_Y hP12b_Y hP22a_Y hP12_ne (Ne.symm hP22a_ne_P12b) (Ne.symm hP22a_ne_P12a) ⟨by simp [hP12a_red, hcY], by simp [hP12b_red, hcY], by simp [hP22a_red, hcY]⟩

        have hP22a_ne_P23a : P22a ≠ P23a := fun h => diff_radius_diff_point Y s₂ s₃ hs2_pos hs3_pos hs23 P23a (h ▸ hP22a_Y) hP23a_Y
        have hP22a_ne_P23b : P22a ≠ P23b := fun h => diff_radius_diff_point Y s₂ s₃ hs2_pos hs3_pos hs23 P23b (h ▸ hP22a_Y) hP23b_Y

        exact at_most_two_opposite c hc X r₂ hr2_pos P22a P23a P23b hP22a_X hP23a_X hP23b_X hP22a_ne_P23a hP23_ne hP22a_ne_P23b ⟨by simp [hP22a_green, hcX], by simp [hP23a_green, hcX], by simp [hP23b_green, hcX]⟩

      · -- g₁ ≥ 1, g₂ ≥ 1, g₃ = 0 => g₁ = g₂ = 1
        have hg1_eq1 : g₁ = 1 := by omega
        have hP11_one_red : (c P11a = true ∧ c P11b = false) ∨ (c P11a = false ∧ c P11b = true) := by
          simp only [hg1_def] at hg1_eq1
          cases hb0 : c P11a <;> cases hb1 : c P11b <;> simp_all

        have hP21_one_green : c P21a = false ∨ c P21b = false := by
          rcases hP11_one_red with ⟨hP11a_red, _⟩ | ⟨_, hP11b_red⟩
          · by_contra h
            push_neg at h
            have hP21a_red : c P21a = true := by cases hc' : c P21a <;> simp_all
            have hP21b_red : c P21b = true := by cases hc' : c P21b <;> simp_all
            exact at_most_two_opposite c hc Y s₁ hs1_pos P11a P21a P21b hP11a_Y hP21a_Y hP21b_Y (Ne.symm hP21a_ne_P11a) hP21_ne (Ne.symm hP21b_ne_P11a) ⟨by simp [hP11a_red, hcY], by simp [hP21a_red, hcY], by simp [hP21b_red, hcY]⟩
          · by_contra h
            push_neg at h
            have hP21a_red : c P21a = true := by cases hc' : c P21a <;> simp_all
            have hP21b_red : c P21b = true := by cases hc' : c P21b <;> simp_all
            exact at_most_two_opposite c hc Y s₁ hs1_pos P11b P21a P21b hP11b_Y hP21a_Y hP21b_Y (Ne.symm hP21a_ne_P11b) hP21_ne (Ne.symm hP21b_ne_P11b) ⟨by simp [hP11b_red, hcY], by simp [hP21a_red, hcY], by simp [hP21b_red, hcY]⟩

        have hP21a_ne_P23a : P21a ≠ P23a := fun h => diff_radius_diff_point Y s₁ s₃ hs1_pos hs3_pos hs13 P23a (h ▸ hP21a_Y) hP23a_Y
        have hP21a_ne_P23b : P21a ≠ P23b := fun h => diff_radius_diff_point Y s₁ s₃ hs1_pos hs3_pos hs13 P23b (h ▸ hP21a_Y) hP23b_Y
        have hP21b_ne_P23a : P21b ≠ P23a := fun h => diff_radius_diff_point Y s₁ s₃ hs1_pos hs3_pos hs13 P23a (h ▸ hP21b_Y) hP23a_Y
        have hP21b_ne_P23b : P21b ≠ P23b := fun h => diff_radius_diff_point Y s₁ s₃ hs1_pos hs3_pos hs13 P23b (h ▸ hP21b_Y) hP23b_Y

        rcases hP21_one_green with hP21a_green | hP21b_green
        · exact at_most_two_opposite c hc X r₂ hr2_pos P21a P23a P23b hP21a_X hP23a_X hP23b_X hP21a_ne_P23a hP23_ne hP21a_ne_P23b ⟨by simp [hP21a_green, hcX], by simp [hP23a_green, hcX], by simp [hP23b_green, hcX]⟩
        · exact at_most_two_opposite c hc X r₂ hr2_pos P21b P23a P23b hP21b_X hP23a_X hP23b_X hP21b_ne_P23a hP23_ne hP21b_ne_P23b ⟨by simp [hP21b_green, hcX], by simp [hP23a_green, hcX], by simp [hP23b_green, hcX]⟩

/-! ## Main Theorem -/

theorem putnam_2025_B1 (c : Coloring) (hc : ColoringCondition c) :
    (∀ p : Point, c p = true) ∨ (∀ p : Point, c p = false) := by
  by_contra h
  push_neg at h
  obtain ⟨⟨Y, hY⟩, ⟨X, hX⟩⟩ := h
  have hcX : c X = true := by cases h : c X <;> simp_all
  have hcY : c Y = false := by cases h : c Y <;> simp_all
  have hXY : X ≠ Y := fun heq => by rw [heq] at hcX; simp_all
  exact no_opposite_colors c hc X Y hXY hcX hcY

end Putnam2025B1
