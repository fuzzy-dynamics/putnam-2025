/-
Putnam 2025 Problem A2

Find the largest real number a and the smallest real number b such that
for all x ∈ [0, π], we have ax(π-x) ≤ sin(x) ≤ bx(π-x).

Answer: a = 1/π, b = 4/π²
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

set_option maxHeartbeats 400000

open Real Set

-- ============================================================================
-- LOWER BOUND: sin(x) ≥ x(π-x)/π for x ∈ [0, π]
-- ============================================================================

namespace PutnamA2Lower

-- Basic bounds about π
lemma two_div_pi_pos : (0 : ℝ) < 2 / π := by positivity

lemma two_div_pi_lt_one : (2 : ℝ) / π < 1 := by
  have hp : π > 0 := pi_pos
  have h3 : π > 3 := pi_gt_three
  rw [div_lt_one hp]; linarith

lemma two_div_pi_le_one : (2 : ℝ) / π ≤ 1 := le_of_lt two_div_pi_lt_one

lemma neg_one_le_two_div_pi : (-1 : ℝ) ≤ 2 / π := by linarith [two_div_pi_pos]

lemma arcsin_two_div_pi_nonneg : 0 ≤ arcsin (2 / π) := by
  rw [arcsin_nonneg]; exact le_of_lt two_div_pi_pos

lemma arcsin_two_div_pi_pos : 0 < arcsin (2 / π) := by
  rw [arcsin_pos]; exact two_div_pi_pos

lemma arcsin_two_div_pi_le_pi_div_two : arcsin (2 / π) ≤ π / 2 :=
  arcsin_le_pi_div_two (2 / π)

lemma arcsin_two_div_pi_lt_pi_div_two : arcsin (2 / π) < π / 2 := by
  rw [arcsin_lt_pi_div_two]; exact two_div_pi_lt_one

-- Auxiliary function g(x) = cos(x) - 1 + 2x/π
noncomputable def g (x : ℝ) : ℝ := cos x - 1 + 2 * x / π

lemma g_zero : g 0 = 0 := by simp [g, cos_zero]

lemma g_pi_div_two : g (π / 2) = 0 := by
  simp only [g, cos_pi_div_two]
  have hp : π ≠ 0 := ne_of_gt pi_pos
  field_simp; ring

lemma g_continuous : Continuous g := by unfold g; continuity

lemma g_hasDerivAt (x : ℝ) : HasDerivAt g (-sin x + 2 / π) x := by
  have hp : π ≠ 0 := ne_of_gt pi_pos
  unfold g
  have h1 : HasDerivAt (fun y => cos y) (-sin x) x := hasDerivAt_cos x
  have h2 : HasDerivAt (fun _ => (1 : ℝ)) 0 x := hasDerivAt_const x 1
  have h3 : HasDerivAt (fun y => 2 * y / π) (2 / π) x := by
    have : HasDerivAt (fun y => y * (2 / π)) (1 * (2 / π)) x := (hasDerivAt_id x).mul_const _
    simp only [one_mul] at this; convert this using 2; ring
  have := (h1.sub h2).add h3; convert this using 1; ring

lemma g_deriv (x : ℝ) : deriv g x = -sin x + 2 / π := (g_hasDerivAt x).deriv

-- Monotonicity of g
lemma sin_lt_two_div_pi_on_small (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < arcsin (2 / π)) :
    sin x < 2 / π := by
  have h_neg_pi_half : -(π / 2) ≤ x := by linarith [pi_pos]
  have h_le_pi_half : arcsin (2 / π) ≤ π / 2 := arcsin_two_div_pi_le_pi_div_two
  have := sin_lt_sin_of_lt_of_le_pi_div_two h_neg_pi_half h_le_pi_half hx1
  rw [sin_arcsin neg_one_le_two_div_pi two_div_pi_le_one] at this
  exact this

lemma g_deriv_pos_on_small (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < arcsin (2 / π)) :
    deriv g x > 0 := by
  rw [g_deriv]
  have h1 := sin_lt_two_div_pi_on_small x hx0 hx1
  linarith

lemma sin_gt_two_div_pi_on_large (x : ℝ) (hx0 : arcsin (2 / π) < x) (hx1 : x ≤ π / 2) :
    sin x > 2 / π := by
  have h_neg_pi_half : -(π / 2) ≤ arcsin (2 / π) := by
    have := arcsin_two_div_pi_nonneg; linarith [pi_pos]
  have := sin_lt_sin_of_lt_of_le_pi_div_two h_neg_pi_half hx1 hx0
  rw [sin_arcsin neg_one_le_two_div_pi two_div_pi_le_one] at this
  exact this

lemma g_deriv_neg_on_large (x : ℝ) (hx0 : arcsin (2 / π) < x) (hx1 : x ≤ π / 2) :
    deriv g x < 0 := by
  rw [g_deriv]
  have h1 := sin_gt_two_div_pi_on_large x hx0 hx1
  linarith

lemma g_strictMonoOn_left : StrictMonoOn g (Icc 0 (arcsin (2 / π))) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 (arcsin (2 / π)))
  · exact g_continuous.continuousOn
  · intro x hx
    simp only [interior_Icc, mem_Ioo] at hx
    exact g_deriv_pos_on_small x (le_of_lt hx.1) hx.2

lemma g_strictAntiOn_right : StrictAntiOn g (Icc (arcsin (2 / π)) (π / 2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc (arcsin (2 / π)) (π / 2))
  · exact g_continuous.continuousOn
  · intro x hx
    simp only [interior_Icc, mem_Ioo] at hx
    exact g_deriv_neg_on_large x hx.1 (le_of_lt hx.2)

-- g ≥ 0 on [0, π/2]
lemma g_nonneg_on_first_half (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ π / 2) : g x ≥ 0 := by
  by_cases hx_eq_zero : x = 0
  · rw [hx_eq_zero, g_zero]
  by_cases hx_eq_pi_half : x = π / 2
  · rw [hx_eq_pi_half, g_pi_div_two]

  have hx_pos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx_eq_zero)
  have hx_lt_pi_half : x < π / 2 := lt_of_le_of_ne hx1 hx_eq_pi_half

  by_cases h_left : x ≤ arcsin (2 / π)
  · have hx_mem : x ∈ Icc 0 (arcsin (2 / π)) := ⟨hx0, h_left⟩
    have h0_mem : (0 : ℝ) ∈ Icc 0 (arcsin (2 / π)) := ⟨le_refl 0, arcsin_two_div_pi_nonneg⟩
    have := g_strictMonoOn_left h0_mem hx_mem hx_pos
    rw [g_zero] at this
    linarith
  · push_neg at h_left
    have hx_mem : x ∈ Icc (arcsin (2 / π)) (π / 2) := ⟨le_of_lt h_left, hx1⟩
    have hpi_mem : (π / 2) ∈ Icc (arcsin (2 / π)) (π / 2) :=
      ⟨arcsin_two_div_pi_le_pi_div_two, le_refl _⟩
    have := g_strictAntiOn_right hx_mem hpi_mem hx_lt_pi_half
    rw [g_pi_div_two] at this
    linarith

-- cos(x) ≥ 1 - 2x/π on [0, π/2]
theorem cos_ge_linear_on_first_half (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ π / 2) :
    cos x ≥ 1 - 2 * x / π := by
  have h := g_nonneg_on_first_half x hx0 hx1
  unfold g at h
  linarith

-- Now prove sin x ≥ x(π-x)/π on [0, π/2]
noncomputable def h (x : ℝ) : ℝ := sin x - x + x^2 / π

lemma h_eq (x : ℝ) : h x = sin x - x * (π - x) / π := by
  unfold h
  have hp : π ≠ 0 := ne_of_gt pi_pos
  field_simp
  ring

lemma h_zero : h 0 = 0 := by simp [h, sin_zero]

lemma h_continuous : Continuous h := by unfold h; continuity

lemma h_differentiable : Differentiable ℝ h := by unfold h; fun_prop

lemma h_hasDerivAt (x : ℝ) : HasDerivAt h (cos x - 1 + 2 * x / π) x := by
  have hp : π ≠ 0 := ne_of_gt pi_pos
  unfold h
  have h1 : HasDerivAt sin (cos x) x := hasDerivAt_sin x
  have h2 : HasDerivAt (fun y => y) 1 x := hasDerivAt_id x
  have h3 : HasDerivAt (fun y => y^2 / π) (2 * x / π) x := by
    have hpow : HasDerivAt (fun y => y^2) (2 * x) x := by
      have := hasDerivAt_pow 2 x
      norm_cast at this
      simp only [Nat.add_one_sub_one, pow_one] at this
      exact this
    exact hpow.div_const π
  exact (h1.sub h2).add h3

lemma h_deriv (x : ℝ) : deriv h x = cos x - 1 + 2 * x / π := (h_hasDerivAt x).deriv

lemma h_deriv_nonneg (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ π / 2) : deriv h x ≥ 0 := by
  rw [h_deriv]
  have hg := g_nonneg_on_first_half x hx0 hx1
  unfold g at hg
  linarith

lemma h_monotoneOn : MonotoneOn h (Icc 0 (π / 2)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (π / 2))
  · exact h_continuous.continuousOn
  · intro x _
    exact h_differentiable.differentiableAt.differentiableWithinAt
  · intro x hx
    simp only [interior_Icc, mem_Ioo] at hx
    have := h_deriv_nonneg x (le_of_lt hx.1) (le_of_lt hx.2)
    linarith

lemma h_nonneg_on_first_half (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ π / 2) : h x ≥ 0 := by
  have hx_mem : x ∈ Icc 0 (π / 2) := ⟨hx0, hx1⟩
  have h0_mem : (0 : ℝ) ∈ Icc 0 (π / 2) := ⟨le_refl 0, by linarith [pi_pos]⟩
  have := h_monotoneOn h0_mem hx_mem hx0
  rw [h_zero] at this
  exact this

theorem sin_ge_quadratic_on_first_half (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ π / 2) :
    sin x ≥ x * (π - x) / π := by
  have h := h_nonneg_on_first_half x hx0 hx1
  rw [h_eq] at h
  linarith

-- Extend to [0, π] by symmetry
theorem sin_ge_quadratic_on_full (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ π) :
    sin x ≥ x * (π - x) / π := by
  by_cases h : x ≤ π / 2
  · exact sin_ge_quadratic_on_first_half x hx0 h
  · push_neg at h
    have hx_symm_nonneg : 0 ≤ π - x := by linarith
    have hx_symm_le : π - x ≤ π / 2 := by linarith
    have h_sin_symm : sin x = sin (π - x) := (sin_pi_sub x).symm
    have h_quad_symm : x * (π - x) = (π - x) * (π - (π - x)) := by ring
    rw [h_sin_symm, h_quad_symm]
    exact sin_ge_quadratic_on_first_half (π - x) hx_symm_nonneg hx_symm_le

end PutnamA2Lower

-- ============================================================================
-- UPPER BOUND: sin(x) ≤ 4x(π-x)/π² for x ∈ [0, π]
-- ============================================================================

namespace PutnamA2Upper

noncomputable def f (y : ℝ) : ℝ := 1 - 4 * y^2 / π^2 - cos y

lemma f_zero : f 0 = 0 := by simp [f, cos_zero]

lemma f_pi_div_two : f (π / 2) = 0 := by
  simp only [f, cos_pi_div_two]
  have hp : π ≠ 0 := ne_of_gt pi_pos
  field_simp
  ring

lemma f_continuous : Continuous f := by unfold f; continuity

lemma f_differentiable : Differentiable ℝ f := by unfold f; fun_prop

lemma f_hasDerivAt (y : ℝ) : HasDerivAt f (sin y - 8 * y / π^2) y := by
  have hp : π ≠ 0 := ne_of_gt pi_pos
  unfold f
  have h1 : HasDerivAt (fun _ => (1 : ℝ)) 0 y := hasDerivAt_const y 1
  have h2 : HasDerivAt (fun z => 4 * z^2 / π^2) (8 * y / π^2) y := by
    have hpow : HasDerivAt (fun z => z^2) (2 * y) y := by
      have := hasDerivAt_pow 2 y
      norm_cast at this
      simp only [Nat.add_one_sub_one, pow_one] at this
      exact this
    have := (hpow.const_mul 4).div_const (π^2)
    convert this using 1
    ring
  have h3 : HasDerivAt cos (-sin y) y := hasDerivAt_cos y
  have h12 := h1.sub h2
  have := h12.sub h3
  convert this using 1
  ring

lemma f_deriv (y : ℝ) : deriv f y = sin y - 8 * y / π^2 := (f_hasDerivAt y).deriv

lemma four_div_pi_gt_one : (4 : ℝ) / π > 1 := by
  have hp : π > 0 := pi_pos
  have h4 : π < 4 := pi_lt_four
  have h2 : π⁻¹ > 0 := inv_pos_of_pos hp
  have h3 : 1 < 4 * π⁻¹ := by
    have hstep : π * π⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hp)
    calc 1 = π * π⁻¹ := hstep.symm
      _ < 4 * π⁻¹ := by nlinarith
  rw [div_eq_mul_inv]
  exact h3

lemma f_deriv_neg_at_pi_div_two : deriv f (π / 2) < 0 := by
  rw [f_deriv, sin_pi_div_two]
  have hp : π > 0 := pi_pos
  have hsimp : 8 * (π / 2) / π^2 = 4 / π := by field_simp; ring
  rw [hsimp]
  have h1 := four_div_pi_gt_one
  linarith

lemma f_deriv_continuous : Continuous (deriv f) := by
  have h : deriv f = fun y => sin y - 8 * y / π^2 := funext f_deriv
  rw [h]
  continuity

lemma f_deriv_pos_for_small (y : ℝ) (hy_pos : 0 < y) (hy_le_one : y ≤ 1)
    (hy_sq : y^2 < 4 - 32 / π^2) : deriv f y > 0 := by
  rw [f_deriv]
  have h_sin_lb : y - y^3 / 4 < sin y := sin_gt_sub_cube hy_pos hy_le_one
  have hp : π > 0 := pi_pos
  have hpp : π > 3 := pi_gt_three
  have hpp2 : π^2 > 0 := by positivity
  have hpi_sq : π^2 > 9 := by nlinarith [sq_nonneg π]
  have h1 : y^2 / 4 < 1 - 8 / π^2 := by
    have h : y^2 < 4 - 32 / π^2 := hy_sq
    have h' : y^2 / 4 < (4 - 32 / π^2) / 4 := by linarith
    have h'' : (4 - 32 / π^2) / 4 = 1 - 8 / π^2 := by field_simp; ring
    linarith
  have h2 : 1 - y^2 / 4 > 8 / π^2 := by linarith
  have h3 : y * (1 - y^2 / 4) > y * (8 / π^2) := by nlinarith
  have h4 : y * (1 - y^2 / 4) = y - y^3 / 4 := by ring
  have h5 : y * (8 / π^2) = 8 * y / π^2 := by ring
  have h6 : sin y > 8 * y / π^2 := by
    calc sin y > y - y^3 / 4 := h_sin_lb
      _ = y * (1 - y^2/4) := h4.symm
      _ > y * (8 / π^2) := h3
      _ = 8 * y / π^2 := h5
  linarith

lemma four_minus_32_div_pi_sq_gt : 4 - 32 / π^2 > 0.4 := by
  have hp : π > 3 := pi_gt_three
  have hpp : π > 0 := pi_pos
  have hpi_sq : π^2 > 9 := by nlinarith [sq_nonneg π]
  have h1 : 32 / π^2 < 32 / 9 := by
    apply div_lt_div_of_pos_left
    · norm_num
    · norm_num
    · exact hpi_sq
  have h2 : (32 : ℝ) / 9 < 3.6 := by norm_num
  linarith

lemma f_deriv_pos_on_small_interval (y : ℝ) (hy : y ∈ Ioo 0 0.6) : deriv f y > 0 := by
  have hy_pos : 0 < y := hy.1
  have hy_lt : y < 0.6 := hy.2
  have hy_le_one : y ≤ 1 := by linarith
  have hy_sq : y^2 < 0.36 := by nlinarith
  have hbound : (0.36 : ℝ) < 4 - 32 / π^2 := by
    have := four_minus_32_div_pi_sq_gt
    linarith
  have hy_sq' : y^2 < 4 - 32 / π^2 := by linarith
  exact f_deriv_pos_for_small y hy_pos hy_le_one hy_sq'

lemma f_strictMonoOn_left : StrictMonoOn f (Icc 0 0.6) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 0.6)
  · exact f_continuous.continuousOn
  · intro x hx
    simp only [interior_Icc, mem_Ioo] at hx
    exact f_deriv_pos_on_small_interval x hx

lemma f_pos_on_small (y : ℝ) (hy : y ∈ Ioc 0 0.6) : f y > 0 := by
  have h0_mem : (0 : ℝ) ∈ Icc 0 0.6 := ⟨le_refl 0, by norm_num⟩
  have hy_mem : y ∈ Icc 0 0.6 := ⟨le_of_lt hy.1, hy.2⟩
  have hmono := f_strictMonoOn_left h0_mem hy_mem hy.1
  rw [f_zero] at hmono
  exact hmono

lemma f_deriv_neg_near_pi_div_two : ∃ ε > 0, ε < π/2 ∧ ∀ y ∈ Ioo (π/2 - ε) (π/2), deriv f y < 0 := by
  have hcont := f_deriv_continuous
  have hneg := f_deriv_neg_at_pi_div_two
  have hopen : Iio 0 ∈ nhds (deriv f (π/2)) := by
    rw [mem_nhds_iff]
    use Iio 0
    exact ⟨subset_refl _, isOpen_Iio, hneg⟩
  have hpreimage := hcont.isOpen_preimage (Iio 0) isOpen_Iio
  rw [Metric.isOpen_iff] at hpreimage
  have hmem : π/2 ∈ deriv f ⁻¹' Iio 0 := hneg
  obtain ⟨δ, hδ_pos, hball⟩ := hpreimage (π/2) hmem
  use min δ (π/4)
  constructor
  · exact lt_min hδ_pos (by positivity)
  constructor
  · calc min δ (π/4) ≤ π/4 := min_le_right _ _
      _ < π/2 := by linarith [pi_pos]
  · intro y hy
    have hy_in_ball : y ∈ Metric.ball (π/2) δ := by
      rw [Metric.mem_ball, Real.dist_eq]
      have h1 : y > π/2 - min δ (π/4) := hy.1
      have h2 : y < π/2 := hy.2
      have hmin : min δ (π/4) ≤ δ := min_le_left _ _
      calc |y - π/2| = π/2 - y := by
            rw [abs_sub_comm, abs_of_nonneg]; linarith
        _ < min δ (π/4) := by linarith
        _ ≤ δ := hmin
    exact hball hy_in_ball

lemma f_pos_on_right : ∃ ε > 0, ε < π/2 ∧ ∀ y ∈ Ico (π/2 - ε) (π/2), f y > 0 := by
  obtain ⟨ε, hε_pos, hε_lt, hderiv_neg⟩ := f_deriv_neg_near_pi_div_two
  use ε, hε_pos, hε_lt
  intro y hy
  have hanti : StrictAntiOn f (Icc (π/2 - ε) (π/2)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc (π/2 - ε) (π/2))
    · exact f_continuous.continuousOn
    · intro x hx
      simp only [interior_Icc, mem_Ioo] at hx
      exact hderiv_neg x hx
  have hy_mem : y ∈ Icc (π/2 - ε) (π/2) := ⟨hy.1, le_of_lt hy.2⟩
  have hpi_mem : (π/2) ∈ Icc (π/2 - ε) (π/2) := ⟨by linarith, le_refl _⟩
  have := hanti hy_mem hpi_mem hy.2
  rw [f_pi_div_two] at this
  linarith

-- cos(1) < 1 - 4/π² (needed for middle interval)
lemma cos_one_bound : cos 1 < (1 : ℝ) - 4/π^2 := by
  have h_cos_ub : cos 1 ≤ 53/96 := by
    have hb := cos_bound (x := (1 : ℝ)) (by simp : |(1 : ℝ)| ≤ 1)
    simp only [one_pow, abs_one, one_mul] at hb
    rw [abs_le] at hb; linarith [hb.2]
  have hp : π > 3.14 := pi_gt_d2
  have hpp : π^2 > 9.8596 := by nlinarith [sq_nonneg π]
  have h1 : 4 / π^2 < 4 / 9.8596 := by apply div_lt_div_of_pos_left; norm_num; norm_num; exact hpp
  linarith

lemma f_one_pos : f 1 > 0 := by
  unfold f; simp only [one_pow]; linarith [cos_one_bound]

-- The main non-negativity lemma
-- f(0) = f(π/2) = 0, f > 0 on (0, 0.6], f > 0 on [π/2-ε, π/2), f(1) > 0
-- Since f is continuous on compact [0, π/2] and f > 0 at interior points near
-- boundaries and at y=1, by IVT f has no interior zeros, hence f ≥ 0.
set_option maxHeartbeats 1000000 in
lemma f_nonneg (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ π / 2) : f y ≥ 0 := by
  -- Handle endpoints
  by_cases hy_eq_0 : y = 0
  · rw [hy_eq_0, f_zero]
  by_cases hy_eq_pi_half : y = π / 2
  · rw [hy_eq_pi_half, f_pi_div_two]
  have hy_pos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hy_eq_0)
  have hy_lt_pi_half : y < π / 2 := lt_of_le_of_ne hy1 hy_eq_pi_half

  -- Case 1: y ∈ (0, 0.6]
  by_cases hy_small : y ≤ 0.6
  · have := f_pos_on_small y ⟨hy_pos, hy_small⟩; linarith
  push_neg at hy_small

  -- Get ε from f_pos_on_right
  obtain ⟨ε, hε_pos, hε_lt_pi_half, hf_pos_right⟩ := f_pos_on_right

  -- Case 2: y ∈ [π/2 - ε, π/2)
  by_cases hy_near_pi_half : π/2 - ε ≤ y
  · have := hf_pos_right y ⟨hy_near_pi_half, hy_lt_pi_half⟩; linarith
  push_neg at hy_near_pi_half

  -- Case 3: y ∈ (0.6, π/2 - ε)
  -- f(0.6) > 0, f(π/2 - ε) > 0, f is continuous
  -- If f(y) < 0, then by IVT there would be zeros in (0.6, y) and (y, π/2-ε)
  -- Combined with f(0) = f(π/2) = 0, this gives 4 zeros total
  -- By Rolle, between consecutive zeros there's a critical point
  -- But f' = sin(x) - 8x/π² has limited zeros in (0, π/2):
  -- f'(0) = 0, and f' has exactly one zero in (0, π/2) at the max of f
  -- So f can't have interior zeros, hence f(y) ≥ 0

  -- f attains min on compact [0.6, π/2-ε]
  -- f(0.6) > 0: from f_pos_on_small
  have hf_0p6 : f 0.6 > 0 := f_pos_on_small 0.6 ⟨by norm_num, le_refl 0.6⟩
  -- f(1) > 0: from f_one_pos
  have hf_1 : f 1 > 0 := f_one_pos
  -- 0.6 < 1 < π/2 - ε (assuming ε < π/2 - 1 ≈ 0.57)
  have h_one_in_range : 0.6 < (1 : ℝ) ∧ 1 < π/2 := by
    constructor; norm_num
    have hpi : π > 3 := pi_gt_three; linarith

  -- Split into (0.6, 1] and [1, π/2 - ε)
  by_cases hy_le_1 : y ≤ 1
  · -- y ∈ (0.6, 1]
    -- f(0.6) > 0, f(1) > 0, f continuous on [0.6, 1]
    -- Show f > 0 on [0.6, 1] using that f has no zero in this interval
    -- If f(c) ≤ 0 for some c ∈ (0.6, 1), by IVT there's a zero in (0.6, c)
    -- and a zero in (c, 1), giving 2 zeros in (0.6, 1)
    -- Combined with f(0) = 0, there would be a critical point in (0, first_zero)
    -- and another in (first_zero, second_zero) by Rolle
    -- But the structure of f' allows only one interior critical point
    -- This is a contradiction, so f(c) > 0 for all c ∈ (0.6, 1)

    -- For y ∈ (0.6, 1], use convexity-like argument
    -- Actually, use: f strictly monotone on each subinterval determined by critical point
    -- The unique critical point c* of f in (0, π/2) is where f achieves max
    -- On [0, c*], f is increasing; on [c*, π/2], f is decreasing
    -- Since f(0) = 0, f is increasing → positive on (0, c*]
    -- Since f(π/2) = 0, f is decreasing → positive on [c*, π/2)
    -- So f > 0 on (0, π/2)

    -- Key: c* > 0.6 (since f' > 0 on (0, 0.6) by f_deriv_pos_on_small_interval)
    -- And c* < π/2 (since f'(π/2) < 0 by f_deriv_neg_at_pi_div_two)
    -- f is strictly increasing on [0, c*], so f(y) > f(0) = 0 for y ∈ (0, c*]
    -- f is strictly decreasing on [c*, π/2], so f(y) > f(π/2) = 0 for y ∈ [c*, π/2)

    -- Since we don't have c* explicitly, use: f(0.6) > 0 and f monotone behavior
    -- f' > 0 on (0, 0.6) → f increasing on [0, 0.6] → f > 0 on (0, 0.6]
    -- f' changes sign somewhere in (0.6, π/2)
    -- For y ∈ (0.6, 1], if f(y) ≤ 0, then since f(0.6) > 0 and f(1) > 0,
    -- by IVT there's z₁ ∈ (0.6, y) with f(z₁) = 0 and z₂ ∈ (y, 1) with f(z₂) = 0
    -- Combined with f(0) = 0, Rolle gives critical points in (0, z₁) and (z₁, z₂)
    -- But f' > 0 on (0, 0.6) means first critical point is in (0.6, z₁)
    -- So there are 2 critical points in (0.6, z₂) ⊆ (0, π/2)
    -- But f' = sin - 8x/π² changes sign at most once in (0, π/2)
    -- (since f'' = cos - 8/π² changes sign exactly once)
    -- This is a contradiction, so f(y) > 0

    -- f(y) = 1 - 4y²/π² - cos(y)
    -- For y ∈ (0.6, 1], use Taylor bound: cos(y) ≤ 1 - y²/2 + y⁴ * 5/96
    -- f(y) ≥ y²(1/2 - 4/π²) - y⁴ * 5/96 ≥ y²(0.094 - y² * 0.052) > 0 for y ≤ 1
    unfold f
    have hp : π > 3.14 := pi_gt_d2
    have hpi_sq : π^2 > 9.8596 := by nlinarith [sq_nonneg π]
    have hcos : cos y ≤ 1 - y^2/2 + y^4 * (5/96) := by
      have hb := cos_bound (x := y) (by rw [abs_of_nonneg hy0]; linarith)
      rw [abs_le] at hb
      have habs : |y|^4 = y^4 := by rw [abs_of_nonneg hy0]
      linarith [hb.2, habs]
    have h_coeff : (1:ℝ)/2 - 4/π^2 > 0.094 := by
      have h : 4/π^2 < 4/9.8596 := by apply div_lt_div_of_pos_left; norm_num; norm_num; exact hpi_sq
      linarith
    have hy_sq_bound : y^2 ≤ 1 := by nlinarith
    have hy_4_bound : y^4 * (5/96) ≤ 5/96 := by nlinarith [sq_nonneg y]
    have h_positive : y^2 * (1/2 - 4/π^2) - y^4 * (5/96) > 0 := by
      have hy_sq_pos : y^2 > 0 := sq_pos_of_pos hy_pos
      have h1 : y^2 * 0.094 > 0 := by nlinarith
      have h2 : y^2 * (1/2 - 4/π^2) > y^2 * 0.094 := by nlinarith
      have h3 : y^4 * (5/96) < y^2 * 0.053 := by
        have hy4 : y^4 = y^2 * y^2 := by ring
        rw [hy4]; nlinarith
      nlinarith
    have hcalc : 1 - 4*y^2/π^2 - cos y > 0 := by
      calc 1 - 4*y^2/π^2 - cos y ≥ 1 - 4*y^2/π^2 - (1 - y^2/2 + y^4*(5/96)) := by linarith
        _ = y^2/2 - 4*y^2/π^2 - y^4*(5/96) := by ring
        _ = y^2 * (1/2 - 4/π^2) - y^4*(5/96) := by ring
        _ > 0 := h_positive
    linarith
  · -- y ∈ (1, π/2)
    push_neg at hy_le_1
    have hp : π > 3.14 := pi_gt_d2
    have hpi : π < 3.15 := pi_lt_d2
    have hpi_sq : π^2 > 9.8596 := by nlinarith [sq_nonneg π]
    have hpi_sq_lt : π^2 < 3.15^2 := sq_lt_sq' (by linarith [pi_pos]) hpi
    have hpi_sq_pos : π^2 > 0 := by positivity
    have hpi_sq_ne : π^2 ≠ 0 := ne_of_gt hpi_sq_pos
    have hpi_half_bound : π / 2 < 1.575 := by linarith
    have hy_gt_1 : y > 1 := hy_le_1

    -- Helper: 10/π² > 1 (needed for y ≥ 1.25 case)
    have h_10_div_pi_sq_gt_1 : (10:ℝ) / π^2 > 1 := by
      have h1 : (10 : ℝ) / 3.15^2 < 10 / π^2 :=
        div_lt_div_of_pos_left (by norm_num : (0:ℝ) < 10) hpi_sq_pos hpi_sq_lt
      have h2 : (10 : ℝ) / 3.15^2 > 1 := by norm_num
      linarith

    -- Helper: for y ≥ 1.25, f'(y) = sin(y) - 8y/π² < 0
    have h_f_deriv_neg : ∀ z, z ≥ 1.25 → sin z - 8 * z / π^2 < 0 := by
      intro z hz
      have h1 : 8 * z / π^2 ≥ 8 * 1.25 / π^2 := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hpi_sq_pos)
        linarith
      have h2 : (8 : ℝ) * 1.25 = 10 := by ring
      have h3 : 8 * z / π^2 ≥ 10 / π^2 := by linarith
      have h5 : sin z ≤ 1 := sin_le_one z
      linarith

    -- We split into two cases based on whether y ≥ 1.25
    by_cases h_case : y ≥ 1.25
    · -- CASE A: y ≥ 1.25
      -- Here f' = sin(y) - 8y/π² < 0 since 8*1.25/π² = 10/π² > 1 ≥ sin(y)
      -- f is strictly decreasing, f(π/2) = 0, so f(y) > 0

      -- f is strictly decreasing on [y, π/2] since f' < 0 there
      -- f(π/2) = 0, so f(y) > 0 for y < π/2
      have hf_anti : StrictAntiOn f (Icc y (π/2)) := by
        apply strictAntiOn_of_deriv_neg (convex_Icc y (π/2))
        · exact f_continuous.continuousOn
        · intro z hz
          simp only [interior_Icc, mem_Ioo] at hz
          rw [f_deriv]
          have hz_ge : z ≥ 1.25 := by linarith [hz.1]
          exact h_f_deriv_neg z hz_ge

      have hy_mem : y ∈ Icc y (π/2) := ⟨le_refl y, le_of_lt hy_lt_pi_half⟩
      have hpi_mem : (π/2) ∈ Icc y (π/2) := ⟨le_of_lt hy_lt_pi_half, le_refl _⟩
      have hfy_gt : f y > f (π/2) := hf_anti hy_mem hpi_mem hy_lt_pi_half
      rw [f_pi_div_two] at hfy_gt
      linarith

    · -- CASE B: y < 1.25, so y ∈ (1, 1.25)
      push_neg at h_case

      -- For y ∈ (1, 1.25), we show f(y) > 0 directly using bounds on cos
      -- Key insight: f(y) = 1 - 4y²/π² - cos(y)
      -- cos(y) < cos(1) (since cos is decreasing and y > 1)
      -- cos(1) ≤ 53/96 (from Taylor bound)
      -- 4y²/π² < 4*1.25²/π² = 6.25/π² < 6.25/9.86 < 0.634
      -- So f(y) > 1 - 0.634 - 0.552 = -0.186... this doesn't work directly

      -- Better approach: use MVT to bound cos(y)
      have hcos_cont : ContinuousOn cos (Icc 1 y) := continuousOn_cos
      have hcos_diff : DifferentiableOn ℝ cos (Ioo 1 y) := by
        intro z _; exact differentiableAt_cos.differentiableWithinAt

      have h_mvt_cos := exists_deriv_eq_slope cos hy_gt_1 hcos_cont hcos_diff
      obtain ⟨ξ, hξ_mem, hξ_eq⟩ := h_mvt_cos

      have hξ_gt_1 : ξ > 1 := hξ_mem.1
      have hξ_lt_y : ξ < y := hξ_mem.2
      have hξ_lt_1p25 : ξ < 1.25 := by linarith

      -- sin(ξ) > sin(1) since ξ > 1 and sin is increasing on [0, π/2]
      have h_sin_mono : StrictMonoOn sin (Icc 0 (π/2)) := by
        apply strictMonoOn_sin.mono
        intro x hx; constructor <;> linarith [hx.1, hx.2]
      have h1_in : (1 : ℝ) ∈ Icc 0 (π/2) := by constructor; norm_num; linarith
      have hξ_in : ξ ∈ Icc 0 (π/2) := by constructor; linarith; linarith
      have hsin_ξ_gt_sin_1 : sin ξ > sin 1 := h_sin_mono h1_in hξ_in hξ_gt_1

      -- sin(1) > 3/4
      have hsin_1_gt : sin 1 > 3/4 := by
        have hsc := sin_gt_sub_cube (x := (1 : ℝ)) (by norm_num : (0 : ℝ) < 1) (by linarith : (1 : ℝ) ≤ 1)
        simp only [one_pow] at hsc; linarith

      have hsin_ξ_gt : sin ξ > 3/4 := by linarith

      -- From MVT: cos(y) = cos(1) - sin(ξ)*(y-1) < cos(1) - (3/4)*(y-1)
      have h_deriv_cos_xi : deriv cos ξ = -sin ξ := Real.deriv_cos
      have h_cos_y_eq : cos y = cos 1 - sin ξ * (y - 1) := by
        have h_ne : y - 1 ≠ 0 := ne_of_gt (by linarith : y - 1 > 0)
        have h1 : deriv cos ξ = (cos y - cos 1) / (y - 1) := hξ_eq
        rw [h_deriv_cos_xi] at h1
        field_simp at h1 ⊢; linarith

      have hy_sub_1_pos : y - 1 > 0 := by linarith
      have h_cos_bound : cos y < cos 1 - (3/4) * (y - 1) := by
        rw [h_cos_y_eq]
        have h1 : sin ξ * (y - 1) > (3/4) * (y - 1) :=
          mul_lt_mul_of_pos_right hsin_ξ_gt hy_sub_1_pos
        linarith

      -- cos(1) ≤ 53/96
      have hcos_1_bound : cos 1 ≤ 53/96 := by
        have hb := cos_bound (x := (1 : ℝ)) (by norm_num : |(1 : ℝ)| ≤ 1)
        simp only [one_pow, abs_one, one_mul] at hb
        rw [abs_le] at hb; linarith [hb.2]

      -- f(y) > -29/96 + (3/4)y - 4y²/π²
      have h_f_lower : f y > -29/96 + (3/4)*y - 4*y^2/π^2 := by
        unfold f
        have step1 : 1 - 4*y^2/π^2 - cos y > 1 - 4*y^2/π^2 - (cos 1 - (3/4)*(y-1)) := by
          linarith [h_cos_bound]
        have step2 : 1 - 4*y^2/π^2 - (cos 1 - (3/4)*(y-1)) = 1 - cos 1 - 3/4 + (3/4)*y - 4*y^2/π^2 := by ring
        have step3 : 1 - cos 1 - 3/4 + (3/4)*y - 4*y^2/π^2 ≥ 1 - 53/96 - 3/4 + (3/4)*y - 4*y^2/π^2 := by
          linarith [hcos_1_bound]
        have step4 : 1 - 53/96 - 3/4 + (3/4)*y - 4*y^2/π^2 = -29/96 + (3/4)*y - 4*y^2/π^2 := by ring
        linarith

      -- For y ∈ (1, 1.25], h(y) = -29/96 + (3/4)y - 4y²/π² achieves min at y = 1.25
      -- h(1.25) = -29/96 + 3*1.25/4 - 4*1.5625/π² = -29/96 + 15/16 - 6.25/π²
      --         > -29/96 + 15/16 - 6.25/9.86 > -0.302 + 0.9375 - 0.634 > 0

      -- Actually evaluate h at y = 1 and y = 1.25
      have h_at_1 : (-29:ℝ)/96 + (3/4)*1 - 4*1^2/π^2 > 0 := by
        have h1 : (4:ℝ)/π^2 < 4/9.8596 :=
          div_lt_div_of_pos_left (by norm_num : (0:ℝ) < 4) (by norm_num) hpi_sq
        have h2 : (4:ℝ)/9.8596 < 0.406 := by norm_num
        linarith

      have h_at_1p25 : (-29:ℝ)/96 + (3/4)*1.25 - 4*1.25^2/π^2 > 0 := by
        have h_sq : (1.25 : ℝ)^2 = 1.5625 := by norm_num
        rw [h_sq]
        have h1 : (4:ℝ)*1.5625/π^2 < 4*1.5625/9.8596 := by
          apply div_lt_div_of_pos_left (by norm_num : (0:ℝ) < 4*1.5625) (by norm_num) hpi_sq
        have h2 : (4:ℝ)*1.5625/9.8596 < 0.634 := by norm_num
        have h3 : (-29:ℝ)/96 + (3/4)*1.25 = -29/96 + 15/16 := by ring
        have h4 : (-29:ℝ)/96 + 15/16 > 0.635 := by norm_num
        linarith

      -- h is a downward parabola in y, so min on [1, 1.25] is at one of the endpoints
      -- h'(y) = 3/4 - 8y/π² = 0 when y = 3π²/32 ≈ 0.93 < 1
      -- So h is decreasing on [1, 1.25], and min is at y = 1.25
      -- Actually h_at_1 > 0 and h_at_1p25 > 0, so h > 0 on the interval

      -- Since h is decreasing on [1, 1.25] (h' < 0 for y > 0.93), h(y) ≥ h(1.25) > 0
      have h_mono : -29/96 + (3/4)*y - 4*y^2/π^2 ≥ -29/96 + (3/4)*1.25 - 4*1.25^2/π^2 := by
        have h_sq : (1.25 : ℝ)^2 = 1.5625 := by norm_num
        rw [h_sq]
        -- h(y) - h(1.25) = (3/4)(y - 1.25) - 4(y² - 1.5625)/π²
        --                = (y - 1.25)[(3/4) - 4(y + 1.25)/π²]
        -- y ≤ 1.25, so (y - 1.25) ≤ 0
        -- y > 1, so y + 1.25 > 2.25, thus 4(y + 1.25)/π² > 9/π² > 9/9.93 > 0.9 > 3/4
        -- Product of two ≤ 0 is ≥ 0
        have hf1 : y - 1.25 ≤ 0 := by linarith
        have hsum : y + 1.25 > 2.25 := by linarith
        have hf2_numer : 4*(y + 1.25) > 9 := by linarith
        have hf2_frac : 4*(y + 1.25)/π^2 > 9/π^2 :=
          div_lt_div_of_pos_right hf2_numer hpi_sq_pos
        -- Use exact value 9.9225 for 3.15^2 to avoid linarith timeout
        have hpi_sq_lt_9p9225 : π^2 < 9.9225 := by
          have h1 : (3.15 : ℝ)^2 = 9.9225 := by norm_num
          rw [← h1]; exact hpi_sq_lt
        have h9_bound : (9:ℝ)/π^2 > 9/9.9225 := by
          apply div_lt_div_of_pos_left (by norm_num : (0:ℝ) < 9) hpi_sq_pos hpi_sq_lt_9p9225
        have h9_lower : (9:ℝ)/9.9225 > 0.907 := by norm_num
        have hf2_bound : 4*(y + 1.25)/π^2 > 0.907 := by linarith
        have hf2 : (3:ℝ)/4 - 4*(y + 1.25)/π^2 < 0 := by linarith
        have h_factor : -29/96 + (3/4)*y - 4*y^2/π^2 - (-29/96 + (3/4)*1.25 - 4*1.5625/π^2) =
                        (y - 1.25) * ((3/4) - 4*(y + 1.25)/π^2) := by
          field_simp; ring
        have hprod := mul_nonneg_of_nonpos_of_nonpos hf1 (le_of_lt hf2)
        linarith

      linarith [h_f_lower, h_mono, h_at_1p25]

theorem cos_le_parabola (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ π / 2) :
    cos y ≤ 1 - 4 * y^2 / π^2 := by
  have h := f_nonneg y hy0 hy1
  unfold f at h
  linarith

theorem sin_le_parabola_first_half (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ π / 2) :
    sin x ≤ 4 * x * (π - x) / π^2 := by
  set y := π / 2 - x with hy_def
  have hy0 : 0 ≤ y := by linarith
  have hy1 : y ≤ π / 2 := by linarith
  have hsin : sin x = cos y := by
    have : x = π / 2 - y := by linarith
    rw [this, sin_pi_div_two_sub]
  have hpara : 4 * x * (π - x) / π^2 = 1 - 4 * y^2 / π^2 := by
    have hp : π ≠ 0 := ne_of_gt pi_pos
    have : x = π / 2 - y := by linarith
    rw [this]
    field_simp
    ring
  rw [hsin, hpara]
  exact cos_le_parabola y hy0 hy1

theorem sin_le_parabola_full (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ π) :
    sin x ≤ 4 * x * (π - x) / π^2 := by
  by_cases h : x ≤ π / 2
  · exact sin_le_parabola_first_half x hx0 h
  · push_neg at h
    have hx' : π - x ≤ π / 2 := by linarith
    have hx'0 : 0 ≤ π - x := by linarith
    have h_sin_sym : sin x = sin (π - x) := (sin_pi_sub x).symm
    rw [h_sin_sym]
    have hpara : 4 * x * (π - x) / π^2 = 4 * (π - x) * (π - (π - x)) / π^2 := by ring
    rw [hpara]
    exact sin_le_parabola_first_half (π - x) hx'0 hx'

end PutnamA2Upper

-- ============================================================================
-- MAIN THEOREM: Combined bounds
-- ============================================================================

namespace PutnamA2

/-- The main inequality: (1/π) * x(π-x) ≤ sin(x) ≤ (4/π²) * x(π-x) for x ∈ [0, π] -/
theorem sin_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ π) :
    x * (π - x) / π ≤ sin x ∧ sin x ≤ 4 * x * (π - x) / π^2 := by
  constructor
  · exact PutnamA2Lower.sin_ge_quadratic_on_full x hx0 hx1
  · exact PutnamA2Upper.sin_le_parabola_full x hx0 hx1

/-- The answer: a = 1/π, b = 4/π² -/
noncomputable def a : ℝ := 1 / π
noncomputable def b : ℝ := 4 / π^2

/-- The bounds hold with a = 1/π and b = 4/π² -/
theorem bounds_hold (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ π) :
    a * x * (π - x) ≤ sin x ∧ sin x ≤ b * x * (π - x) := by
  have ⟨hlower, hupper⟩ := sin_bounds x hx0 hx1
  have hp : π ≠ 0 := ne_of_gt pi_pos
  constructor
  · unfold a
    have heq : 1 / π * x * (π - x) = x * (π - x) / π := by field_simp
    rw [heq]
    exact hlower
  · unfold b
    have heq : 4 / π^2 * x * (π - x) = 4 * x * (π - x) / π^2 := by field_simp
    rw [heq]
    exact hupper

-- ============================================================================
-- OPTIMALITY PROOFS: a = 1/π is the LARGEST and b = 4/π² is the SMALLEST
-- ============================================================================

/-- Optimality of b = 4/π²: At x = π/2, sin(x) = b * x * (π - x) exactly.
    Therefore, any b' < b would fail the upper bound at x = π/2. -/
theorem b_is_optimal : sin (π / 2) = b * (π / 2) * (π - π / 2) := by
  have hp : π ≠ 0 := ne_of_gt pi_pos
  rw [sin_pi_div_two]
  unfold b
  field_simp
  ring

/-- For any b' < 4/π², there exists x ∈ [0, π] where sin(x) > b' * x * (π - x) -/
theorem b_optimal_witness (b' : ℝ) (hb' : b' < 4 / π^2) :
    ∃ x, 0 ≤ x ∧ x ≤ π ∧ sin x > b' * x * (π - x) := by
  use π / 2
  have hp : π > 0 := pi_pos
  refine ⟨by linarith, by linarith, ?_⟩
  rw [sin_pi_div_two]
  have heq : (π / 2) * (π - π / 2) = π^2 / 4 := by field_simp; ring
  have h1 : b' * ((π / 2) * (π - π / 2)) < (4 / π^2) * (π^2 / 4) := by
    rw [heq]
    apply mul_lt_mul_of_pos_right hb'
    have hp2 : π^2 > 0 := by positivity
    linarith
  have h2 : (4 : ℝ) / π^2 * (π^2 / 4) = 1 := by field_simp
  linarith

/-- Key lemma: sin(x) ≤ x for x ≥ 0 -/
lemma sin_le_self (x : ℝ) (hx : 0 ≤ x) : sin x ≤ x := by
  by_cases hx1 : x ≤ 1
  · exact sin_le hx
  · push_neg at hx1
    have h1 : sin x ≤ 1 := sin_le_one x
    linarith

/-- For any a' > 1/π, there exists x ∈ (0, π) where a' * x * (π - x) > sin(x) -/
theorem a_optimal_witness (a' : ℝ) (ha' : a' > 1 / π) :
    ∃ x, 0 < x ∧ x < π ∧ a' * x * (π - x) > sin x := by
  have hp : π > 0 := pi_pos
  have ha'_pos : a' > 0 := by
    have h1 : (1 : ℝ) / π > 0 := by positivity
    linarith
  -- 1 < a' * π since a' > 1/π implies a' * π > 1
  have h1 : 1 < a' * π := by
    have hstep : a' > 1 / π := ha'
    have hstep2 : a' * π > (1 / π) * π := by nlinarith
    simp at hstep2
    exact hstep2
  -- 1/a' < π
  have h_inv_a' : 1 / a' < π := by
    have h2 : 1 / a' < a' * π / a' := div_lt_div_of_pos_right h1 ha'_pos
    have h3 : a' * π / a' = π := by field_simp
    linarith
  have h_diff_pos : π - 1 / a' > 0 := by linarith

  let x₀ := min 1 ((π - 1 / a') / 2)
  use x₀

  have hx₀_pos : x₀ > 0 := by
    have h1' : (1 : ℝ) > 0 := by norm_num
    have h2' : (π - 1 / a') / 2 > 0 := by linarith
    exact lt_min h1' h2'

  have hx₀_le_1 : x₀ ≤ 1 := min_le_left 1 ((π - 1 / a') / 2)

  have hx₀_lt_diff : x₀ < π - 1 / a' := by
    calc x₀ ≤ (π - 1 / a') / 2 := min_le_right 1 ((π - 1 / a') / 2)
      _ < π - 1 / a' := by linarith

  have hx₀_lt_pi : x₀ < π := by
    have h1' : 1 / a' > 0 := by positivity
    linarith

  refine ⟨hx₀_pos, hx₀_lt_pi, ?_⟩

  have ha_step : a' * (π - x₀) > 1 := by
    have h : x₀ < π - 1 / a' := hx₀_lt_diff
    have h' : π - x₀ > 1 / a' := by linarith
    have hstep : a' * (π - x₀) > a' * (1 / a') := by nlinarith
    have hsimp : a' * (1 / a') = 1 := by field_simp
    linarith

  have h2 : a' * x₀ * (π - x₀) > x₀ := by
    have hx₀_pos' : x₀ > 0 := hx₀_pos
    have hstep1 : a' * x₀ * (π - x₀) = x₀ * (a' * (π - x₀)) := by ring
    have hstep2 : x₀ * (a' * (π - x₀)) > x₀ * 1 := by nlinarith
    linarith

  have h3 : sin x₀ ≤ x₀ := sin_le_self x₀ (le_of_lt hx₀_pos)

  linarith

/-- Combined optimality: a = 1/π is the largest lower bound constant, b = 4/π² is the smallest upper bound constant -/
theorem optimal_constants :
    (∀ a' > 1 / π, ∃ x, 0 ≤ x ∧ x ≤ π ∧ a' * x * (π - x) > sin x) ∧
    (∀ b' < 4 / π^2, ∃ x, 0 ≤ x ∧ x ≤ π ∧ sin x > b' * x * (π - x)) := by
  constructor
  · intro a' ha'
    obtain ⟨x, hx_pos, hx_lt_pi, hineq⟩ := a_optimal_witness a' ha'
    exact ⟨x, le_of_lt hx_pos, le_of_lt hx_lt_pi, hineq⟩
  · intro b' hb'
    exact b_optimal_witness b' hb'

end PutnamA2
