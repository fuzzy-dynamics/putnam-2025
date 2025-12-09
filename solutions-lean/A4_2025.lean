/-
  Putnam 2025 Problem A4 - Complete Formalization

  PROBLEM:
  Find the minimal value of k such that there exist k-by-k real matrices
  A_1, ..., A_2025 with the property that A_i*A_j = A_j*A_i if and only if
  |i-j| in {0, 1, 2024}.

  ANSWER: k = 3

  PROOF OVERVIEW:
  Part 1: k = 2 is impossible.
    Key lemma: If A is a 2x2 non-scalar matrix that commutes with both B and C,
    then B and C must commute. (Centralizer of non-scalar 2x2 matrix is commutative)
    Contrapositive: if B and C don't commute, and A commutes with both, then A is scalar.
    Since scalar matrices commute with everything, we get a contradiction.

  Part 2: k = 3 works.
    Construction using rank-1 matrices.
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Putnam2025A4

open Matrix Finset

/-! ### Part 1: k = 2 is Impossible -/

section TwoByTwo

/-- A scalar matrix (multiple of identity) -/
def isScalar2 (A : Matrix (Fin 2) (Fin 2) Real) : Prop :=
  exists c : Real, A = c • (1 : Matrix (Fin 2) (Fin 2) Real)

/-- Every matrix commutes with scalar matrices -/
lemma scalar_commutes_all (c : Real) (B : Matrix (Fin 2) (Fin 2) Real) :
    (c • (1 : Matrix (Fin 2) (Fin 2) Real)) * B = B * (c • (1 : Matrix (Fin 2) (Fin 2) Real)) := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

/-- Key lemma: the centralizer of a non-scalar 2x2 matrix is commutative.

    Mathematical fact: For any 2x2 non-scalar matrix A over a field, the centralizer
    C(A) = {B : AB = BA} is a 2-dimensional commutative algebra spanned by {I, A}.
    Therefore any two matrices in the centralizer commute.

    This is because:
    1. If A has two distinct eigenvalues, A is diagonalizable and C(A) consists of
       diagonal matrices in the same eigenbasis, hence commutative.
    2. If A has one eigenvalue with multiplicity 2 but is not scalar, A is similar
       to a Jordan block, and C(A) = {aI + bN : a,b in R} where N is nilpotent,
       which is commutative.
-/
lemma centralizer_commutative (A : Matrix (Fin 2) (Fin 2) Real) (hA : ¬isScalar2 A)
    (B C : Matrix (Fin 2) (Fin 2) Real)
    (hB : A * B = B * A) (hC : A * C = C * A) :
    B * C = C * B := by
  -- We prove this by explicit coordinate calculation
  -- Let A = ![![a,b],![c,d]], B = ![![x,y],![z,w]], C = ![![p,q],![r,s]]

  -- First, establish that A is non-scalar means: b ≠ 0 ∨ c ≠ 0 ∨ A 0 0 ≠ A 1 1
  have hA' : A 0 1 ≠ 0 ∨ A 1 0 ≠ 0 ∨ A 0 0 ≠ A 1 1 := by
    by_contra hall
    push_neg at hall
    apply hA
    use A 0 0
    ext i j
    fin_cases i <;> fin_cases j
    · simp
    · simp [hall.1]
    · simp [hall.2.1]
    · simp [hall.2.2]

  -- Extract commutativity constraints from AB = BA
  have hAB01 : A 0 0 * B 0 1 + A 0 1 * B 1 1 = A 0 1 * B 0 0 + A 1 1 * B 0 1 := by
    have := congrFun (congrFun hB 0) 1
    simp only [mul_apply, Fin.sum_univ_two, Fin.isValue] at this
    linarith

  have hAB10 : A 1 0 * B 0 0 + A 1 1 * B 1 0 = A 0 0 * B 1 0 + A 1 0 * B 1 1 := by
    have := congrFun (congrFun hB 1) 0
    simp only [mul_apply, Fin.sum_univ_two, Fin.isValue] at this
    linarith

  have hAC01 : A 0 0 * C 0 1 + A 0 1 * C 1 1 = A 0 1 * C 0 0 + A 1 1 * C 0 1 := by
    have := congrFun (congrFun hC 0) 1
    simp only [mul_apply, Fin.sum_univ_two, Fin.isValue] at this
    linarith

  have hAC10 : A 1 0 * C 0 0 + A 1 1 * C 1 0 = A 0 0 * C 1 0 + A 1 0 * C 1 1 := by
    have := congrFun (congrFun hC 1) 0
    simp only [mul_apply, Fin.sum_univ_two, Fin.isValue] at this
    linarith

  -- Simplify the constraints
  -- hAB01: (A00 - A11)*B01 = A01*(B00 - B11)
  -- hAB10: A10*(B00 - B11) = (A00 - A11)*B10
  -- Similarly for C

  have eq1 : (A 0 0 - A 1 1) * B 0 1 = A 0 1 * (B 0 0 - B 1 1) := by linarith
  have eq2 : A 1 0 * (B 0 0 - B 1 1) = (A 0 0 - A 1 1) * B 1 0 := by linarith
  have eq3 : (A 0 0 - A 1 1) * C 0 1 = A 0 1 * (C 0 0 - C 1 1) := by linarith
  have eq4 : A 1 0 * (C 0 0 - C 1 1) = (A 0 0 - A 1 1) * C 1 0 := by linarith

  -- Also need to extract diagonal constraints from AB = BA
  have hAB00 : A 0 0 * B 0 0 + A 0 1 * B 1 0 = A 0 0 * B 0 0 + A 1 0 * B 0 1 := by
    have := congrFun (congrFun hB 0) 0
    simp only [mul_apply, Fin.sum_univ_two, Fin.isValue] at this
    linarith
  have eq5 : A 0 1 * B 1 0 = A 1 0 * B 0 1 := by linarith

  have hAC00 : A 0 0 * C 0 0 + A 0 1 * C 1 0 = A 0 0 * C 0 0 + A 1 0 * C 0 1 := by
    have := congrFun (congrFun hC 0) 0
    simp only [mul_apply, Fin.sum_univ_two, Fin.isValue] at this
    linarith
  have eq6 : A 0 1 * C 1 0 = A 1 0 * C 0 1 := by linarith

  -- Now we need to show BC = CB
  -- (BC)_ij = sum_k B_ik * C_kj
  -- We need to show: B*C - C*B = 0

  -- The commutator [B,C] has entries:
  -- [B,C]_00 = B01*C10 - B10*C01
  -- [B,C]_01 = B00*C01 + B01*C11 - C00*B01 - C01*B11 = (B00-B11)*C01 - (C00-C11)*B01
  -- [B,C]_10 = B10*C00 + B11*C10 - C10*B00 - C11*B10 = (B11-B00)*C10 + (C00-C11)*B10
  --          = -(B00-B11)*C10 + (C00-C11)*B10
  -- [B,C]_11 = B10*C01 - B01*C10 = -[B,C]_00

  -- Show [B,C]_01 = 0
  -- We have: eq1: (A00-A11)*B01 = A01*(B00-B11)
  --          eq3: (A00-A11)*C01 = A01*(C00-C11)
  -- If A01 ≠ 0: B01 = A01*(B00-B11)/(A00-A11) if A00≠A11, else B00=B11
  --             C01 = A01*(C00-C11)/(A00-A11) if A00≠A11, else C00=C11
  -- Then [B,C]_01 = (B00-B11)*C01 - (C00-C11)*B01
  --              = (B00-B11)*A01*(C00-C11)/(A00-A11) - (C00-C11)*A01*(B00-B11)/(A00-A11)
  --              = 0

  -- First prove the key fact that B 0 1 * C 1 0 = C 0 1 * B 1 0
  have key00 : B 0 1 * C 1 0 = C 0 1 * B 1 0 := by
    rcases hA' with hb | hc | had
    · -- A01 ≠ 0
      have h3 : A 0 1 * (B 0 1 * C 1 0 - C 0 1 * B 1 0) = 0 := by
        calc A 0 1 * (B 0 1 * C 1 0 - C 0 1 * B 1 0)
          = B 0 1 * (A 0 1 * C 1 0) - C 0 1 * (A 0 1 * B 1 0) := by ring
        _ = B 0 1 * (A 1 0 * C 0 1) - C 0 1 * (A 1 0 * B 0 1) := by rw [eq6, eq5]
        _ = 0 := by ring
      cases mul_eq_zero.mp h3 with
      | inl h => exact absurd h hb
      | inr h => linarith
    · -- A10 ≠ 0
      have h2 : A 1 0 * B 0 1 = A 0 1 * B 1 0 := by linarith [eq5]
      have h3 : A 1 0 * C 0 1 = A 0 1 * C 1 0 := by linarith [eq6]
      have h5 : A 1 0 * (B 0 1 * C 1 0 - C 0 1 * B 1 0) = 0 := by
        calc A 1 0 * (B 0 1 * C 1 0 - C 0 1 * B 1 0)
          = (A 1 0 * B 0 1) * C 1 0 - (A 1 0 * C 0 1) * B 1 0 := by ring
        _ = (A 0 1 * B 1 0) * C 1 0 - (A 0 1 * C 1 0) * B 1 0 := by rw [h2, h3]
        _ = 0 := by ring
      cases mul_eq_zero.mp h5 with
      | inl h => exact absurd h hc
      | inr h => linarith
    · -- A00 ≠ A11
      by_cases hb' : A 0 1 ≠ 0
      · have h2 : A 0 1 * (B 0 1 * C 1 0 - C 0 1 * B 1 0) = 0 := by
          calc A 0 1 * (B 0 1 * C 1 0 - C 0 1 * B 1 0)
            = B 0 1 * (A 0 1 * C 1 0) - C 0 1 * (A 0 1 * B 1 0) := by ring
          _ = B 0 1 * (A 1 0 * C 0 1) - C 0 1 * (A 1 0 * B 0 1) := by rw [eq6, eq5]
          _ = 0 := by ring
        cases mul_eq_zero.mp h2 with
        | inl h => exact absurd h hb'
        | inr h => linarith
      · push_neg at hb'
        by_cases hc' : A 1 0 ≠ 0
        · have h2 : A 1 0 * B 0 1 = A 0 1 * B 1 0 := by linarith [eq5]
          have h3 : A 1 0 * C 0 1 = A 0 1 * C 1 0 := by linarith [eq6]
          have h4 : A 1 0 * (B 0 1 * C 1 0 - C 0 1 * B 1 0) = 0 := by
            calc A 1 0 * (B 0 1 * C 1 0 - C 0 1 * B 1 0)
              = (A 1 0 * B 0 1) * C 1 0 - (A 1 0 * C 0 1) * B 1 0 := by ring
            _ = (A 0 1 * B 1 0) * C 1 0 - (A 0 1 * C 1 0) * B 1 0 := by rw [h2, h3]
            _ = 0 := by ring
          cases mul_eq_zero.mp h4 with
          | inl h => exact absurd h hc'
          | inr h => linarith
        · push_neg at hc'
          -- A01 = 0, A10 = 0, A00 ≠ A11
          have hB01 : B 0 1 = 0 := by
            have h' : (A 0 0 - A 1 1) * B 0 1 = 0 := by simp only [hb'] at eq1; linarith
            cases mul_eq_zero.mp h' with
            | inl h => exact absurd (sub_eq_zero.mp h) had
            | inr h => exact h
          have hC01 : C 0 1 = 0 := by
            have h' : (A 0 0 - A 1 1) * C 0 1 = 0 := by simp only [hb'] at eq3; linarith
            cases mul_eq_zero.mp h' with
            | inl h => exact absurd (sub_eq_zero.mp h) had
            | inr h => exact h
          simp [hB01, hC01]

  -- Prove (B00-B11)*C01 = (C00-C11)*B01
  have key01 : (B 0 0 - B 1 1) * C 0 1 = (C 0 0 - C 1 1) * B 0 1 := by
    rcases hA' with hb | hc | had
    · -- A01 ≠ 0
      by_cases had' : A 0 0 = A 1 1
      · -- If A00 = A11, then from eq1: 0 = A01*(B00-B11), so B00=B11
        have hBdiag : B 0 0 = B 1 1 := by
          have h' : A 0 1 * (B 0 0 - B 1 1) = 0 := by simp only [had', sub_self, zero_mul] at eq1; linarith
          cases mul_eq_zero.mp h' with
          | inl h => exact absurd h hb
          | inr h => linarith
        have hCdiag : C 0 0 = C 1 1 := by
          have h' : A 0 1 * (C 0 0 - C 1 1) = 0 := by simp only [had', sub_self, zero_mul] at eq3; linarith
          cases mul_eq_zero.mp h' with
          | inl h => exact absurd h hb
          | inr h => linarith
        simp [hBdiag, hCdiag]
      · -- A00 ≠ A11
        -- After rw [eq3, eq1], h1 becomes:
        -- (A00-A11)*(...) = (B00-B11)*A01*(C00-C11) - (C00-C11)*A01*(B00-B11) = 0
        have h3 : (A 0 0 - A 1 1) * ((B 0 0 - B 1 1) * C 0 1 - (C 0 0 - C 1 1) * B 0 1) = 0 := by
          calc (A 0 0 - A 1 1) * ((B 0 0 - B 1 1) * C 0 1 - (C 0 0 - C 1 1) * B 0 1)
            = (B 0 0 - B 1 1) * ((A 0 0 - A 1 1) * C 0 1) -
              (C 0 0 - C 1 1) * ((A 0 0 - A 1 1) * B 0 1) := by ring
          _ = (B 0 0 - B 1 1) * (A 0 1 * (C 0 0 - C 1 1)) -
              (C 0 0 - C 1 1) * (A 0 1 * (B 0 0 - B 1 1)) := by rw [eq3, eq1]
          _ = 0 := by ring
        cases mul_eq_zero.mp h3 with
        | inl h => exact absurd (sub_eq_zero.mp h) had'
        | inr h => linarith
    · -- A10 ≠ 0
      by_cases had' : A 0 0 = A 1 1
      · have hBdiag : B 0 0 = B 1 1 := by
          have h' : A 1 0 * (B 0 0 - B 1 1) = 0 := by simp only [had', sub_self] at eq2; linarith
          cases mul_eq_zero.mp h' with
          | inl h => exact absurd h hc
          | inr h => linarith
        have hCdiag : C 0 0 = C 1 1 := by
          have h' : A 1 0 * (C 0 0 - C 1 1) = 0 := by simp only [had', sub_self] at eq4; linarith
          cases mul_eq_zero.mp h' with
          | inl h => exact absurd h hc
          | inr h => linarith
        simp [hBdiag, hCdiag]
      · have h2 : (A 0 0 - A 1 1) * ((B 0 0 - B 1 1) * C 0 1 - (C 0 0 - C 1 1) * B 0 1) = 0 := by
          calc (A 0 0 - A 1 1) * ((B 0 0 - B 1 1) * C 0 1 - (C 0 0 - C 1 1) * B 0 1)
            = (B 0 0 - B 1 1) * ((A 0 0 - A 1 1) * C 0 1) -
              (C 0 0 - C 1 1) * ((A 0 0 - A 1 1) * B 0 1) := by ring
          _ = (B 0 0 - B 1 1) * (A 0 1 * (C 0 0 - C 1 1)) -
              (C 0 0 - C 1 1) * (A 0 1 * (B 0 0 - B 1 1)) := by rw [eq3, eq1]
          _ = 0 := by ring
        cases mul_eq_zero.mp h2 with
        | inl h => exact absurd (sub_eq_zero.mp h) had'
        | inr h => linarith
    · -- A00 ≠ A11
      have h2 : (A 0 0 - A 1 1) * ((B 0 0 - B 1 1) * C 0 1 - (C 0 0 - C 1 1) * B 0 1) = 0 := by
        calc (A 0 0 - A 1 1) * ((B 0 0 - B 1 1) * C 0 1 - (C 0 0 - C 1 1) * B 0 1)
          = (B 0 0 - B 1 1) * ((A 0 0 - A 1 1) * C 0 1) -
            (C 0 0 - C 1 1) * ((A 0 0 - A 1 1) * B 0 1) := by ring
        _ = (B 0 0 - B 1 1) * (A 0 1 * (C 0 0 - C 1 1)) -
            (C 0 0 - C 1 1) * (A 0 1 * (B 0 0 - B 1 1)) := by rw [eq3, eq1]
        _ = 0 := by ring
      cases mul_eq_zero.mp h2 with
      | inl h => exact absurd (sub_eq_zero.mp h) had
      | inr h => linarith

  -- Prove (B00-B11)*C10 = (C00-C11)*B10
  have key10 : (B 0 0 - B 1 1) * C 1 0 = (C 0 0 - C 1 1) * B 1 0 := by
    rcases hA' with hb | hc | had
    · -- A01 ≠ 0
      by_cases had' : A 0 0 = A 1 1
      · have hBdiag : B 0 0 = B 1 1 := by
          have h' : A 0 1 * (B 0 0 - B 1 1) = 0 := by simp only [had', sub_self, zero_mul] at eq1; linarith
          cases mul_eq_zero.mp h' with
          | inl h => exact absurd h hb
          | inr h => linarith
        have hCdiag : C 0 0 = C 1 1 := by
          have h' : A 0 1 * (C 0 0 - C 1 1) = 0 := by simp only [had', sub_self, zero_mul] at eq3; linarith
          cases mul_eq_zero.mp h' with
          | inl h => exact absurd h hb
          | inr h => linarith
        simp [hBdiag, hCdiag]
      · have eq2' : (A 0 0 - A 1 1) * B 1 0 = A 1 0 * (B 0 0 - B 1 1) := by linarith
        have eq4' : (A 0 0 - A 1 1) * C 1 0 = A 1 0 * (C 0 0 - C 1 1) := by linarith
        have h2 : (A 0 0 - A 1 1) * ((B 0 0 - B 1 1) * C 1 0 - (C 0 0 - C 1 1) * B 1 0) = 0 := by
          calc (A 0 0 - A 1 1) * ((B 0 0 - B 1 1) * C 1 0 - (C 0 0 - C 1 1) * B 1 0)
            = (B 0 0 - B 1 1) * ((A 0 0 - A 1 1) * C 1 0) -
              (C 0 0 - C 1 1) * ((A 0 0 - A 1 1) * B 1 0) := by ring
          _ = (B 0 0 - B 1 1) * (A 1 0 * (C 0 0 - C 1 1)) -
              (C 0 0 - C 1 1) * (A 1 0 * (B 0 0 - B 1 1)) := by rw [eq4', eq2']
          _ = 0 := by ring
        cases mul_eq_zero.mp h2 with
        | inl h => exact absurd (sub_eq_zero.mp h) had'
        | inr h => linarith
    · -- A10 ≠ 0
      by_cases had' : A 0 0 = A 1 1
      · have hBdiag : B 0 0 = B 1 1 := by
          have h' : A 1 0 * (B 0 0 - B 1 1) = 0 := by simp only [had', sub_self] at eq2; linarith
          cases mul_eq_zero.mp h' with
          | inl h => exact absurd h hc
          | inr h => linarith
        have hCdiag : C 0 0 = C 1 1 := by
          have h' : A 1 0 * (C 0 0 - C 1 1) = 0 := by simp only [had', sub_self] at eq4; linarith
          cases mul_eq_zero.mp h' with
          | inl h => exact absurd h hc
          | inr h => linarith
        simp [hBdiag, hCdiag]
      · have eq2' : (A 0 0 - A 1 1) * B 1 0 = A 1 0 * (B 0 0 - B 1 1) := by linarith
        have eq4' : (A 0 0 - A 1 1) * C 1 0 = A 1 0 * (C 0 0 - C 1 1) := by linarith
        have h2 : (A 0 0 - A 1 1) * ((B 0 0 - B 1 1) * C 1 0 - (C 0 0 - C 1 1) * B 1 0) = 0 := by
          calc (A 0 0 - A 1 1) * ((B 0 0 - B 1 1) * C 1 0 - (C 0 0 - C 1 1) * B 1 0)
            = (B 0 0 - B 1 1) * ((A 0 0 - A 1 1) * C 1 0) -
              (C 0 0 - C 1 1) * ((A 0 0 - A 1 1) * B 1 0) := by ring
          _ = (B 0 0 - B 1 1) * (A 1 0 * (C 0 0 - C 1 1)) -
              (C 0 0 - C 1 1) * (A 1 0 * (B 0 0 - B 1 1)) := by rw [eq4', eq2']
          _ = 0 := by ring
        cases mul_eq_zero.mp h2 with
        | inl h => exact absurd (sub_eq_zero.mp h) had'
        | inr h => linarith
    · -- A00 ≠ A11
      have eq2' : (A 0 0 - A 1 1) * B 1 0 = A 1 0 * (B 0 0 - B 1 1) := by linarith
      have eq4' : (A 0 0 - A 1 1) * C 1 0 = A 1 0 * (C 0 0 - C 1 1) := by linarith
      have h2 : (A 0 0 - A 1 1) * ((B 0 0 - B 1 1) * C 1 0 - (C 0 0 - C 1 1) * B 1 0) = 0 := by
        calc (A 0 0 - A 1 1) * ((B 0 0 - B 1 1) * C 1 0 - (C 0 0 - C 1 1) * B 1 0)
          = (B 0 0 - B 1 1) * ((A 0 0 - A 1 1) * C 1 0) -
            (C 0 0 - C 1 1) * ((A 0 0 - A 1 1) * B 1 0) := by ring
        _ = (B 0 0 - B 1 1) * (A 1 0 * (C 0 0 - C 1 1)) -
            (C 0 0 - C 1 1) * (A 1 0 * (B 0 0 - B 1 1)) := by rw [eq4', eq2']
        _ = 0 := by ring
      cases mul_eq_zero.mp h2 with
      | inl h => exact absurd (sub_eq_zero.mp h) had
      | inr h => linarith

  -- We need to show (B * C) i j = (C * B) i j for all i, j
  -- Break into 4 cases and prove each using the key lemmas
  have entry00 : (B * C) 0 0 = (C * B) 0 0 := by
    simp only [mul_apply, Fin.sum_univ_two, Fin.isValue]
    linarith [key00]
  have entry01 : (B * C) 0 1 = (C * B) 0 1 := by
    simp only [mul_apply, Fin.sum_univ_two, Fin.isValue]
    have := key01; ring_nf at this ⊢; linarith
  have entry10 : (B * C) 1 0 = (C * B) 1 0 := by
    simp only [mul_apply, Fin.sum_univ_two, Fin.isValue]
    have := key10; ring_nf at this ⊢; linarith
  have entry11 : (B * C) 1 1 = (C * B) 1 1 := by
    simp only [mul_apply, Fin.sum_univ_two, Fin.isValue]
    linarith [key00]
  -- Now combine
  ext i j
  fin_cases i <;> fin_cases j
  · exact entry00
  · exact entry01
  · exact entry10
  · exact entry11

/-- Main lemma for k=2: If A commutes with B and C, but B doesn't commute with C,
    then A must be scalar. -/
theorem commutes_with_noncommuting_implies_scalar
    (A B C : Matrix (Fin 2) (Fin 2) Real)
    (hAB : A * B = B * A)
    (hAC : A * C = C * A)
    (hBC : B * C ≠ C * B) :
    isScalar2 A := by
  by_contra hA
  have := centralizer_commutative A hA B C hAB hAC
  exact hBC this

end TwoByTwo

/-! ### Index type and closeness -/

section Index

/-- Index type for our 2025 matrices (using ZMod for cyclic structure) -/
abbrev Index := ZMod 2025

/-- Two indices are "close" if |i-j| in {0, 1, 2024} mod 2025 -/
def close (i j : Index) : Prop :=
  i = j ∨ j = i + 1 ∨ i = j + 1

/-- close is symmetric -/
lemma close_symm (i j : Index) : close i j ↔ close j i := by
  unfold close
  constructor <;> intro h <;> rcases h with rfl | h | h
  · left; rfl
  · right; right; exact h
  · right; left; exact h
  · left; rfl
  · right; right; exact h
  · right; left; exact h

/-- close is reflexive -/
lemma close_refl (i : Index) : close i i := Or.inl rfl

end Index

/-! ### Main Theorem -/

/-- k = 1 is impossible: all 1x1 matrices commute -/
lemma one_by_one_impossible :
    ¬(∃ A : Index → Matrix (Fin 1) (Fin 1) Real,
      ∀ i j : Index, (A i * A j = A j * A i ↔ close i j)) := by
  intro ⟨A, hA⟩
  -- 1x1 matrices always commute
  have hall_comm : ∀ i j, A i * A j = A j * A i := fun i j => by
    ext r s; fin_cases r; fin_cases s
    simp only [Matrix.mul_apply, Fin.sum_univ_one, Fin.isValue]
    ring_nf
    exact mul_comm _ _
  -- But indices 0 and 2 are not close
  have hnotclose : ¬close 0 2 := by
    unfold close; push_neg
    constructor
    · intro h; cases h
    · constructor <;> (intro h; cases h)
  exact hnotclose ((hA 0 2).mp (hall_comm 0 2))

/-- The answer to Putnam 2025 A4 is k = 3 -/
theorem putnam_2025_A4_answer :
    -- There exist 3x3 real matrices A_1, ..., A_2025 satisfying the condition
    (exists A : Index -> Matrix (Fin 3) (Fin 3) Real,
      ∀ i j : Index, (A i * A j = A j * A i ↔ close i j)) ∧
    -- There do NOT exist 2x2 real matrices satisfying the condition
    (Not (exists A : Index -> Matrix (Fin 2) (Fin 2) Real,
      ∀ i j : Index, (A i * A j = A j * A i ↔ close i j))) := by
  constructor
  · -- Part 1: Construction for k = 3
    -- We use rank-1 matrices A_i = v_i ⊗ u_i where:
    -- - v_i = (1, t_i, t_i^2) with t_i = i.val (points on moment curve)
    -- - u_i = v_{i-1} × v_{i+1} (cross product, orthogonal to both neighbors)
    --
    -- Key property: For rank-1 matrices, A_i * A_j = (u_i · v_j) · (v_i ⊗ u_j)
    -- - Close pairs: u_i ⊥ v_{i±1} by cross product → products = 0 → commute
    -- - Non-close: det(v_{i-1}, v_{i+1}, v_j) ≠ 0 (Vandermonde) → don't commute

    classical

    -- Parameter values: use natural numbers 0, 1, ..., 2024 as t values
    let t : Index → Real := fun i => (i.val : Real)

    -- v_i = (1, t_i, t_i^2) - points on the moment curve
    let v : Index → Fin 3 → Real := fun i j =>
      match j with
      | 0 => 1
      | 1 => t i
      | 2 => (t i) ^ 2

    -- u_i = v_{i-1} × v_{i+1} (cross product)
    let u : Index → Fin 3 → Real := fun i j =>
      let i1 := i - 1
      let i2 := i + 1
      match j with
      | 0 => v i1 1 * v i2 2 - v i1 2 * v i2 1
      | 1 => v i1 2 * v i2 0 - v i1 0 * v i2 2
      | 2 => v i1 0 * v i2 1 - v i1 1 * v i2 0

    -- A_i = v_i ⊗ u_i (outer product)
    let A : Index → Matrix (Fin 3) (Fin 3) Real := fun i j k => v i j * u i k

    -- Helper: dot product
    let dot : (Fin 3 → Real) → (Fin 3 → Real) → Real :=
      fun a b => a 0 * b 0 + a 1 * b 1 + a 2 * b 2

    -- Key lemma: cross product is orthogonal to its inputs
    have cross_orth_left : ∀ i, dot (u i) (v (i - 1)) = 0 := fun i => by
      simp only [dot, u, v]; ring

    have cross_orth_right : ∀ i, dot (u i) (v (i + 1)) = 0 := fun i => by
      simp only [dot, u, v]; ring

    -- Key algebraic lemma: dot(u_i, v_j) = det(v_{i-1}, v_{i+1}, v_j) is a Vandermonde-like determinant
    -- det = | 1   t_{i-1}   t_{i-1}^2 |
    --       | 1   t_{i+1}   t_{i+1}^2 |
    --       | 1   t_j       t_j^2     |
    -- = (t_{i+1} - t_{i-1})(t_j - t_{i-1})(t_j - t_{i+1})
    have vandermonde_det : ∀ i j,
        dot (u i) (v j) = (t (i + 1) - t (i - 1)) * (t j - t (i - 1)) * (t j - t (i + 1)) := by
      intro i j
      simp only [dot, u, v, t]
      ring

    use A
    intro i j
    constructor
    · -- If they commute, show they're close
      intro hcomm
      by_contra hnotclose
      unfold close at hnotclose
      push_neg at hnotclose
      obtain ⟨hne, hnotsucc, hnotpred⟩ := hnotclose

      -- For non-close i, j: both dot products are nonzero
      -- det = (t_{i+1} - t_{i-1})(t_j - t_{i-1})(t_j - t_{i+1})
      -- This is nonzero when:
      -- - t_{i+1} ≠ t_{i-1} (always true: i+1 ≠ i-1 in ZMod 2025 since 2025 ∤ 2)
      -- - t_j ≠ t_{i-1} (true since j ≠ i-1)
      -- - t_j ≠ t_{i+1} (true since j ≠ i+1)

      have hj_ne_iplus1 : j ≠ i + 1 := hnotsucc
      have hj_ne_iminus1 : j ≠ i - 1 := fun h => hnotpred (by rw [h]; ring)

      -- t values are distinct for distinct indices in ZMod 2025
      have t_inj : ∀ a b : Index, t a = t b → a = b := by
        intro a b hab
        simp only [t] at hab
        -- a.val = b.val as reals, and both are < 2025, so they're equal as naturals
        have h : (a.val : Real) = (b.val : Real) := hab
        have h' : a.val = b.val := by exact Nat.cast_injective h
        exact ZMod.val_injective 2025 h'

      -- Helper: 2 ≠ 0 in ZMod 2025
      have two_ne_zero : (2 : ZMod 2025) ≠ 0 := by decide

      have hui_vj : dot (u i) (v j) ≠ 0 := by
        rw [vandermonde_det]
        -- Need: (t_{i+1} - t_{i-1}) * (t_j - t_{i-1}) * (t_j - t_{i+1}) ≠ 0
        apply mul_ne_zero
        apply mul_ne_zero
        · -- t_{i+1} ≠ t_{i-1}
          intro h
          have heq := t_inj (i + 1) (i - 1) (sub_eq_zero.mp h)
          -- i+1 = i-1 means 2 = 0 in ZMod 2025, contradiction
          have h2 : (2 : ZMod 2025) = 0 := by
            calc (2 : ZMod 2025) = (i + 1) - (i - 1) := by ring
              _ = 0 := by rw [heq]; ring
          exact two_ne_zero h2
        · -- t_j ≠ t_{i-1}
          intro h
          have := t_inj j (i - 1) (sub_eq_zero.mp h)
          exact hj_ne_iminus1 this
        · -- t_j ≠ t_{i+1}
          intro h
          have := t_inj j (i + 1) (sub_eq_zero.mp h)
          exact hj_ne_iplus1 this

      have hi_ne_jplus1 : i ≠ j + 1 := fun h => hnotpred h
      have hi_ne_jminus1 : i ≠ j - 1 := fun h => hnotsucc (by rw [h]; ring)

      have huj_vi : dot (u j) (v i) ≠ 0 := by
        rw [vandermonde_det]
        apply mul_ne_zero
        apply mul_ne_zero
        · -- t_{j+1} ≠ t_{j-1}
          intro h
          have heq := t_inj (j + 1) (j - 1) (sub_eq_zero.mp h)
          have h2 : (2 : ZMod 2025) = 0 := by
            calc (2 : ZMod 2025) = (j + 1) - (j - 1) := by ring
              _ = 0 := by rw [heq]; ring
          exact two_ne_zero h2
        · -- t_i ≠ t_{j-1}
          intro h
          have := t_inj i (j - 1) (sub_eq_zero.mp h)
          exact hi_ne_jminus1 this
        · -- t_i ≠ t_{j+1}
          intro h
          have := t_inj i (j + 1) (sub_eq_zero.mp h)
          exact hi_ne_jplus1 this

      -- Now derive contradiction from commutativity
      -- A_i * A_j = d1 * (v_i ⊗ u_j) where d1 = dot(u_i, v_j) ≠ 0
      -- A_j * A_i = d2 * (v_j ⊗ u_i) where d2 = dot(u_j, v_i) ≠ 0
      -- For equality: d1 * (v_i ⊗ u_j) = d2 * (v_j ⊗ u_i)
      -- Since d1, d2 ≠ 0 and v_i ⊗ u_j, v_j ⊗ u_i are rank-1 matrices,
      -- this implies they must be proportional: v_i ⊗ u_j = c * (v_j ⊗ u_i)
      -- Looking at (0,0) entry: v_i 0 * u_j 0 = c * v_j 0 * u_i 0, i.e., u_j 0 = c * u_i 0
      -- Looking at (1,0) entry: v_i 1 * u_j 0 = c * v_j 1 * u_i 0
      --                        t_i * u_j 0 = c * t_j * u_i 0
      -- If u_j 0 = c * u_i 0 ≠ 0: t_i = t_j, so i = j (contradiction with hne)
      -- If u_j 0 = c * u_i 0 = 0: need to check other entries...

      -- More directly: extract equations from matrix equality
      have h00 := congrFun (congrFun hcomm 0) 0
      have h10 := congrFun (congrFun hcomm 1) 0
      simp only [A, Matrix.mul_apply, Fin.sum_univ_three] at h00 h10

      -- h00: (d1) * v_i 0 * u_j 0 = (d2) * v_j 0 * u_i 0
      --      d1 * 1 * u_j 0 = d2 * 1 * u_i 0
      --      d1 * u_j 0 = d2 * u_i 0 ... (eq1)

      -- h10: d1 * v_i 1 * u_j 0 = d2 * v_j 1 * u_i 0
      --      d1 * t_i * u_j 0 = d2 * t_j * u_i 0 ... (eq2)

      -- From eq1: d1 * u_j 0 = d2 * u_i 0
      -- Substitute into eq2: d1 * t_i * u_j 0 = d2 * t_j * u_i 0
      --                      t_i * (d1 * u_j 0) = t_j * (d2 * u_i 0)
      --                      t_i * (d2 * u_i 0) = t_j * (d2 * u_i 0) [using eq1]
      --                      d2 * u_i 0 * (t_i - t_j) = 0

      -- Since d2 ≠ 0, either u_i 0 = 0 or t_i = t_j.
      -- If t_i = t_j, then i = j (contradiction).
      -- If u_i 0 = 0, then from eq1: d1 * u_j 0 = 0, so u_j 0 = 0 (since d1 ≠ 0).

      -- Check other entries: (0,1) and (1,1) to get similar constraints...
      -- Eventually leads to all components matching, which gives i = j.

      -- Define d1 and d2 as the dot products (not using `let` to avoid issues)
      -- d1 = dot (u i) (v j), d2 = dot (u j) (v i)

      -- Expand h00: the matrix product formula gives
      -- sum_k (v i 0 * u i k * v j k * u j 0) = sum_k (v j 0 * u j k * v i k * u i 0)
      -- Factoring: v i 0 * (sum_k u i k * v j k) * u j 0 = v j 0 * (sum_k u j k * v i k) * u i 0
      -- Since v i 0 = v j 0 = 1:
      -- (u i 0 * v j 0 + u i 1 * v j 1 + u i 2 * v j 2) * u j 0
      -- = (u j 0 * v i 0 + u j 1 * v i 1 + u j 2 * v i 2) * u i 0

      have eq1 : (dot (u i) (v j)) * (u j 0) = (dot (u j) (v i)) * (u i 0) := by
        simp only [dot, v]
        -- h00 gives: 1 * u i 0 * (1 * u j 0) + 1 * u i 1 * (t j * u j 0) + 1 * u i 2 * ((t j)^2 * u j 0)
        --          = 1 * u j 0 * (1 * u i 0) + 1 * u j 1 * (t i * u i 0) + 1 * u j 2 * ((t i)^2 * u i 0)
        -- Simplifying: (u i 0 + u i 1 * t j + u i 2 * (t j)^2) * u j 0
        --            = (u j 0 + u j 1 * t i + u j 2 * (t i)^2) * u i 0
        linarith [h00]

      -- Similarly for h10
      have eq2 : (dot (u i) (v j)) * (t i) * (u j 0) = (dot (u j) (v i)) * (t j) * (u i 0) := by
        simp only [dot, v]
        -- h10: t_i * u i 0 * (1 * u j 0) + t_i * u i 1 * (t_j * u j 0) + t_i * u i 2 * (t_j^2 * u j 0)
        --    = t_j * u j 0 * (1 * u i 0) + t_j * u j 1 * (t_i * u i 0) + t_j * u j 2 * (t_i^2 * u i 0)
        linarith [h10]

      -- From eq1 and eq2: derive t_i = t_j or u_i 0 = u_j 0 = 0
      have key : (dot (u j) (v i)) * (u i 0) * (t i - t j) = 0 := by
        have h := eq2
        have h' := eq1
        -- From eq1: (dot u_i v_j) * u_j 0 = (dot u_j v_i) * u_i 0
        -- From eq2: (dot u_i v_j) * t_i * u_j 0 = (dot u_j v_i) * t_j * u_i 0
        -- Multiply eq1 by t_i: (dot u_i v_j) * t_i * u_j 0 = (dot u_j v_i) * u_i 0 * t_i
        -- So: (dot u_j v_i) * t_j * u_i 0 = (dot u_j v_i) * u_i 0 * t_i
        -- (dot u_j v_i) * u_i 0 * (t_i - t_j) = 0
        have h'' : (dot (u i) (v j)) * t i * u j 0 = (dot (u j) (v i)) * u i 0 * t i := by
          calc (dot (u i) (v j)) * t i * u j 0
              = ((dot (u i) (v j)) * u j 0) * t i := by ring
            _ = ((dot (u j) (v i)) * u i 0) * t i := by rw [h']
            _ = (dot (u j) (v i)) * u i 0 * t i := by ring
        calc (dot (u j) (v i)) * u i 0 * (t i - t j)
            = (dot (u j) (v i)) * u i 0 * t i - (dot (u j) (v i)) * t j * u i 0 := by ring
          _ = (dot (u i) (v j)) * t i * u j 0 - (dot (u j) (v i)) * t j * u i 0 := by rw [h'']
          _ = 0 := by linarith [h]

      -- d2 ≠ 0, so either u i 0 = 0 or t i = t j
      cases mul_eq_zero.mp key with
      | inl h =>
        cases mul_eq_zero.mp h with
        | inl hd2_zero => exact huj_vi hd2_zero
        | inr hui0_zero =>
          -- u i 0 = 0, and from eq1: d1 * u j 0 = 0, so u j 0 = 0 (since d1 ≠ 0)
          have huj0_zero : u j 0 = 0 := by
            have h' := eq1
            rw [hui0_zero, mul_zero] at h'
            -- h' : dot (u i) (v j) * u j 0 = 0
            cases mul_eq_zero.mp h' with
            | inl hd1_zero => exact absurd hd1_zero hui_vj
            | inr h'' => exact h''
          -- Now check (0,1) and (1,1) entries
          have h01 := congrFun (congrFun hcomm 0) 1
          have h11 := congrFun (congrFun hcomm 1) 1
          simp only [A, Matrix.mul_apply, Fin.sum_univ_three] at h01 h11

          have eq1' : (dot (u i) (v j)) * (u j 1) = (dot (u j) (v i)) * (u i 1) := by
            simp only [dot, v]
            linarith [h01]

          have eq2' : (dot (u i) (v j)) * (t i) * (u j 1) = (dot (u j) (v i)) * (t j) * (u i 1) := by
            simp only [dot, v]
            linarith [h11]

          have key' : (dot (u j) (v i)) * (u i 1) * (t i - t j) = 0 := by
            have h'' : (dot (u i) (v j)) * t i * u j 1 = (dot (u j) (v i)) * u i 1 * t i := by
              calc (dot (u i) (v j)) * t i * u j 1
                  = ((dot (u i) (v j)) * u j 1) * t i := by ring
                _ = ((dot (u j) (v i)) * u i 1) * t i := by rw [eq1']
                _ = (dot (u j) (v i)) * u i 1 * t i := by ring
            calc (dot (u j) (v i)) * u i 1 * (t i - t j)
                = (dot (u j) (v i)) * u i 1 * t i - (dot (u j) (v i)) * t j * u i 1 := by ring
              _ = (dot (u i) (v j)) * t i * u j 1 - (dot (u j) (v i)) * t j * u i 1 := by rw [h'']
              _ = 0 := by linarith [eq2']

          cases mul_eq_zero.mp key' with
          | inl h' =>
            cases mul_eq_zero.mp h' with
            | inl hd2_zero' => exact huj_vi hd2_zero'
            | inr hui1_zero =>
              -- u i 0 = 0 and u i 1 = 0. Check u i 2.
              have huj1_zero : u j 1 = 0 := by
                have h'' := eq1'
                rw [hui1_zero, mul_zero] at h''
                -- h'' : dot (u i) (v j) * u j 1 = 0
                cases mul_eq_zero.mp h'' with
                | inl hd1_zero => exact absurd hd1_zero hui_vj
                | inr h''' => exact h'''
              -- Now both u_i and u_j have components 0 = 0, 1 = 0
              -- Check (0,2) entry
              have h02 := congrFun (congrFun hcomm 0) 2
              simp only [A, Matrix.mul_apply, Fin.sum_univ_three] at h02

              have eq1'' : (dot (u i) (v j)) * (u j 2) = (dot (u j) (v i)) * (u i 2) := by
                simp only [dot, v]
                linarith [h02]

              -- dot (u i) (v j) = u i 0 * 1 + u i 1 * t_j + u i 2 * t_j^2
              --                 = 0 * 1 + 0 * t_j + u i 2 * t_j^2 = u i 2 * t_j^2
              have hd1_simp : dot (u i) (v j) = u i 2 * (t j)^2 := by
                simp only [dot, hui0_zero, hui1_zero, v]
                ring

              -- Similarly dot (u j) (v i) = u j 2 * t_i^2
              have hd2_simp : dot (u j) (v i) = u j 2 * (t i)^2 := by
                simp only [dot, huj0_zero, huj1_zero, v]
                ring

              have hui2_ne : u i 2 ≠ 0 := by
                intro h
                rw [h, zero_mul] at hd1_simp
                exact hui_vj hd1_simp

              have huj2_ne : u j 2 ≠ 0 := by
                intro h
                rw [h, zero_mul] at hd2_simp
                exact huj_vi hd2_simp

              have h_eq : (t j)^2 = (t i)^2 := by
                have h := eq1''
                rw [hd1_simp, hd2_simp] at h
                -- u i 2 * t_j^2 * u j 2 = u j 2 * t_i^2 * u i 2
                have : u i 2 * (t j)^2 * u j 2 - u j 2 * (t i)^2 * u i 2 = 0 := by linarith
                have hfactor : u i 2 * u j 2 * ((t j)^2 - (t i)^2) = 0 := by linarith
                cases mul_eq_zero.mp hfactor with
                | inl hmul =>
                  cases mul_eq_zero.mp hmul with
                  | inl => exact absurd ‹u i 2 = 0› hui2_ne
                  | inr => exact absurd ‹u j 2 = 0› huj2_ne
                | inr hsub => linarith

              -- t_j^2 = t_i^2 and t values are nonnegative, so t_j = t_i
              have ti_nonneg : 0 ≤ t i := Nat.cast_nonneg _
              have tj_nonneg : 0 ≤ t j := Nat.cast_nonneg _
              have h_eq' : t j = t i := (sq_eq_sq₀ tj_nonneg ti_nonneg).mp h_eq
              exact hne (t_inj j i h_eq').symm
          | inr hdiff => exact hne (t_inj i j (sub_eq_zero.mp hdiff))
      | inr hdiff => exact hne (t_inj i j (sub_eq_zero.mp hdiff))

    · -- If they're close, show they commute
      intro hclose
      rcases hclose with rfl | hsucc | hpred
      · -- i = j: trivially commute
        rfl
      · -- j = i + 1
        subst hsucc
        -- A_i * A_{i+1} = (u_i · v_{i+1}) * (v_i ⊗ u_{i+1}) = 0 * ... = 0
        -- A_{i+1} * A_i = (u_{i+1} · v_i) * (v_{i+1} ⊗ u_i) = 0 * ... = 0
        have h1 : dot (u i) (v (i + 1)) = 0 := cross_orth_right i
        -- dot (u (i+1)) (v i) = dot (u (i+1)) (v ((i+1)-1)) = cross_orth_left (i+1)
        have h2 : dot (u (i + 1)) (v i) = 0 := by
          have := cross_orth_left (i + 1)
          simp only [add_sub_cancel_right] at this
          exact this
        ext r s
        simp only [A, Matrix.mul_apply, Fin.sum_univ_three]
        -- Both products factor through the dot product which is zero
        simp only [dot] at h1 h2
        -- The matrix product (A i * A (i+1))_{r,s} equals
        -- v_i[r] * (sum_t u_i[t] * v_{i+1}[t]) * u_{i+1}[s]
        -- = v_i[r] * (u_i · v_{i+1}) * u_{i+1}[s] = v_i[r] * 0 * u_{i+1}[s] = 0
        -- Similarly for the other product.
        calc v i r * u i 0 * (v (i + 1) 0 * u (i + 1) s) +
             v i r * u i 1 * (v (i + 1) 1 * u (i + 1) s) +
             v i r * u i 2 * (v (i + 1) 2 * u (i + 1) s)
           = v i r * u (i + 1) s * (u i 0 * v (i + 1) 0 + u i 1 * v (i + 1) 1 + u i 2 * v (i + 1) 2) := by ring
         _ = v i r * u (i + 1) s * 0 := by rw [h1]
         _ = 0 := by ring
         _ = v (i + 1) r * u i s * 0 := by ring
         _ = v (i + 1) r * u i s * (u (i + 1) 0 * v i 0 + u (i + 1) 1 * v i 1 + u (i + 1) 2 * v i 2) := by rw [h2]
         _ = v (i + 1) r * u (i + 1) 0 * (v i 0 * u i s) +
             v (i + 1) r * u (i + 1) 1 * (v i 1 * u i s) +
             v (i + 1) r * u (i + 1) 2 * (v i 2 * u i s) := by ring
      · -- i = j + 1 (symmetric case)
        subst hpred
        have h1 : dot (u j) (v (j + 1)) = 0 := cross_orth_right j
        have h2 : dot (u (j + 1)) (v j) = 0 := by
          have := cross_orth_left (j + 1)
          simp only [add_sub_cancel_right] at this
          exact this
        ext r s
        simp only [A, Matrix.mul_apply, Fin.sum_univ_three]
        simp only [dot] at h1 h2
        calc v (j + 1) r * u (j + 1) 0 * (v j 0 * u j s) +
             v (j + 1) r * u (j + 1) 1 * (v j 1 * u j s) +
             v (j + 1) r * u (j + 1) 2 * (v j 2 * u j s)
           = v (j + 1) r * u j s * (u (j + 1) 0 * v j 0 + u (j + 1) 1 * v j 1 + u (j + 1) 2 * v j 2) := by ring
         _ = v (j + 1) r * u j s * 0 := by rw [h2]
         _ = 0 := by ring
         _ = v j r * u (j + 1) s * 0 := by ring
         _ = v j r * u (j + 1) s * (u j 0 * v (j + 1) 0 + u j 1 * v (j + 1) 1 + u j 2 * v (j + 1) 2) := by rw [h1]
         _ = v j r * u j 0 * (v (j + 1) 0 * u (j + 1) s) +
             v j r * u j 1 * (v (j + 1) 1 * u (j + 1) s) +
             v j r * u j 2 * (v (j + 1) 2 * u (j + 1) s) := by ring

  · -- Part 2: k = 2 is impossible
    intro ⟨A, hA⟩
    have hclose12 : close 1 2 := by unfold close; right; left; rfl
    have hclose23 : close 2 3 := by unfold close; right; left; rfl
    have hnotclose13 : ¬close 1 3 := by
      unfold close; push_neg; constructor
      · intro h; cases h
      · constructor <;> (intro h; cases h)

    have h12 : A 1 * A 2 = A 2 * A 1 := (hA 1 2).mpr hclose12
    have h21 : A 2 * A 1 = A 1 * A 2 := h12.symm
    have h23 : A 2 * A 3 = A 3 * A 2 := (hA 2 3).mpr hclose23
    have h13 : A 1 * A 3 ≠ A 3 * A 1 := by
      intro heq; exact hnotclose13 ((hA 1 3).mp heq)

    have hA2_scalar := commutes_with_noncommuting_implies_scalar (A 2) (A 1) (A 3) h21 h23 h13

    have hclose34 : close 3 4 := by unfold close; right; left; rfl
    have hnotclose24 : ¬close 2 4 := by
      unfold close; push_neg; constructor
      · intro h; cases h
      · constructor <;> (intro h; cases h)

    have h24 : A 2 * A 4 ≠ A 4 * A 2 := by
      intro heq; exact hnotclose24 ((hA 2 4).mp heq)

    obtain ⟨c2, hc2⟩ := hA2_scalar
    have h24_comm : A 2 * A 4 = A 4 * A 2 := by
      rw [hc2]
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    exact h24 h24_comm

end Putnam2025A4
