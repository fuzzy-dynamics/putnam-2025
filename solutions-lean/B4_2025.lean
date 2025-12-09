/-
Putnam 2025 Problem B4 - Complete Proof

For n >= 2, prove 3S <= (n+2)N.

The proof uses:
1. Horizontal bound: 2*s_i <= x_i*(x_i+1)
2. Vertical bound: s_i <= C_i (cumulative nonzeros up to row i)
3. Key algebraic lemma combining these
4. Row-by-row summation with double counting
-/

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card

open Finset BigOperators

/-
The problem conditions (using 1-indexed i,j from 1 to n):
(a) a_{i,j} = 0 when i + j ≤ n
(b) a_{i+1,j} ∈ {a_{i,j}, a_{i,j}+1}
(c) a_{i,j+1} ∈ {a_{i,j}, a_{i,j}+1}

In 0-indexed terms (Fin n with i,j from 0 to n-1):
(a) a_{i,j} = 0 when (i+1) + (j+1) ≤ n, i.e., i + j + 2 ≤ n
(b) a_{i+1,j} - a_{i,j} ∈ {0, 1}, i.e., a_{i,j} ≤ a_{i+1,j} ≤ a_{i,j} + 1
(c) a_{i,j+1} - a_{i,j} ∈ {0, 1}, i.e., a_{i,j} ≤ a_{i,j+1} ≤ a_{i,j} + 1

The proof works for the more general condition |diff| ≤ 1 (entries can decrease by 1),
which includes the original problem as a special case. We prove for this weaker condition.
-/
structure ValidMatrix (n : Nat) where
  a : Fin n → Fin n → Nat
  zero_region : ∀ i j : Fin n, i.val + j.val + 2 ≤ n → a i j = 0
  vert_diff : ∀ i j : Fin n, (hi : i.val + 1 < n) →
    let i' : Fin n := ⟨i.val + 1, hi⟩
    (a i' j : Int) - (a i j : Int) ≤ 1 ∧ (a i j : Int) - (a i' j : Int) ≤ 1
  horiz_diff : ∀ i j : Fin n, (hj : j.val + 1 < n) →
    let j' : Fin n := ⟨j.val + 1, hj⟩
    (a i j' : Int) - (a i j : Int) ≤ 1 ∧ (a i j : Int) - (a i j' : Int) ≤ 1

/-
Original problem structure with exact conditions (non-decreasing).
Any matrix satisfying these conditions also satisfies ValidMatrix.
-/
structure PutnamB4Matrix (n : Nat) where
  a : Fin n → Fin n → Nat
  zero_region : ∀ i j : Fin n, i.val + j.val + 2 ≤ n → a i j = 0
  vert_nondec : ∀ i j : Fin n, (hi : i.val + 1 < n) →
    let i' : Fin n := ⟨i.val + 1, hi⟩
    a i j ≤ a i' j ∧ a i' j ≤ a i j + 1
  horiz_nondec : ∀ i j : Fin n, (hj : j.val + 1 < n) →
    let j' : Fin n := ⟨j.val + 1, hj⟩
    a i j ≤ a i j' ∧ a i j' ≤ a i j + 1

/-- Convert a PutnamB4Matrix to a ValidMatrix (the weaker condition) -/
def PutnamB4Matrix.toValidMatrix (A : PutnamB4Matrix n) : ValidMatrix n where
  a := A.a
  zero_region := A.zero_region
  vert_diff := fun i j hi => by
    have h := A.vert_nondec i j hi
    constructor <;> omega
  horiz_diff := fun i j hj => by
    have h := A.horiz_nondec i j hj
    constructor <;> omega

variable {n : Nat}

def rowSum (A : ValidMatrix n) (i : Fin n) : Nat := ∑ j : Fin n, A.a i j
def rowNonzeroCount (A : ValidMatrix n) (i : Fin n) : Nat := (univ.filter (fun j : Fin n => A.a i j ≠ 0)).card
def totalSum (A : ValidMatrix n) : Nat := ∑ i : Fin n, rowSum A i
def countNonzero (A : ValidMatrix n) : Nat := ∑ i : Fin n, rowNonzeroCount A i
def cumNonzeroCount (A : ValidMatrix n) (i : Fin n) : Nat :=
  ∑ k ∈ univ.filter (fun k : Fin n => k.val ≤ i.val), rowNonzeroCount A k

-- Entry at boundary is at most 1 (using horizontal predecessor)
-- hj_succ : j.val = pred.val + 1
lemma entry_boundary_horiz (_hn : n ≥ 2) (A : ValidMatrix n) (i : Fin n)
    (pred j : Fin n) (hj_succ : j.val = pred.val + 1) (hpred_lt : pred.val + 1 < n)
    (hprev_zero : A.a i pred = 0) :
    A.a i j ≤ 1 := by
  have hdiff := A.horiz_diff i pred hpred_lt
  have hj_eq : (⟨pred.val + 1, hpred_lt⟩ : Fin n) = j := Fin.ext (by simp; omega)
  rw [hj_eq] at hdiff
  simp only [hprev_zero, Nat.cast_zero, sub_zero] at hdiff
  omega

-- Entry at boundary is at most 1 (using vertical predecessor)
lemma entry_boundary_vert (_hn : n ≥ 2) (A : ValidMatrix n) (j : Fin n)
    (pred i : Fin n) (hi_succ : i.val = pred.val + 1) (hpred_lt : pred.val + 1 < n)
    (hprev_zero : A.a pred j = 0) :
    A.a i j ≤ 1 := by
  have hdiff := A.vert_diff pred j hpred_lt
  have hi_eq : (⟨pred.val + 1, hpred_lt⟩ : Fin n) = i := Fin.ext (by simp; omega)
  rw [hi_eq] at hdiff
  simp only [hprev_zero, Nat.cast_zero, sub_zero] at hdiff
  omega

-- Entry bounded by count of nonzeros to its left (horizontal rank)
lemma entry_le_horiz_rank_aux (hn : n ≥ 2) (A : ValidMatrix n) (i : Fin n)
    (nz : Finset (Fin n)) (hnz : nz = univ.filter (fun j : Fin n => A.a i j ≠ 0)) :
    ∀ d : Nat, ∀ j : Fin n, j.val = d → j ∈ nz →
    A.a i j ≤ (nz.filter (fun k => k.val ≤ j.val)).card := by
  intro d
  induction d with
  | zero =>
    intro j hj_val hj_mem
    subst hnz
    simp only [mem_filter, mem_univ, true_and] at hj_mem
    -- j.val = 0, so position is (i, 0). For this to be nonzero, need i + 0 + 2 > n, so i >= n-1
    have hi_large : i.val ≥ n - 1 := by
      by_contra hcontra; push_neg at hcontra
      have hzero := A.zero_region i j (by omega)
      exact hj_mem hzero
    have hi_eq : i.val = n - 1 := by omega
    -- Use vertical predecessor
    have hpred_lt : n - 2 < n := by omega
    have hpred_succ_lt : n - 2 + 1 < n := by omega
    have hprev_zero := A.zero_region ⟨n - 2, hpred_lt⟩ j (by omega : n - 2 + j.val + 2 ≤ n)
    have hdiff := A.vert_diff ⟨n - 2, hpred_lt⟩ j hpred_succ_lt
    have hi_eq' : (⟨n - 2 + 1, hpred_succ_lt⟩ : Fin n) = i := Fin.ext (by simp; omega)
    rw [hi_eq'] at hdiff
    simp only [hprev_zero, Nat.cast_zero, sub_zero] at hdiff
    have ha_le : A.a i j ≤ 1 := by omega
    have hj_in : j ∈ (univ.filter (fun k : Fin n => A.a i k ≠ 0)).filter (fun k => k.val ≤ j.val) := by
      simp only [mem_filter, mem_univ, true_and]; exact ⟨hj_mem, le_refl _⟩
    have hcard_ge : 1 ≤ ((univ.filter (fun k : Fin n => A.a i k ≠ 0)).filter (fun k => k.val ≤ j.val)).card :=
      card_pos.mpr ⟨j, hj_in⟩
    omega
  | succ d ih =>
    intro j hj_val hj_mem
    subst hnz
    simp only [mem_filter, mem_univ, true_and] at hj_mem
    -- j.val = d + 1
    have hj_pred_lt : d < n := by omega
    let jm : Fin n := ⟨d, hj_pred_lt⟩
    have hj_succ : j.val = jm.val + 1 := by simp only [jm]; omega
    by_cases hjm_zero : A.a i jm = 0
    · -- Previous column is zero: use boundary lemma
      have ha_le := entry_boundary_horiz hn A i jm j hj_succ (by omega) hjm_zero
      have hj_in : j ∈ (univ.filter (fun k : Fin n => A.a i k ≠ 0)).filter (fun k => k.val ≤ j.val) := by
        simp only [mem_filter, mem_univ, true_and]; exact ⟨hj_mem, le_refl _⟩
      have hcard_ge : 1 ≤ ((univ.filter (fun k : Fin n => A.a i k ≠ 0)).filter (fun k => k.val ≤ j.val)).card :=
        card_pos.mpr ⟨j, hj_in⟩
      omega
    · -- Previous column is nonzero: use IH
      have hjm_mem : jm ∈ univ.filter (fun k : Fin n => A.a i k ≠ 0) := by
        simp only [mem_filter, mem_univ, true_and]; exact hjm_zero
      have ih_result := ih jm rfl hjm_mem
      -- Entry increases by at most 1
      have hdiff := A.horiz_diff i jm (by simp only [jm]; omega : jm.val + 1 < n)
      have hj_eq : (⟨jm.val + 1, by omega⟩ : Fin n) = j := by ext; simp only [jm]; omega
      rw [hj_eq] at hdiff
      have hstep : (A.a i j : Int) - (A.a i jm : Int) ≤ 1 := hdiff.1
      -- Count increases by 1
      have hcount_inc : ((univ.filter (fun k : Fin n => A.a i k ≠ 0)).filter (fun k => k.val ≤ j.val)).card =
          ((univ.filter (fun k : Fin n => A.a i k ≠ 0)).filter (fun k => k.val ≤ jm.val)).card + 1 := by
        have hsplit : (univ.filter (fun k : Fin n => A.a i k ≠ 0)).filter (fun k => k.val ≤ j.val) =
            ((univ.filter (fun k : Fin n => A.a i k ≠ 0)).filter (fun k => k.val ≤ jm.val)) ∪ {j} := by
          ext k
          simp only [mem_filter, mem_union, mem_singleton, mem_univ, true_and, jm]
          constructor
          · intro ⟨hk_nz, hk_le⟩
            by_cases hk_le' : k.val ≤ d
            · left; exact ⟨hk_nz, hk_le'⟩
            · right; ext; omega
          · intro hcase
            cases hcase with
            | inl h => exact ⟨h.1, by omega⟩
            | inr h => subst h; exact ⟨hj_mem, le_refl _⟩
        rw [hsplit, card_union_of_disjoint]
        · simp
        · simp only [disjoint_singleton_right, mem_filter, mem_univ, true_and, not_and, not_le, jm]
          intro _; omega
      omega

lemma entry_le_horiz_rank (hn : n ≥ 2) (A : ValidMatrix n) (i : Fin n)
    (nz : Finset (Fin n)) (hnz : nz = univ.filter (fun j : Fin n => A.a i j ≠ 0))
    (j : Fin n) (hj : j ∈ nz) :
    A.a i j ≤ (nz.filter (fun k => k.val ≤ j.val)).card :=
  entry_le_horiz_rank_aux hn A i nz hnz j.val j rfl hj

-- Entry bounded by count of nonzeros above (vertical count)
lemma entry_le_vert_count_aux (hn : n ≥ 2) (A : ValidMatrix n) (j : Fin n) :
    ∀ d : Nat, ∀ i : Fin n, i.val = d → i.val + j.val + 2 > n →
    A.a i j ≤ (univ.filter (fun k : Fin n => k.val ≤ i.val ∧ A.a k j ≠ 0)).card := by
  intro d
  induction d with
  | zero =>
    intro i hi_val hregion
    by_cases ha_zero : A.a i j = 0
    · simp [ha_zero]
    · -- i.val = 0 and nonzero means j.val = n - 1
      have hj_eq : j.val = n - 1 := by omega
      -- Use horizontal predecessor
      have hpred_lt : n - 2 < n := by omega
      have hpred_succ_lt : n - 2 + 1 < n := by omega
      have hprev_zero := A.zero_region i ⟨n - 2, hpred_lt⟩ (by omega : i.val + (n - 2) + 2 ≤ n)
      have hdiff := A.horiz_diff i ⟨n - 2, hpred_lt⟩ hpred_succ_lt
      have hj_eq' : (⟨n - 2 + 1, hpred_succ_lt⟩ : Fin n) = j := Fin.ext (by simp; omega)
      rw [hj_eq'] at hdiff
      simp only [hprev_zero, Nat.cast_zero, sub_zero] at hdiff
      have ha_le : A.a i j ≤ 1 := by omega
      have hi_in : i ∈ univ.filter (fun k : Fin n => k.val ≤ i.val ∧ A.a k j ≠ 0) := by
        simp only [mem_filter, mem_univ, true_and]; exact ⟨le_refl _, ha_zero⟩
      have hcard_ge : 1 ≤ (univ.filter (fun k : Fin n => k.val ≤ i.val ∧ A.a k j ≠ 0)).card :=
        card_pos.mpr ⟨i, hi_in⟩
      omega
  | succ d ih =>
    intro i hi_val hregion
    by_cases ha_zero : A.a i j = 0
    · simp [ha_zero]
    · have hi_pred_lt : d < n := by omega
      let im : Fin n := ⟨d, hi_pred_lt⟩
      have hi_succ : i.val = im.val + 1 := by simp only [im]; omega
      by_cases him_zero : A.a im j = 0
      · -- Previous row is zero: use boundary lemma
        have ha_le := entry_boundary_vert hn A j im i hi_succ (by simp only [im]; omega) him_zero
        have hi_in : i ∈ univ.filter (fun k : Fin n => k.val ≤ i.val ∧ A.a k j ≠ 0) := by
          simp only [mem_filter, mem_univ, true_and]; exact ⟨le_refl _, ha_zero⟩
        have hcard_ge : 1 ≤ (univ.filter (fun k : Fin n => k.val ≤ i.val ∧ A.a k j ≠ 0)).card :=
          card_pos.mpr ⟨i, hi_in⟩
        omega
      · -- Previous row is nonzero: use IH
        have hregion' : im.val + j.val + 2 > n := by
          by_contra hcontra; push_neg at hcontra
          have hzero := A.zero_region im j hcontra
          exact him_zero hzero
        have ih_result := ih im rfl hregion'
        -- Entry increases by at most 1
        have hdiff := A.vert_diff im j (by simp only [im]; omega : im.val + 1 < n)
        have hi_eq : (⟨im.val + 1, by omega⟩ : Fin n) = i := by ext; simp only [im]; omega
        rw [hi_eq] at hdiff
        have hstep : (A.a i j : Int) - (A.a im j : Int) ≤ 1 := hdiff.1
        -- Count increases by 1
        have hcount_inc : (univ.filter (fun k : Fin n => k.val ≤ i.val ∧ A.a k j ≠ 0)).card =
            (univ.filter (fun k : Fin n => k.val ≤ im.val ∧ A.a k j ≠ 0)).card + 1 := by
          have hsplit : univ.filter (fun k : Fin n => k.val ≤ i.val ∧ A.a k j ≠ 0) =
              (univ.filter (fun k : Fin n => k.val ≤ im.val ∧ A.a k j ≠ 0)) ∪ {i} := by
            ext k
            simp only [mem_filter, mem_univ, true_and, mem_union, mem_singleton, im]
            constructor
            · intro ⟨hk_le, hk_nz⟩
              by_cases hk_le' : k.val ≤ d
              · left; exact ⟨hk_le', hk_nz⟩
              · right; ext; omega
            · intro hcase
              cases hcase with
              | inl h => exact ⟨by omega, h.2⟩
              | inr h => subst h; exact ⟨le_refl _, ha_zero⟩
          rw [hsplit, card_union_of_disjoint]
          · simp
          · simp only [disjoint_singleton_right, mem_filter, mem_univ, true_and, not_and, im]
            intro hle _; omega
        omega

lemma entry_le_vert_count (hn : n ≥ 2) (A : ValidMatrix n) (i j : Fin n)
    (hregion : i.val + j.val + 2 > n) :
    A.a i j ≤ (univ.filter (fun k : Fin n => k.val ≤ i.val ∧ A.a k j ≠ 0)).card :=
  entry_le_vert_count_aux hn A j i.val i rfl hregion

-- Sum from 1 to m
lemma sum_Icc_one_to_m (m : Nat) : ∑ r ∈ Finset.Icc 1 m, r = m * (m + 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext x; simp only [Finset.mem_Icc, mem_insert]
      omega
    rw [hsplit, sum_insert (by simp), ih]
    have hdiv : 2 ∣ m * (m + 1) := Even.two_dvd (Nat.even_mul_succ_self m)
    obtain ⟨t, ht⟩ := hdiv
    rw [ht, Nat.mul_div_cancel_left t (by omega)]
    have h2t : 2 * t = m * (m + 1) := ht.symm
    have hprod : (m + 1) * (m + 2) = 2 * (t + (m + 1)) := by nlinarith
    have hdiv' : 2 ∣ (m + 1) * (m + 2) := ⟨t + (m + 1), hprod⟩
    rw [hprod, Nat.mul_div_cancel_left _ (by omega)]
    ring

-- Horizontal bound: 2*s_i <= x_i*(x_i+1)
lemma horizontal_bound (hn : n ≥ 2) (A : ValidMatrix n) (i : Fin n) :
    2 * rowSum A i ≤ rowNonzeroCount A i * (rowNonzeroCount A i + 1) := by
  unfold rowSum rowNonzeroCount
  set nz := univ.filter (fun j : Fin n => A.a i j ≠ 0) with hnz_def
  have hsum_eq : ∑ j : Fin n, A.a i j = ∑ j ∈ nz, A.a i j := by
    symm; apply sum_subset
    · intro j _; exact mem_univ j
    · intro j _ hjnot
      simp only [nz, mem_filter, mem_univ, true_and, ne_eq, not_not] at hjnot
      exact hjnot
  rw [hsum_eq]
  by_cases hnz_empty : nz.card = 0
  · simp [Finset.card_eq_zero.mp hnz_empty]
  · have hcard_pos : 0 < nz.card := Nat.pos_of_ne_zero hnz_empty
    -- Each entry bounded by its rank
    have hentry_le : ∀ j ∈ nz, A.a i j ≤ (nz.filter (fun k => k.val ≤ j.val)).card :=
      fun j hj => entry_le_horiz_rank hn A i nz hnz_def j hj
    -- Ranks are strictly monotone
    have hrank_strict : ∀ j1 j2 : Fin n, j1 ∈ nz → j2 ∈ nz → j1.val < j2.val →
        (nz.filter (fun k => k.val ≤ j1.val)).card < (nz.filter (fun k => k.val ≤ j2.val)).card := by
      intro j1 j2 hj1 hj2 hlt
      apply card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      constructor
      · intro k hk; simp only [mem_filter] at hk ⊢; exact ⟨hk.1, by omega⟩
      · intro heq_set
        have hj2_in : j2 ∈ nz.filter (fun k => k.val ≤ j2.val) := by
          simp only [mem_filter]; exact ⟨hj2, le_refl _⟩
        have hj2_not : j2 ∉ nz.filter (fun k => k.val ≤ j1.val) := by
          simp only [mem_filter, not_and, not_le]; intro _; exact hlt
        rw [heq_set] at hj2_not; exact hj2_not hj2_in
    -- Rank function is injective on nz
    let rankFn : Fin n → Nat := fun j => (nz.filter (fun k => k.val ≤ j.val)).card
    have hrankFn_inj : ∀ j1 ∈ nz, ∀ j2 ∈ nz, rankFn j1 = rankFn j2 → j1 = j2 := by
      intro j1 hj1 j2 hj2 heq
      by_contra hne
      have htric : j1.val < j2.val ∨ j1.val > j2.val := by
        rcases Nat.lt_trichotomy j1.val j2.val with h | h | h
        · left; exact h
        · exfalso; apply hne; ext; exact h
        · right; exact h
      rcases htric with hlt | hgt
      · have hstrict := hrank_strict j1 j2 hj1 hj2 hlt
        simp only [rankFn] at heq; omega
      · have hstrict := hrank_strict j2 j1 hj2 hj1 hgt
        simp only [rankFn] at heq; omega
    -- Sum of entries ≤ sum of ranks
    have hsum_le : ∑ j ∈ nz, A.a i j ≤ ∑ j ∈ nz, rankFn j :=
      sum_le_sum (fun j hj => hentry_le j hj)
    -- Ranks range from 1 to m
    have hrank_range : ∀ j ∈ nz, 1 ≤ rankFn j ∧ rankFn j ≤ nz.card := by
      intro j hj; constructor
      · exact card_pos.mpr ⟨j, by simp [hj]⟩
      · exact card_filter_le _ _
    have himage_card : (nz.image rankFn).card = nz.card := by
      rw [card_image_of_injOn]
      exact fun j1 hj1 j2 hj2 heq => hrankFn_inj j1 hj1 j2 hj2 heq
    have himage_subset : nz.image rankFn ⊆ Finset.Icc 1 nz.card := by
      intro r hr
      simp only [mem_image] at hr
      obtain ⟨j, hj, hr_eq⟩ := hr
      simp only [Finset.mem_Icc]
      rw [← hr_eq]
      exact hrank_range j hj
    have himage_eq : nz.image rankFn = Finset.Icc 1 nz.card := by
      apply Finset.eq_of_subset_of_card_le himage_subset
      rw [Nat.card_Icc, himage_card]
      omega
    have hsum_ranks : ∑ j ∈ nz, rankFn j = ∑ r ∈ Finset.Icc 1 nz.card, r := by
      rw [← himage_eq]
      rw [sum_image]
      exact fun j1 hj1 j2 hj2 heq => hrankFn_inj j1 hj1 j2 hj2 heq
    -- Sum 1 + 2 + ... + m = m(m+1)/2
    have harith : ∑ r ∈ Finset.Icc 1 nz.card, r = nz.card * (nz.card + 1) / 2 :=
      sum_Icc_one_to_m nz.card
    -- 2 * (m(m+1)/2) ≤ m(m+1)
    have hdiv2 : 2 ∣ nz.card * (nz.card + 1) := Even.two_dvd (Nat.even_mul_succ_self nz.card)
    have hsum_bound : ∑ j ∈ nz, rankFn j = nz.card * (nz.card + 1) / 2 := by
      rw [hsum_ranks, harith]
    calc 2 * ∑ j ∈ nz, A.a i j
        ≤ 2 * ∑ j ∈ nz, rankFn j := Nat.mul_le_mul_left 2 hsum_le
      _ = 2 * (nz.card * (nz.card + 1) / 2) := by rw [hsum_bound]
      _ = nz.card * (nz.card + 1) := Nat.mul_div_cancel' hdiv2

-- Vertical bound: s_i <= C_i
lemma vertical_bound (hn : n ≥ 2) (A : ValidMatrix n) (i : Fin n) :
    rowSum A i ≤ cumNonzeroCount A i := by
  unfold rowSum cumNonzeroCount rowNonzeroCount
  have hentry_bound : ∀ j : Fin n,
      A.a i j ≤ (univ.filter (fun k : Fin n => k.val ≤ i.val ∧ A.a k j ≠ 0)).card := by
    intro j
    by_cases hregion : i.val + j.val + 2 > n
    · exact entry_le_vert_count hn A i j hregion
    · have hzero := A.zero_region i j (by omega)
      simp [hzero]
  -- Sum and double count
  calc ∑ j : Fin n, A.a i j
      ≤ ∑ j : Fin n, (univ.filter (fun k : Fin n => k.val ≤ i.val ∧ A.a k j ≠ 0)).card :=
        sum_le_sum (fun j _ => hentry_bound j)
    _ = ∑ k ∈ univ.filter (fun k : Fin n => k.val ≤ i.val),
          (univ.filter (fun j : Fin n => A.a k j ≠ 0)).card := by
        -- Double counting: swap order of summation
        -- LHS: sum over j of |{k : k ≤ i and A k j ≠ 0}|
        -- RHS: sum over k ≤ i of |{j : A k j ≠ 0}|
        -- Both count pairs (k, j) with k ≤ i and A k j ≠ 0
        trans ∑ j : Fin n, ∑ k : Fin n, if k.val ≤ i.val ∧ A.a k j ≠ 0 then 1 else 0
        · congr 1; ext j
          rw [sum_boole]
          congr 1
        trans ∑ k : Fin n, ∑ j : Fin n, if k.val ≤ i.val ∧ A.a k j ≠ 0 then 1 else 0
        · rw [sum_comm]
        trans ∑ k : Fin n, if k.val ≤ i.val then ∑ j : Fin n, if A.a k j ≠ 0 then 1 else 0 else 0
        · congr 1; ext k
          by_cases hk : k.val ≤ i.val
          · simp only [hk, true_and, ite_true]
          · simp only [hk, false_and, ite_false, sum_const_zero]
        trans ∑ k ∈ univ.filter (fun k : Fin n => k.val ≤ i.val),
              ∑ j : Fin n, if A.a k j ≠ 0 then 1 else 0
        · rw [← sum_filter]
        congr 1; ext k
        rw [sum_boole]
        congr 1

-- Row i has at most (i+1) nonzeros
lemma row_nonzero_bound (_hn : n ≥ 2) (A : ValidMatrix n) (i : Fin n) :
    rowNonzeroCount A i ≤ i.val + 1 := by
  unfold rowNonzeroCount
  have hsub : univ.filter (fun j : Fin n => A.a i j ≠ 0) ⊆
              univ.filter (fun j : Fin n => j.val ≥ n - i.val - 1) := by
    intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj ⊢
    by_contra hcontra; push_neg at hcontra
    have : i.val + j.val + 2 ≤ n := by omega
    exact hj (A.zero_region i j this)
  have hcard_filter : (univ.filter (fun j : Fin n => j.val ≥ n - i.val - 1)).card ≤ i.val + 1 := by
    -- Count number of j : Fin n with j.val >= n - i.val - 1
    -- Use Fin.Ici which is a Finset (Fin n)
    have key : n - i.val - 1 < n := by omega
    let threshold : Fin n := ⟨n - i.val - 1, key⟩
    have hsub' : univ.filter (fun j : Fin n => j.val ≥ n - i.val - 1) ⊆ Finset.Ici threshold := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and, Finset.mem_Ici, Fin.le_def, threshold] at hj ⊢
      exact hj
    have hIci_card : (Finset.Ici threshold).card = n - threshold.val := Fin.card_Ici threshold
    have hthreshold_val : threshold.val = n - i.val - 1 := rfl
    calc (univ.filter (fun j : Fin n => j.val ≥ n - i.val - 1)).card
        ≤ (Finset.Ici threshold).card := card_le_card hsub'
      _ = n - threshold.val := hIci_card
      _ = n - (n - i.val - 1) := by rw [hthreshold_val]
      _ = i.val + 1 := by omega
  calc (univ.filter (fun j : Fin n => A.a i j ≠ 0)).card
      ≤ (univ.filter (fun j : Fin n => j.val ≥ n - i.val - 1)).card := card_le_card hsub
    _ ≤ i.val + 1 := hcard_filter

-- Key algebraic lemma
lemma key_claim (m x C : Nat) (hx_le : x ≤ m) :
    3 * min C (x * (x + 1) / 2) ≤ C + (m + 1) * x := by
  by_cases hC : C = 0
  · simp [hC]
  by_cases hx0 : x = 0
  · simp [hx0]
  have hC_pos : C > 0 := Nat.pos_of_ne_zero hC
  have hx_pos : x > 0 := Nat.pos_of_ne_zero hx0
  by_cases hcase : x * (x + 1) / 2 ≤ C
  · rw [min_eq_right hcase]
    have hdiv2 : 2 ∣ x * (x + 1) := Even.two_dvd (Nat.even_mul_succ_self x)
    obtain ⟨t, ht⟩ := hdiv2
    have ht_eq : x * (x + 1) / 2 = t := by rw [ht]; exact Nat.mul_div_cancel_left t (by omega)
    rw [ht_eq]
    have h2t_eq : 2 * t = x * (x + 1) := by linarith
    have ht_le_C : t ≤ C := by linarith
    have h2t_le_mx : 2 * t ≤ (m + 1) * x := by
      calc 2 * t = x * (x + 1) := h2t_eq
        _ = x * x + x := by ring
        _ ≤ m * x + x := by nlinarith
        _ = (m + 1) * x := by ring
    linarith
  · push_neg at hcase
    rw [min_eq_left (le_of_lt hcase)]
    have h2C_lt : 2 * C < x * (x + 1) := by
      have hdiv2 : 2 ∣ x * (x + 1) := Even.two_dvd (Nat.even_mul_succ_self x)
      obtain ⟨t, ht⟩ := hdiv2
      have ht_eq : x * (x + 1) / 2 = t := by rw [ht]; exact Nat.mul_div_cancel_left t (by omega)
      rw [ht_eq] at hcase
      linarith
    have hbound : 2 * C < (m + 1) * x := by
      calc 2 * C < x * (x + 1) := h2C_lt
        _ = x * x + x := by ring
        _ ≤ m * x + x := by nlinarith
        _ = (m + 1) * x := by ring
    linarith

-- Per-row bound: 3*s_i <= C_i + (i+2)*x_i
lemma row_bound (hn : n ≥ 2) (A : ValidMatrix n) (i : Fin n) :
    3 * rowSum A i ≤ cumNonzeroCount A i + (i.val + 2) * rowNonzeroCount A i := by
  have hh := horizontal_bound hn A i
  have hv := vertical_bound hn A i
  have hx_bound := row_nonzero_bound hn A i
  set s := rowSum A i with hs_def
  set x := rowNonzeroCount A i with hx_def
  set C := cumNonzeroCount A i with hC_def
  have hs_le_min : s ≤ min C (x * (x + 1) / 2) := by
    rw [le_min_iff]; constructor
    · exact hv
    · have : s * 2 ≤ x * (x + 1) := by linarith
      exact Nat.le_div_iff_mul_le (by omega) |>.mpr this
  have hkey := key_claim (i.val + 1) x C hx_bound
  calc 3 * s ≤ 3 * min C (x * (x + 1) / 2) := Nat.mul_le_mul_left 3 hs_le_min
    _ ≤ C + (i.val + 1 + 1) * x := hkey
    _ = C + (i.val + 2) * x := by ring

-- Sum of cumulative counts via double counting
lemma sum_cumulative (A : ValidMatrix n) :
    ∑ i : Fin n, cumNonzeroCount A i = ∑ k : Fin n, (n - k.val) * rowNonzeroCount A k := by
  unfold cumNonzeroCount
  trans ∑ i : Fin n, ∑ k : Fin n, if k.val ≤ i.val then rowNonzeroCount A k else 0
  · congr 1; ext i; rw [sum_filter]
  · rw [sum_comm]
    congr 1; ext k
    trans (univ.filter (fun i : Fin n => k.val ≤ i.val)).card * rowNonzeroCount A k
    · rw [← sum_filter]; simp only [sum_const, smul_eq_mul]
    · congr 1
      have heq : univ.filter (fun i : Fin n => k.val ≤ i.val) = Finset.Ici k := by
        ext i; simp only [mem_filter, mem_univ, true_and, Finset.mem_Ici, Fin.le_def]
      rw [heq, Fin.card_Ici]

-- Main theorem
theorem putnam_B4_2025 (hn : n ≥ 2) (A : ValidMatrix n) :
    3 * totalSum A ≤ (n + 2) * countNonzero A := by
  unfold totalSum countNonzero
  have hrow_bounds : ∀ i : Fin n,
      3 * rowSum A i ≤ cumNonzeroCount A i + (i.val + 2) * rowNonzeroCount A i :=
    fun i => row_bound hn A i
  have hsum : 3 * ∑ i : Fin n, rowSum A i ≤
              ∑ i : Fin n, cumNonzeroCount A i + ∑ i : Fin n, (i.val + 2) * rowNonzeroCount A i := by
    calc 3 * ∑ i : Fin n, rowSum A i
        = ∑ i : Fin n, 3 * rowSum A i := by rw [mul_sum]
      _ ≤ ∑ i : Fin n, (cumNonzeroCount A i + (i.val + 2) * rowNonzeroCount A i) :=
          sum_le_sum (fun i _ => hrow_bounds i)
      _ = ∑ i : Fin n, cumNonzeroCount A i + ∑ i : Fin n, (i.val + 2) * rowNonzeroCount A i := by
          rw [sum_add_distrib]
  have hcum := sum_cumulative A
  have hcombine : ∑ i : Fin n, cumNonzeroCount A i + ∑ i : Fin n, (i.val + 2) * rowNonzeroCount A i =
                  (n + 2) * ∑ i : Fin n, rowNonzeroCount A i := by
    rw [hcum]
    calc ∑ k : Fin n, (n - k.val) * rowNonzeroCount A k +
         ∑ i : Fin n, (i.val + 2) * rowNonzeroCount A i
        = ∑ i : Fin n, ((n - i.val) * rowNonzeroCount A i + (i.val + 2) * rowNonzeroCount A i) := by
          rw [← sum_add_distrib]
      _ = ∑ i : Fin n, ((n - i.val) + (i.val + 2)) * rowNonzeroCount A i := by
          congr 1; ext i; ring
      _ = ∑ i : Fin n, (n + 2) * rowNonzeroCount A i := by
          congr 1; ext i
          have : (n - i.val) + (i.val + 2) = n + 2 := by omega
          rw [this]
      _ = (n + 2) * ∑ i : Fin n, rowNonzeroCount A i := by rw [mul_sum]
  linarith

/--
The main result for the exact Putnam 2025 B4 problem statement.

For n ≥ 2, let A be an n×n matrix of nonnegative integers satisfying:
(a) a_{i,j} = 0 when i + j ≤ n (1-indexed)
(b) a_{i+1,j} ∈ {a_{i,j}, a_{i,j}+1}
(c) a_{i,j+1} ∈ {a_{i,j}, a_{i,j}+1}

Then 3S ≤ (n+2)N where S = sum of entries and N = count of nonzeros.
-/
theorem putnam_2025_B4 (hn : n ≥ 2) (A : PutnamB4Matrix n) :
    3 * (∑ i : Fin n, ∑ j : Fin n, A.a i j) ≤
    (n + 2) * (∑ i : Fin n, (univ.filter (fun j : Fin n => A.a i j ≠ 0)).card) := by
  -- Convert to ValidMatrix and apply the main theorem
  let A' := A.toValidMatrix
  have h := putnam_B4_2025 hn A'
  -- Show the sums are the same
  have hsum : ∑ i : Fin n, ∑ j : Fin n, A.a i j = totalSum A' := rfl
  have hcount : ∑ i : Fin n, (univ.filter (fun j : Fin n => A.a i j ≠ 0)).card = countNonzero A' := rfl
  rw [hsum, hcount]
  exact h
