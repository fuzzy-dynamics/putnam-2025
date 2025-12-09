/-
  Putnam 2025 Problem B3 - Complete Formalized Proof (NO axiom, NO sorry)

  S is a set of positive integers with the property that, for each element n of S,
  all positive divisors of 2025^n - 15^n are also in S.

  Show S = all positive integers.

  Key insight: 2025 = 15 * 135 = 3^4 * 5^2, so pow_diff(k) = 15^k * (135^k - 1)

  Strategy: For any n >= 2, we show there exists witness 0 < k < n with n | pow_diff(k).
  - For primes p /= 3,5: Fermat gives p | 135^(p-1) - 1, so k = p-1 works
  - For primes 3 and 5: Direct computation shows k = 1 works
  - For composites coprime to 15: Euler gives n | 135^phi(n) - 1, so k = phi(n) works
  - For composites NOT coprime to 15: Use k = max(v_3(n), v_5(n)) * phi(m)
    where n = 3^a * 5^b * m with gcd(m, 15) = 1
-/

import Mathlib

set_option maxRecDepth 2000

namespace Putnam2025B3

-- The expression 2025^k - 15^k
def pow_diff (k : Nat) : Nat := 2025^k - 15^k

-- Divisor-closed property
def DivisorClosed (S : Set Nat) : Prop :=
  forall n, n ∈ S -> forall d, d > 0 -> d ∣ pow_diff n -> d ∈ S

-- Basic lemmas
lemma pow_diff_pos (k : Nat) (hk : k > 0) : pow_diff k > 0 := by
  unfold pow_diff
  have : 2025^k > 15^k := Nat.pow_lt_pow_left (by norm_num) (by omega)
  omega

lemma one_in_S {S : Set Nat} (hS : DivisorClosed S) (hne : ∃ n ∈ S, n > 0) : 1 ∈ S := by
  obtain ⟨n, hn, hn_pos⟩ := hne
  exact hS n hn 1 (by omega) (Nat.one_dvd _)

-- The factorization: pow_diff(k) = 15^k * (135^k - 1)
lemma pow_diff_factored (k : Nat) : pow_diff k = 15^k * (135^k - 1) := by
  unfold pow_diff
  have h2025 : (2025 : ℕ) = 15 * 135 := by norm_num
  calc 2025^k - 15^k = (15 * 135)^k - 15^k := by rw [h2025]
    _ = 15^k * 135^k - 15^k := by rw [mul_pow]
    _ = 15^k * (135^k - 1) := by rw [Nat.mul_sub_one]

-- Fermat's Little Theorem application for primes p /= 3, 5
lemma fermat_witness {p : Nat} (hp : Nat.Prime p) (hp3 : p ≠ 3) (hp5 : p ≠ 5) :
    p ∣ pow_diff (p - 1) := by
  rw [pow_diff_factored]
  apply dvd_mul_of_dvd_right
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hFermat : (135 : ZMod p)^(p-1) = 1 := by
    apply ZMod.pow_card_sub_one_eq_one
    intro h_zero
    have hp_dvd_135 : p ∣ 135 := by rw [← ZMod.natCast_eq_zero_iff]; exact h_zero
    have h135 : (135 : ℕ) = 3^3 * 5 := by norm_num
    rw [h135] at hp_dvd_135
    rw [hp.dvd_mul] at hp_dvd_135
    cases hp_dvd_135 with
    | inl h3 =>
      have : p ∣ 3 := Nat.Prime.dvd_of_dvd_pow hp h3
      have : p = 3 := (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) p this).resolve_left hp.ne_one
      exact hp3 this
    | inr h5 =>
      have : p = 5 := (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) p h5).resolve_left hp.ne_one
      exact hp5 this
  have h_ge : 135^(p-1) ≥ 1 := Nat.one_le_pow _ _ (by norm_num)
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast [Nat.cast_sub h_ge]
  simp [hFermat]

-- Helper: coprimality of 135 with n coprime to 15
lemma coprime_135_of_coprime_15 {n : Nat} (hcop15 : Nat.Coprime n 15) : Nat.Coprime 135 n := by
  have h135 : (135 : ℕ) = 3^3 * 5 := by norm_num
  have h3 : Nat.Coprime n 3 := Nat.Coprime.coprime_dvd_right (by norm_num : (3 : ℕ) ∣ 15) hcop15
  have h5 : Nat.Coprime n 5 := Nat.Coprime.coprime_dvd_right (by norm_num : (5 : ℕ) ∣ 15) hcop15
  have h27 : Nat.Coprime n 27 := Nat.Coprime.pow_right 3 h3
  rw [h135]
  rw [Nat.coprime_comm] at h27 h5
  exact Nat.Coprime.mul_left h27 h5

-- Euler's theorem application for composites coprime to 15
lemma euler_witness {n : Nat} (hn2 : n ≥ 2) (hcop15 : Nat.Coprime n 15) :
    n ∣ pow_diff (Nat.totient n) := by
  rw [pow_diff_factored]
  have hcop135 : Nat.Coprime 135 n := coprime_135_of_coprime_15 hcop15
  have hmod : 135 ^ Nat.totient n ≡ 1 [MOD n] := Nat.ModEq.pow_totient hcop135
  have h135_dvd : n ∣ 135^(Nat.totient n) - 1 := by
    have h1 : 135^(Nat.totient n) ≥ 1 := Nat.one_le_pow _ 135 (by norm_num)
    rw [← Nat.modEq_iff_dvd' h1]
    exact hmod.symm
  exact dvd_mul_of_dvd_right h135_dvd (15^(Nat.totient n))

-- Key helper: k < p^k for p >= 2 and k >= 1
lemma k_lt_pow_k (p k : ℕ) (hp : p ≥ 2) (hk : k ≥ 1) : k < p^k :=
  Nat.lt_pow_self (by omega : 1 < p)

-- Key lemma for composites NOT coprime to 15
-- For n not coprime to 15, we construct a witness using padic valuations
lemma not_coprime_15_witness {n : Nat} (hn : n ≥ 2) (hncop : ¬Nat.Coprime n 15) :
    ∃ k, 0 < k ∧ k < n ∧ n ∣ pow_diff k := by
  -- gcd(n, 15) > 1 means 3 | n or 5 | n
  have h35 : 3 ∣ n ∨ 5 ∣ n := by
    by_contra h
    push_neg at h
    have hg3 : Nat.Coprime n 3 := by
      rw [Nat.coprime_comm]
      rw [Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)]
      exact h.1
    have hg5 : Nat.Coprime n 5 := by
      rw [Nat.coprime_comm]
      rw [Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)]
      exact h.2
    have : Nat.Coprime n 15 := by
      rw [show (15 : ℕ) = 3 * 5 by norm_num]
      exact Nat.Coprime.mul_right hg3 hg5
    exact hncop this

  haveI hF3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI hF5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

  -- Step 1: Define p-adic valuations
  let a := padicValNat 3 n
  let b := padicValNat 5 n

  -- Step 2: Extract the coprime part m = n / (3^a * 5^b)
  have h3a_dvd : 3^a ∣ n := pow_padicValNat_dvd
  have h5b_dvd : 5^b ∣ n := pow_padicValNat_dvd

  have h35_coprime : Nat.Coprime (3^a) (5^b) := by
    apply Nat.Coprime.pow_right b
    apply Nat.Coprime.pow_left a
    norm_num

  have h35_dvd : 3^a * 5^b ∣ n :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd h35_coprime h3a_dvd h5b_dvd

  let m := n / (3^a * 5^b)

  have hn_factor : n = 3^a * 5^b * m := by
    have h := Nat.div_mul_cancel h35_dvd
    rw [mul_comm] at h
    exact h.symm

  -- Step 3: Show m is coprime to 15
  have hm_coprime_3 : Nat.Coprime m 3 := by
    rw [Nat.coprime_comm]
    rw [Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)]
    intro h3m
    have hdvd : 3^(a + 1) ∣ n := by
      rw [hn_factor]
      have h3_dvd_5bm : 3 ∣ 5^b * m := dvd_mul_of_dvd_right h3m _
      calc 3^(a + 1) = 3^a * 3 := by ring
        _ ∣ 3^a * (5^b * m) := Nat.mul_dvd_mul_left (3^a) h3_dvd_5bm
        _ = 3^a * 5^b * m := by ring
    have hval : a + 1 ≤ padicValNat 3 n := by
      rw [← padicValNat_dvd_iff_le (by omega : n ≠ 0)]
      exact hdvd
    omega

  have hm_coprime_5 : Nat.Coprime m 5 := by
    rw [Nat.coprime_comm]
    rw [Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)]
    intro h5m
    have hdvd : 5^(b + 1) ∣ n := by
      rw [hn_factor]
      have h5_dvd_3am : 5 ∣ 3^a * m := dvd_mul_of_dvd_right h5m _
      calc 5^(b + 1) = 5^b * 5 := by ring
        _ ∣ 5^b * (3^a * m) := Nat.mul_dvd_mul_left (5^b) h5_dvd_3am
        _ = 3^a * 5^b * m := by ring
    have hval : b + 1 ≤ padicValNat 5 n := by
      rw [← padicValNat_dvd_iff_le (by omega : n ≠ 0)]
      exact hdvd
    omega

  have hm_coprime_15 : Nat.Coprime m 15 := by
    rw [show (15 : Nat) = 3 * 5 by norm_num]
    exact Nat.Coprime.mul_right hm_coprime_3 hm_coprime_5

  have hm_pos : m ≥ 1 := by
    have h35_pos : 0 < 3^a * 5^b := by positivity
    exact Nat.div_pos (Nat.le_of_dvd (by omega) h35_dvd) h35_pos

  -- Step 4: Since gcd(n, 15) > 1, we have a >= 1 or b >= 1
  have hab_pos : a ≥ 1 ∨ b ≥ 1 := by
    by_contra h_neg
    push_neg at h_neg
    have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    have h3_ndvd : ¬(3 ∣ n) := by
      intro h3
      have : padicValNat 3 n ≥ 1 := one_le_padicValNat_of_dvd (by omega) h3
      omega
    have h5_ndvd : ¬(5 ∣ n) := by
      intro h5
      have : padicValNat 5 n ≥ 1 := one_le_padicValNat_of_dvd (by omega) h5
      omega
    have hcop : Nat.Coprime n 15 := by
      rw [show (15 : Nat) = 3 * 5 by norm_num]
      have h3c : Nat.Coprime n 3 := by
        rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)]
        exact h3_ndvd
      have h5c : Nat.Coprime n 5 := by
        rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)]
        exact h5_ndvd
      exact Nat.Coprime.mul_right h3c h5c
    exact hncop hcop

  -- Step 5: Construct witness k
  by_cases hm1 : m = 1

  · -- Case m = 1: witness k = max(a, b)
    use max a b
    refine ⟨by omega, ?_, ?_⟩

    · -- Prove max(a, b) < n
      have hn_eq : n = 3^a * 5^b := by rw [hn_factor, hm1, mul_one]
      have h3a_pos : 0 < 3^a := by positivity
      have h5b_pos : 0 < 5^b := by positivity
      -- Use Nat.lt_pow_self directly
      cases hab_pos with
      | inl ha1 =>
        by_cases hb0 : b = 0
        · simp only [hb0, pow_zero, mul_one] at hn_eq
          have : max a b = a := by simp [hb0]
          rw [this, hn_eq]
          exact Nat.lt_pow_self (by omega : 1 < 3)
        · have hb1 : b ≥ 1 := by omega
          have a_lt : a < 3^a := Nat.lt_pow_self (by omega : 1 < 3)
          have b_lt : b < 5^b := Nat.lt_pow_self (by omega : 1 < 5)
          have : max a b < max (3^a) (5^b) := max_lt_max a_lt b_lt
          have : max (3^a) (5^b) ≤ 3^a * 5^b :=
            max_le_iff.mpr ⟨Nat.le_mul_of_pos_right _ h5b_pos, Nat.le_mul_of_pos_left _ h3a_pos⟩
          rw [hn_eq]; omega
      | inr hb1 =>
        by_cases ha0 : a = 0
        · simp only [ha0, pow_zero, one_mul] at hn_eq
          have : max a b = b := by simp [ha0]
          rw [this, hn_eq]
          exact Nat.lt_pow_self (by omega : 1 < 5)
        · have ha1 : a ≥ 1 := by omega
          have a_lt : a < 3^a := Nat.lt_pow_self (by omega : 1 < 3)
          have b_lt : b < 5^b := Nat.lt_pow_self (by omega : 1 < 5)
          have : max a b < max (3^a) (5^b) := max_lt_max a_lt b_lt
          have : max (3^a) (5^b) ≤ 3^a * 5^b :=
            max_le_iff.mpr ⟨Nat.le_mul_of_pos_right _ h5b_pos, Nat.le_mul_of_pos_left _ h3a_pos⟩
          rw [hn_eq]; omega

    · -- Prove n | pow_diff(max a b)
      have hn_eq : n = 3^a * 5^b := by rw [hn_factor, hm1, mul_one]
      let k := max a b
      rw [pow_diff_factored]
      have h15 : (15 : Nat) = 3 * 5 := by norm_num
      have h15k : 15^k = 3^k * 5^k := by rw [h15, mul_pow]
      rw [h15k, hn_eq]
      have ha_le : a ≤ k := Nat.le_max_left a b
      have hb_le : b ≤ k := Nat.le_max_right a b
      have h3_dvd : 3^a ∣ 3^k := Nat.pow_dvd_pow 3 ha_le
      have h5_dvd : 5^b ∣ 5^k := Nat.pow_dvd_pow 5 hb_le
      have h35_dvd' : 3^a * 5^b ∣ 3^k * 5^k := Nat.mul_dvd_mul h3_dvd h5_dvd
      exact Nat.dvd_mul_right_of_dvd h35_dvd' _

  · -- Case m > 1: witness k = max(a, b) * phi(m)
    have hm_gt1 : m > 1 := by omega

    have htot_lt : Nat.totient m < m := Nat.totient_lt m hm_gt1
    have htot_pos : Nat.totient m ≥ 1 := by
      have : 0 < Nat.totient m := Nat.totient_pos.mpr (by omega)
      omega

    have h135_coprime_m : Nat.Coprime 135 m := by
      rw [show (135 : Nat) = 3^3 * 5 by norm_num]
      have h3_cop : Nat.Coprime (3^3) m := by
        apply Nat.Coprime.pow_left 3
        exact hm_coprime_3.symm
      exact Nat.Coprime.mul_left h3_cop hm_coprime_5.symm

    have hab_ge1 : max a b ≥ 1 := by
      cases hab_pos with
      | inl ha1 => exact Nat.le_max_left a b |>.trans' ha1
      | inr hb1 => exact Nat.le_max_right a b |>.trans' hb1

    let k := max a b * Nat.totient m
    use k
    have hk_pos : k > 0 := by
      have : max a b ≥ 1 := hab_ge1
      have : Nat.totient m ≥ 1 := htot_pos
      show max a b * Nat.totient m > 0
      positivity
    refine ⟨hk_pos, ?_, ?_⟩

    · -- Prove k < n
      have h3a_pos : 0 < 3^a := by positivity
      have h5b_pos : 0 < 5^b := by positivity

      have hab_lt_35 : max a b < 3^a * 5^b := by
        cases hab_pos with
        | inl ha1 =>
          by_cases hb0 : b = 0
          · simp only [hb0, pow_zero, mul_one]
            have ha_lt : a < 3^a := Nat.lt_pow_self (by omega : 1 < 3)
            have : max a b = a := by simp [hb0]
            omega
          · have hb1 : b ≥ 1 := by omega
            have a_lt : a < 3^a := Nat.lt_pow_self (by omega : 1 < 3)
            have b_lt : b < 5^b := Nat.lt_pow_self (by omega : 1 < 5)
            have h1 : max a b < max (3^a) (5^b) := max_lt_max a_lt b_lt
            have h2 : max (3^a) (5^b) ≤ 3^a * 5^b :=
              max_le_iff.mpr ⟨Nat.le_mul_of_pos_right _ h5b_pos, Nat.le_mul_of_pos_left _ h3a_pos⟩
            omega
        | inr hb1 =>
          by_cases ha0 : a = 0
          · simp only [ha0, pow_zero, one_mul]
            have hb_lt : b < 5^b := Nat.lt_pow_self (by omega : 1 < 5)
            have : max a b = b := by simp [ha0]
            omega
          · have ha1 : a ≥ 1 := by omega
            have a_lt : a < 3^a := Nat.lt_pow_self (by omega : 1 < 3)
            have b_lt : b < 5^b := Nat.lt_pow_self (by omega : 1 < 5)
            have h1 : max a b < max (3^a) (5^b) := max_lt_max a_lt b_lt
            have h2 : max (3^a) (5^b) ≤ 3^a * 5^b :=
              max_le_iff.mpr ⟨Nat.le_mul_of_pos_right _ h5b_pos, Nat.le_mul_of_pos_left _ h3a_pos⟩
            omega

      calc k = max a b * Nat.totient m := rfl
        _ < 3^a * 5^b * m := Nat.mul_lt_mul_of_lt_of_le hab_lt_35 (le_of_lt htot_lt) (by positivity)
        _ = n := hn_factor.symm

    · -- Prove n | pow_diff k
      rw [pow_diff_factored]
      have h15 : (15 : Nat) = 3 * 5 := by norm_num
      have h15k : 15^k = 3^k * 5^k := by rw [h15, mul_pow]
      rw [h15k, hn_factor]

      have hk_ge_hab : k ≥ max a b := Nat.le_mul_of_pos_right _ htot_pos
      have ha_le_k : a ≤ k := (Nat.le_max_left a b).trans hk_ge_hab
      have hb_le_k : b ≤ k := (Nat.le_max_right a b).trans hk_ge_hab

      have h3_dvd : 3^a ∣ 3^k := Nat.pow_dvd_pow 3 ha_le_k
      have h5_dvd : 5^b ∣ 5^k := Nat.pow_dvd_pow 5 hb_le_k

      -- By Euler: 135^phi(m) ≡ 1 (mod m), so 135^k ≡ 1 (mod m)
      have hm_dvd : m ∣ 135^k - 1 := by
        have hge1 : 135^k ≥ 1 := Nat.one_le_pow _ _ (by norm_num)
        have h_euler := Nat.ModEq.pow_totient h135_coprime_m

        have hk_eq : k = Nat.totient m * max a b := by
          show max a b * Nat.totient m = Nat.totient m * max a b
          ring

        have h_k_mod : 135^k ≡ 1 [MOD m] := by
          rw [hk_eq, pow_mul]
          calc (135^(Nat.totient m))^(max a b)
              ≡ 1^(max a b) [MOD m] := Nat.ModEq.pow _ h_euler
            _ = 1 := one_pow _

        have h_k_mod' : 1 ≡ 135^k [MOD m] := h_k_mod.symm
        rw [Nat.modEq_iff_dvd' hge1] at h_k_mod'
        exact h_k_mod'

      have h35_dvd' : 3^a * 5^b ∣ 3^k * 5^k := Nat.mul_dvd_mul h3_dvd h5_dvd

      have hm_coprime_35k : Nat.Coprime m (3^k * 5^k) := by
        have h3k : Nat.Coprime m (3^k) := hm_coprime_3.pow_right k
        have h5k : Nat.Coprime m (5^k) := hm_coprime_5.pow_right k
        exact h3k.mul_right h5k

      have h35m_coprime : Nat.Coprime (3^a * 5^b) m := by
        have h3a : Nat.Coprime (3^a) m := hm_coprime_3.symm.pow_left a
        have h5b : Nat.Coprime (5^b) m := hm_coprime_5.symm.pow_left b
        exact h3a.mul_left h5b

      have h35_dvd'' : 3^a * 5^b ∣ 3^k * 5^k * (135^k - 1) :=
        Nat.dvd_mul_right_of_dvd h35_dvd' _

      have hm_dvd' : m ∣ 3^k * 5^k * (135^k - 1) :=
        dvd_mul_of_dvd_right hm_dvd _

      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h35m_coprime h35_dvd'' hm_dvd'

-- Core lemma: for any n >= 2, there exists witness 0 < k < n with n | pow_diff(k)
lemma exists_smaller_witness (n : Nat) (hn : n ≥ 2) :
    ∃ k, 0 < k ∧ k < n ∧ n ∣ pow_diff k := by
  -- Case 1: n is prime
  by_cases h_prime : Nat.Prime n
  · by_cases h3 : n = 3
    · use 1; subst h3; constructor; norm_num; constructor; norm_num
      unfold pow_diff; decide
    · by_cases h5 : n = 5
      · use 1; subst h5; constructor; norm_num; constructor; norm_num
        unfold pow_diff; decide
      · -- n is prime, n /= 3, n /= 5: use Fermat with k = n-1
        use n - 1
        constructor; · omega
        constructor; · omega
        · exact fermat_witness h_prime h3 h5

  · -- Case 2: n is composite
    by_cases hcop15 : Nat.Coprime n 15
    · -- Coprime to 15: use Euler with k = phi(n)
      use Nat.totient n
      constructor
      · exact Nat.totient_pos.mpr (by omega)
      constructor
      · exact Nat.totient_lt n (by omega)
      · exact euler_witness hn hcop15

    · -- Not coprime to 15: use the structural lemma
      exact not_coprime_15_witness hn hcop15

-- Main theorem: S contains all positive integers
theorem all_positive_in_S {S : Set Nat} (hS : DivisorClosed S) (hne : ∃ n ∈ S, n > 0) :
    ∀ n, n > 0 -> n ∈ S := by
  intro n hn
  induction' n using Nat.strong_induction_on with n ih
  by_cases h1 : n = 1
  · subst h1; exact one_in_S hS hne
  · have hn2 : n ≥ 2 := by omega
    obtain ⟨k, hk_pos, hk_lt, hk_dvd⟩ := exists_smaller_witness n hn2
    have hk_in_S := ih k hk_lt hk_pos
    exact hS k hk_in_S n (by omega) hk_dvd

-- Final theorem statement
theorem putnam_2025_B3 (S : Set Nat)
    (hne : ∃ n ∈ S, n > 0)
    (hS : DivisorClosed S) :
    ∀ n, n > 0 -> n ∈ S :=
  all_positive_in_S hS hne

end Putnam2025B3
