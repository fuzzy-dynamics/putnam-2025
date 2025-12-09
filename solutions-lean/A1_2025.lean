/-
  Putnam 2025 Problem A1 - Formalized

  Let m_0 and n_0 be distinct positive integers. For every positive integer k,
  define m_k and n_k to be the relatively prime positive integers such that
    m_k / n_k = (2*m_{k-1} + 1) / (2*n_{k-1} + 1)

  Prove that 2*m_k + 1 and 2*n_k + 1 are relatively prime for all but
  finitely many positive integers k.
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

namespace Putnam2025A1

/-
  Key insight: Track the "odd part" of |a_k - b_k| where a_k = 2*m_k + 1, b_k = 2*n_k + 1.

  The odd part strictly decreases whenever gcd(a_k, b_k) > 1.
  Since odd parts are positive integers, this can only happen finitely many times.
-/

-- Helper: a number of form 2k+1 is coprime to 2
lemma coprime_two_add_one (k : Nat) : Nat.Coprime 2 (2 * k + 1) := by
  rw [Nat.coprime_comm]
  simp only [Nat.coprime_two_right, Nat.odd_iff]
  omega

-- GCD of two numbers of form 2k+1 must be odd (coprime to 2)
lemma gcd_odd_form {a b : Nat} (ha : ∃ k, a = 2 * k + 1) (hb : ∃ k, b = 2 * k + 1) :
    Nat.Coprime 2 (Nat.gcd a b) := by
  obtain ⟨ka, hka⟩ := ha
  obtain ⟨kb, hkb⟩ := hb
  -- Coprime 2 n means gcd 2 n = 1, i.e., n is odd
  rw [Nat.coprime_comm, Nat.coprime_two_right, Nat.odd_iff]
  -- Goal: gcd a b % 2 = 1
  -- Prove by contradiction: if gcd a b is even, then 2 | a, contradiction
  by_contra heven
  have hmod0 : Nat.gcd a b % 2 = 0 := by
    have hlt : Nat.gcd a b % 2 < 2 := Nat.mod_lt _ (by omega)
    omega
  have h2div : 2 ∣ Nat.gcd a b := Nat.dvd_of_mod_eq_zero hmod0
  have h2diva : 2 ∣ a := Nat.dvd_trans h2div (Nat.gcd_dvd_left a b)
  rw [hka] at h2diva
  omega

-- Main structure: the recurrence relation
structure PutnamSeq where
  m : Nat → Nat
  n : Nat → Nat
  m_pos : ∀ k, 0 < m k
  n_pos : ∀ k, 0 < n k
  coprime : ∀ k, 0 < k → Nat.Coprime (m k) (n k)  -- Only for k > 0 (m_0, n_0 only need to be distinct)
  recurrence : ∀ k, (m (k+1)) * (2 * n k + 1) = (n (k+1)) * (2 * m k + 1)
  distinct_init : m 0 ≠ n 0

-- Define a_k = 2*m_k + 1 and b_k = 2*n_k + 1
def a (s : PutnamSeq) (k : Nat) : Nat := 2 * s.m k + 1
def b (s : PutnamSeq) (k : Nat) : Nat := 2 * s.n k + 1

-- a_k has the form 2*m_k + 1
lemma a_form (s : PutnamSeq) (k : Nat) : ∃ j, a s k = 2 * j + 1 := ⟨s.m k, rfl⟩
lemma b_form (s : PutnamSeq) (k : Nat) : ∃ j, b s k = 2 * j + 1 := ⟨s.n k, rfl⟩

-- The gcd d_k = gcd(a_k, b_k)
def d (s : PutnamSeq) (k : Nat) : Nat := Nat.gcd (a s k) (b s k)

-- d_k is always odd (coprime to 2)
lemma d_coprime_two (s : PutnamSeq) (k : Nat) : Nat.Coprime 2 (d s k) :=
  gcd_odd_form (a_form s k) (b_form s k)

-- Key fact: d_k divides the difference |a_k - b_k|
lemma d_dvd_diff (s : PutnamSeq) (k : Nat) : (d s k) ∣ (a s k - b s k : Int).natAbs := by
  have h1 := Nat.gcd_dvd_left (a s k) (b s k)
  have h2 := Nat.gcd_dvd_right (a s k) (b s k)
  exact Int.natAbs_dvd_natAbs.mpr (Int.dvd_sub (Int.ofNat_dvd.mpr h1) (Int.ofNat_dvd.mpr h2))

-- The difference delta_k = |a_k - b_k|
def delta (s : PutnamSeq) (k : Nat) : Nat := (a s k - b s k : Int).natAbs

-- Key lemma: m_k ≠ n_k for all k (by induction from distinct_init)
lemma m_ne_n (s : PutnamSeq) (k : Nat) : s.m k ≠ s.n k := by
  induction k with
  | zero => exact s.distinct_init
  | succ k ih =>
    intro heq
    have hrec := s.recurrence k
    have hm_pos : 0 < s.m (k + 1) := s.m_pos (k + 1)
    have hrec' : s.m (k + 1) * (2 * s.n k + 1) = s.m (k + 1) * (2 * s.m k + 1) := by
      calc s.m (k + 1) * (2 * s.n k + 1)
          = s.n (k + 1) * (2 * s.m k + 1) := hrec
        _ = s.m (k + 1) * (2 * s.m k + 1) := by rw [← heq]
    have h : 2 * s.n k + 1 = 2 * s.m k + 1 := Nat.eq_of_mul_eq_mul_left hm_pos hrec'
    have heq' : s.n k = s.m k := by omega
    exact ih heq'.symm

-- delta_k > 0 since m_k ≠ n_k
lemma delta_pos (s : PutnamSeq) (k : Nat) : 0 < delta s k := by
  unfold delta a b
  have hne : s.m k ≠ s.n k := m_ne_n s k
  simp only [Int.natAbs_sub_pos_iff]
  omega

-- Define the odd part of a positive natural (largest odd divisor)
noncomputable def oddPart (n : Nat) : Nat :=
  if n = 0 then 0 else n / 2^(n.factorization 2)

-- The odd part is always odd for n > 0
lemma oddPart_odd (n : Nat) (hn : n > 0) : Odd (oddPart n) := by
  unfold oddPart
  have hne : n ≠ 0 := by omega
  simp only [hne, ↓reduceIte]
  rw [Nat.odd_iff]
  have hdvd : 2 ^ n.factorization 2 ∣ n := Nat.ordProj_dvd n 2
  by_contra h
  push_neg at h
  have heven : n / 2 ^ n.factorization 2 % 2 = 0 := by omega
  have h2dvd : 2 ∣ n / 2 ^ n.factorization 2 := Nat.dvd_of_mod_eq_zero heven
  have hkey : 2 ^ (n.factorization 2 + 1) ∣ n := by
    rw [pow_succ]
    exact Nat.mul_dvd_of_dvd_div hdvd h2dvd
  have hne : n ≠ 0 := by omega
  have := Nat.pow_succ_factorization_not_dvd hne Nat.prime_two
  exact this hkey

-- The odd part divides the original
lemma oddPart_dvd (n : Nat) : oddPart n ∣ n := by
  unfold oddPart
  split_ifs with hn
  · subst hn; simp
  · -- n / 2^k divides n when 2^k divides n
    exact Nat.ordCompl_dvd n 2

-- An odd number divides the odd part of any number it divides
lemma odd_dvd_oddPart {d n : Nat} (hd : Odd d) (hdvd : d ∣ n) :
    d ∣ oddPart n := by
  unfold oddPart
  split_ifs with hn
  · subst hn
    simp only [Nat.dvd_zero]
  · have hd2 : Nat.Coprime d 2 := Odd.coprime_two_right hd
    have hcop : Nat.Coprime d (2 ^ n.factorization 2) :=
      Nat.Coprime.pow_right (n.factorization 2) hd2
    have hdiv : 2 ^ n.factorization 2 ∣ n := Nat.ordProj_dvd n 2
    have heq : n / 2 ^ n.factorization 2 * 2 ^ n.factorization 2 = n :=
      Nat.div_mul_cancel hdiv
    have hdvd' : d ∣ n / 2 ^ n.factorization 2 * 2 ^ n.factorization 2 := by
      rwa [heq]
    exact Nat.Coprime.dvd_of_dvd_mul_right hcop hdvd'

-- d_k divides the odd part of delta_k (since d_k is odd and divides delta_k)
lemma d_dvd_oddPart (s : PutnamSeq) (k : Nat) : d s k ∣ oddPart (delta s k) := by
  -- d_k is odd (d_coprime_two) and d_k | delta_k (d_dvd_diff)
  have hodd : Odd (d s k) := by
    have h := d_coprime_two s k
    rw [Nat.coprime_comm, Nat.coprime_two_right] at h
    exact h
  exact odd_dvd_oddPart hodd (d_dvd_diff s k)

-- Key lemma: from the recurrence and coprimality, m_{k+1} * d_k = a_k
-- This is because m_{k+1}/n_{k+1} = a_k/b_k in lowest terms
lemma m_eq_a_div_d (s : PutnamSeq) (k : Nat) :
    s.m (k + 1) * d s k = a s k := by
  have hrec := s.recurrence k
  have hcop := s.coprime (k + 1) (by omega)
  -- m_{k+1} | n_{k+1} * (2m_k + 1), and gcd(m,n)=1, so m_{k+1} | (2m_k + 1)
  have hm_dvd_a : s.m (k + 1) ∣ a s k := by
    have hdvd : s.m (k + 1) ∣ s.n (k + 1) * (2 * s.m k + 1) := ⟨2 * s.n k + 1, by linarith [hrec]⟩
    have := Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd
    simp only [a]; exact this
  -- n_{k+1} | m_{k+1} * (2n_k + 1), and gcd(m,n)=1, so n_{k+1} | (2n_k + 1)
  have hn_dvd_b : s.n (k + 1) ∣ b s k := by
    have hdvd : s.n (k + 1) ∣ s.m (k + 1) * (2 * s.n k + 1) := ⟨2 * s.m k + 1, by linarith [hrec]⟩
    have hcop' := Nat.Coprime.symm hcop
    have hdvd' : s.n (k + 1) ∣ (2 * s.n k + 1) * s.m (k + 1) := by rwa [Nat.mul_comm]
    have := Nat.Coprime.dvd_of_dvd_mul_right hcop' hdvd'
    simp only [b]; exact this
  obtain ⟨qa, hqa⟩ := hm_dvd_a
  obtain ⟨qb, hqb⟩ := hn_dvd_b
  -- Show qa = qb
  have hqa' : 2 * s.m k + 1 = s.m (k + 1) * qa := by simp only [a] at hqa; exact hqa
  have hqb' : 2 * s.n k + 1 = s.n (k + 1) * qb := by simp only [b] at hqb; exact hqb
  have hq_eq : qa = qb := by
    have hm_pos : 0 < s.m (k + 1) := s.m_pos (k + 1)
    have hn_pos : 0 < s.n (k + 1) := s.n_pos (k + 1)
    calc qa = (s.m (k + 1) * qa) / s.m (k + 1) := by rw [Nat.mul_div_cancel_left qa hm_pos]
      _ = (2 * s.m k + 1) / s.m (k + 1) := by rw [← hqa']
      _ = (s.n (k + 1) * (2 * s.m k + 1)) / (s.n (k + 1) * s.m (k + 1)) := by
          rw [Nat.mul_div_mul_left _ _ hn_pos]
      _ = (s.m (k + 1) * (2 * s.n k + 1)) / (s.n (k + 1) * s.m (k + 1)) := by rw [hrec]
      _ = (s.m (k + 1) * (2 * s.n k + 1)) / (s.m (k + 1) * s.n (k + 1)) := by ring_nf
      _ = (2 * s.n k + 1) / s.n (k + 1) := by rw [Nat.mul_div_mul_left _ _ hm_pos]
      _ = (s.n (k + 1) * qb) / s.n (k + 1) := by rw [← hqb']
      _ = qb := by rw [Nat.mul_div_cancel_left qb hn_pos]
  -- d_k = gcd(a_k, b_k) = gcd(m * qa, n * qb) = qa * gcd(m, n) = qa
  have hgcd : d s k = qa := by
    simp only [d, a, b, hqa', hqb', hq_eq]
    rw [Nat.gcd_mul_right]
    simp only [hcop, Nat.one_mul]
  simp only [a, hqa', hgcd]

lemma n_eq_b_div_d (s : PutnamSeq) (k : Nat) :
    s.n (k + 1) * d s k = b s k := by
  have hrec := s.recurrence k
  have hcop := s.coprime (k + 1) (by omega)
  have hm_dvd_a : s.m (k + 1) ∣ a s k := by
    have hdvd : s.m (k + 1) ∣ s.n (k + 1) * (2 * s.m k + 1) := ⟨2 * s.n k + 1, by linarith [hrec]⟩
    have := Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd
    simp only [a]; exact this
  have hn_dvd_b : s.n (k + 1) ∣ b s k := by
    have hdvd : s.n (k + 1) ∣ s.m (k + 1) * (2 * s.n k + 1) := ⟨2 * s.m k + 1, by linarith [hrec]⟩
    have hcop' := Nat.Coprime.symm hcop
    have hdvd' : s.n (k + 1) ∣ (2 * s.n k + 1) * s.m (k + 1) := by rwa [Nat.mul_comm]
    have := Nat.Coprime.dvd_of_dvd_mul_right hcop' hdvd'
    simp only [b]; exact this
  obtain ⟨qa, hqa⟩ := hm_dvd_a
  obtain ⟨qb, hqb⟩ := hn_dvd_b
  have hqa' : 2 * s.m k + 1 = s.m (k + 1) * qa := by simp only [a] at hqa; exact hqa
  have hqb' : 2 * s.n k + 1 = s.n (k + 1) * qb := by simp only [b] at hqb; exact hqb
  have hq_eq : qa = qb := by
    have hm_pos : 0 < s.m (k + 1) := s.m_pos (k + 1)
    have hn_pos : 0 < s.n (k + 1) := s.n_pos (k + 1)
    calc qa = (s.m (k + 1) * qa) / s.m (k + 1) := by rw [Nat.mul_div_cancel_left qa hm_pos]
      _ = (2 * s.m k + 1) / s.m (k + 1) := by rw [← hqa']
      _ = (s.n (k + 1) * (2 * s.m k + 1)) / (s.n (k + 1) * s.m (k + 1)) := by
          rw [Nat.mul_div_mul_left _ _ hn_pos]
      _ = (s.m (k + 1) * (2 * s.n k + 1)) / (s.n (k + 1) * s.m (k + 1)) := by rw [hrec]
      _ = (s.m (k + 1) * (2 * s.n k + 1)) / (s.m (k + 1) * s.n (k + 1)) := by ring_nf
      _ = (2 * s.n k + 1) / s.n (k + 1) := by rw [Nat.mul_div_mul_left _ _ hm_pos]
      _ = (s.n (k + 1) * qb) / s.n (k + 1) := by rw [← hqb']
      _ = qb := by rw [Nat.mul_div_cancel_left qb hn_pos]
  have hgcd : d s k = qb := by
    simp only [d, a, b, hqa', hqb', hq_eq]
    rw [Nat.gcd_mul_right]
    simp only [hcop, Nat.one_mul]
  simp only [b, hqb', hgcd]

-- delta is always even: delta_k = 2 * |m_k - n_k|
lemma delta_eq_two_mul (s : PutnamSeq) (k : Nat) :
    delta s k = 2 * (s.m k - s.n k : Int).natAbs := by
  simp only [delta, a, b]
  -- Need to show |(2m+1) - (2n+1)| = 2 * |m - n|
  have h : ((2 * s.m k + 1 : Nat) : Int) - ((2 * s.n k + 1 : Nat) : Int) =
           2 * ((s.m k : Int) - (s.n k : Int)) := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  rw [h, Int.natAbs_mul]
  norm_num

-- Key recurrence: delta_k * d_{k-1} = 2 * delta_{k-1}
lemma delta_recurrence (s : PutnamSeq) (k : Nat) (hk : k > 0) :
    delta s k * d s (k-1) = 2 * delta s (k-1) := by
  -- Use m_{k} * d_{k-1} = a_{k-1} and n_{k} * d_{k-1} = b_{k-1}
  obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  subst hj
  simp only [Nat.add_sub_cancel]
  have hm := m_eq_a_div_d s j
  have hn := n_eq_b_div_d s j
  -- delta_{j+1} = 2 * |m_{j+1} - n_{j+1}|
  rw [delta_eq_two_mul]
  -- delta_j = |a_j - b_j|
  simp only [delta]
  -- Goal: 2 * |m - n| * d = 2 * |a - b| where m * d = a and n * d = b
  have h1 : (s.m (j+1) - s.n (j+1) : Int).natAbs * d s j =
            (a s j - b s j : Int).natAbs := by
    have hm' : (s.m (j+1) : Int) * (d s j : Int) = (a s j : Int) := by
      simp only [← Nat.cast_mul, hm]
    have hn' : (s.n (j+1) : Int) * (d s j : Int) = (b s j : Int) := by
      simp only [← Nat.cast_mul, hn]
    calc (s.m (j+1) - s.n (j+1) : Int).natAbs * d s j
        = ((s.m (j+1) - s.n (j+1) : Int) * d s j).natAbs := by
            rw [Int.natAbs_mul]; simp
      _ = ((s.m (j+1) : Int) * d s j - (s.n (j+1) : Int) * d s j).natAbs := by
            ring_nf
      _ = (a s j - b s j : Int).natAbs := by rw [hm', hn']
  -- Now 2 * |m - n| * d = 2 * |a - b| follows from h1
  calc 2 * (s.m (j+1) - s.n (j+1) : Int).natAbs * d s j
      = 2 * ((s.m (j+1) - s.n (j+1) : Int).natAbs * d s j) := by ring
    _ = 2 * (a s j - b s j : Int).natAbs := by rw [h1]

-- Helper: oddPart 0 = 0
lemma oddPart_zero : oddPart 0 = 0 := by unfold oddPart; simp

-- Helper: oddPart(2 * n) = oddPart(n) for n > 0
lemma oddPart_two_mul (n : Nat) (hn : n > 0) : oddPart (2 * n) = oddPart n := by
  unfold oddPart
  have hne : n ≠ 0 := by omega
  have h2ne : 2 * n ≠ 0 := by omega
  simp only [hne, h2ne, ↓reduceIte]
  -- v_2(2n) = v_2(n) + 1
  have hfact : (2 * n).factorization 2 = n.factorization 2 + 1 := by
    rw [Nat.factorization_mul (by norm_num : 2 ≠ 0) hne]
    simp only [Finsupp.coe_add, Pi.add_apply, Nat.Prime.factorization_self Nat.prime_two]
    ring
  rw [hfact, pow_succ]
  -- pow_succ gives 2^(k+1) = 2 * 2^k
  -- Goal: 2 * n / (2 * 2^k) = n / 2^k
  have h : 2 * n / (2 * 2 ^ n.factorization 2) = n / 2 ^ n.factorization 2 :=
    Nat.mul_div_mul_left n (2 ^ n.factorization 2) (by omega : 0 < 2)
  convert h using 2 <;> ring

-- The odd part decreases: oddPart(delta_k) * d_{k-1} = oddPart(delta_{k-1})
lemma oddPart_descent (s : PutnamSeq) (k : Nat) (hk : k > 0) :
    oddPart (delta s k) * d s (k-1) = oddPart (delta s (k-1)) := by
  -- From delta_recurrence: delta_k * d_{k-1} = 2 * delta_{k-1}
  have hrec := delta_recurrence s k hk
  have hdelta_pos := delta_pos s (k - 1)
  have hdelta_k_pos := delta_pos s k
  -- d_{k-1} is odd and positive
  have hd_odd : Odd (d s (k - 1)) := by
    have h := d_coprime_two s (k - 1)
    rw [Nat.coprime_comm, Nat.coprime_two_right] at h
    exact h
  have hd_pos : 0 < d s (k - 1) := by
    unfold d
    exact Nat.gcd_pos_of_pos_left _ (by unfold a; omega)

  -- Key: oddPart(n * d) = oddPart(n) * d when d is odd
  have hoddPart_mul_odd {n d' : Nat} (hn_pos : n > 0) (hd'_odd : Odd d') :
      oddPart (n * d') = oddPart n * d' := by
    by_cases hd'_zero : d' = 0
    · simp [hd'_zero, oddPart_zero]
    · unfold oddPart
      have hne : n ≠ 0 := by omega
      have hprod_ne : n * d' ≠ 0 := Nat.mul_ne_zero hne hd'_zero
      simp only [hne, hprod_ne, ↓reduceIte]
      -- factorization(n * d') at 2 = factorization(n) at 2 (since d' is odd)
      have hd'_fact : d'.factorization 2 = 0 := by
        rw [Nat.odd_iff] at hd'_odd
        exact Nat.factorization_eq_zero_of_not_dvd (fun h => by omega : ¬ 2 ∣ d')
      have hfact : (n * d').factorization 2 = n.factorization 2 := by
        rw [Nat.factorization_mul hne hd'_zero]
        simp only [Finsupp.coe_add, Pi.add_apply, hd'_fact, add_zero]
      rw [hfact]
      have hdvd : 2 ^ n.factorization 2 ∣ n := Nat.ordProj_dvd n 2
      -- n * d' / 2^k = (n / 2^k) * d'
      calc n * d' / 2 ^ n.factorization 2
          = d' * n / 2 ^ n.factorization 2 := by ring_nf
        _ = d' * (n / 2 ^ n.factorization 2) := Nat.mul_div_assoc d' hdvd
        _ = n / 2 ^ n.factorization 2 * d' := by ring

  -- Apply: oddPart(delta_k * d) = oddPart(delta_k) * d
  have heq := hoddPart_mul_odd hdelta_k_pos hd_odd
  rw [← heq, hrec]
  exact oddPart_two_mul (delta s (k - 1)) hdelta_pos

-- When d_k > 1, since d_k is odd, we have d_k >= 3
lemma d_ge_three (s : PutnamSeq) (k : Nat) (hd : d s k > 1) : d s k ≥ 3 := by
  have hodd := d_coprime_two s k
  -- d_k is odd and > 1, so d_k >= 3
  unfold Nat.Coprime at hodd
  rw [Nat.gcd_comm] at hodd
  simp only [Nat.coprime_two_right, Nat.odd_iff] at hodd
  omega

-- Helper: oddPart is positive for positive inputs
lemma oddPart_pos {n : Nat} (hn : n > 0) : oddPart n > 0 := by
  unfold oddPart
  have hne : n ≠ 0 := by omega
  simp only [hne, ↓reduceIte]
  have hdvd : 2 ^ n.factorization 2 ∣ n := Nat.ordProj_dvd n 2
  have hpow_pos : 0 < 2 ^ n.factorization 2 := Nat.pow_pos (by omega : 0 < 2)
  exact Nat.div_pos (Nat.le_of_dvd hn hdvd) hpow_pos

-- Key: when d_k > 1, oddPart(delta_{k+1}) < oddPart(delta_k)
lemma oddPart_strict_descent (s : PutnamSeq) (k : Nat) (hd : d s k > 1) :
    oddPart (delta s (k + 1)) < oddPart (delta s k) := by
  have hdescent := oddPart_descent s (k + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hdescent
  have hdelta_pos := delta_pos s k
  have hoddPart_pos := oddPart_pos hdelta_pos
  have hd_ge := d_ge_three s k hd
  have hoddPart_k1_pos := oddPart_pos (delta_pos s (k + 1))
  -- oddPart(delta_{k+1}) * d_k = oddPart(delta_k)
  -- Since d_k >= 3, we have oddPart(delta_{k+1}) * 3 ≤ oddPart(delta_k)
  -- So oddPart(delta_{k+1}) < oddPart(delta_k) (since oddPart(delta_{k+1}) >= 1)
  have h : oddPart (delta s (k + 1)) * d s k = oddPart (delta s k) := hdescent
  have h2 : oddPart (delta s (k + 1)) * 3 ≤ oddPart (delta s (k + 1)) * d s k := by
    apply Nat.mul_le_mul_left
    exact hd_ge
  have h3 : oddPart (delta s (k + 1)) * 3 ≤ oddPart (delta s k) := by
    calc oddPart (delta s (k + 1)) * 3
        ≤ oddPart (delta s (k + 1)) * d s k := h2
      _ = oddPart (delta s k) := h
  -- Since oddPart(delta_{k+1}) >= 1, we have 3 * oddPart(delta_{k+1}) >= 3 > 1
  -- And oddPart(delta_{k+1}) < oddPart(delta_{k+1}) * 3 ≤ oddPart(delta_k)
  have h4 : oddPart (delta s (k + 1)) < oddPart (delta s (k + 1)) * 3 := by
    calc oddPart (delta s (k + 1))
        = oddPart (delta s (k + 1)) * 1 := by ring
      _ < oddPart (delta s (k + 1)) * 3 := by
          apply Nat.mul_lt_mul_of_pos_left (by omega : 1 < 3) hoddPart_k1_pos
  omega

-- The set of k where d_k > 1 is finite
-- Proof: When d_k > 1, oddPart(delta_{k+1}) < oddPart(delta_k)
-- Since oddPart is always positive, this can happen finitely many times
lemma finite_bad_indices (s : PutnamSeq) :
    Set.Finite {k : Nat | d s k > 1} := by
  -- First, show oddPart is weakly decreasing overall
  have hweak : ∀ k, oddPart (delta s (k + 1)) ≤ oddPart (delta s k) := fun k => by
    have hdescent := oddPart_descent s (k + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hdescent
    have hd_pos : 0 < d s k := Nat.gcd_pos_of_pos_left _ (by unfold a; omega)
    calc oddPart (delta s (k + 1))
        ≤ oddPart (delta s (k + 1)) * d s k := Nat.le_mul_of_pos_right _ hd_pos
      _ = oddPart (delta s k) := hdescent

  -- Show oddPart(delta_k) ≤ oddPart(delta_0) by induction
  have hbound : ∀ k, oddPart (delta s k) ≤ oddPart (delta s 0) := fun k => by
    induction k with
    | zero => rfl
    | succ k ih =>
      calc oddPart (delta s (k + 1))
          ≤ oddPart (delta s k) := hweak k
        _ ≤ oddPart (delta s 0) := ih

  -- Show oddPart(delta_{k1+1}) ≥ oddPart(delta_{k2}) when k1 + 1 ≤ k2
  have hmono : ∀ k1 k2, k1 + 1 ≤ k2 → oddPart (delta s (k1 + 1)) ≥ oddPart (delta s k2) := by
    intro k1 k2 hle
    have hchain : ∀ n, oddPart (delta s (k1 + 1 + n)) ≤ oddPart (delta s (k1 + 1)) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc oddPart (delta s (k1 + 1 + (n + 1)))
            = oddPart (delta s ((k1 + 1 + n) + 1)) := by ring_nf
          _ ≤ oddPart (delta s (k1 + 1 + n)) := hweak _
          _ ≤ oddPart (delta s (k1 + 1)) := ih
    have heq : k2 = k1 + 1 + (k2 - k1 - 1) := by omega
    rw [heq]; exact hchain _

  -- Define the injection f(k) = oddPart(delta_{k+1})
  let f : Nat → Nat := fun k => oddPart (delta s (k + 1))

  -- f maps bad indices into {0, ..., oddPart(delta_0) - 1}
  have hf_range : f '' {k : Nat | d s k > 1} ⊆ Set.Iio (oddPart (delta s 0)) := by
    intro y hy
    obtain ⟨k, hk, hfk⟩ := hy
    simp only [Set.mem_Iio]
    rw [← hfk]
    have h1 := oddPart_strict_descent s k hk
    have h2 := hbound k
    calc f k = oddPart (delta s (k + 1)) := rfl
      _ < oddPart (delta s k) := h1
      _ ≤ oddPart (delta s 0) := h2

  -- f is injective on bad indices
  have hf_inj : Set.InjOn f {k : Nat | d s k > 1} := by
    intro k1 hk1 k2 hk2 heq
    simp only [Set.mem_setOf_eq] at hk1 hk2
    by_contra hne
    -- WLOG k1 < k2
    cases' Nat.lt_or_gt_of_ne hne with hlt hgt
    · -- k1 < k2
      -- f(k1) = oddPart(delta_{k1+1}) ≥ oddPart(delta_{k2}) > oddPart(delta_{k2+1}) = f(k2)
      have h_ge := hmono k1 k2 (by omega : k1 + 1 ≤ k2)
      have h_strict := oddPart_strict_descent s k2 hk2
      have hcontra : oddPart (delta s (k1 + 1)) > oddPart (delta s (k2 + 1)) :=
        Nat.lt_of_lt_of_le h_strict h_ge
      -- heq : f k1 = f k2, i.e., oddPart(delta_{k1+1}) = oddPart(delta_{k2+1})
      have heq' : oddPart (delta s (k1 + 1)) = oddPart (delta s (k2 + 1)) := heq
      omega
    · -- k2 < k1
      have h_ge := hmono k2 k1 (by omega : k2 + 1 ≤ k1)
      have h_strict := oddPart_strict_descent s k1 hk1
      have hcontra : oddPart (delta s (k2 + 1)) > oddPart (delta s (k1 + 1)) :=
        Nat.lt_of_lt_of_le h_strict h_ge
      have heq' : oddPart (delta s (k2 + 1)) = oddPart (delta s (k1 + 1)) := heq.symm
      omega

  -- Image is finite (subset of finite set)
  have himg_fin : Set.Finite (f '' {k : Nat | d s k > 1}) :=
    Set.Finite.subset (Set.finite_lt_nat (oddPart (delta s 0))) hf_range

  -- Conclude using injective image
  exact Set.Finite.of_finite_image himg_fin hf_inj

-- Main theorem: eventually gcd = 1
theorem eventually_coprime (s : PutnamSeq) :
    ∃ K : Nat, ∀ k, K ≤ k → Nat.Coprime (a s k) (b s k) := by
  -- Get finite set of bad indices
  have hfin := finite_bad_indices s
  obtain ⟨S, hS⟩ := hfin.exists_finset_coe
  -- Take K = max of S + 1 (or 0 if S is empty)
  use (S.sup id) + 1
  intro k hk
  -- k > all elements of S, so d_k = 1
  by_contra hd
  -- gcd(a_k, b_k) ≠ 1 means d_k > 1
  have hk_bad : d s k > 1 := by
    unfold d a b at *
    have hgcd_pos : 0 < Nat.gcd (2 * s.m k + 1) (2 * s.n k + 1) :=
      Nat.gcd_pos_of_pos_left _ (by omega)
    unfold Nat.Coprime at hd
    omega
  have hk_in_set : k ∈ {j : Nat | d s j > 1} := hk_bad
  rw [← hS] at hk_in_set
  simp only [Finset.mem_coe] at hk_in_set
  have hk_le : k ≤ S.sup id := Finset.le_sup (f := id) hk_in_set
  have : S.sup id + 1 ≤ k := hk
  linarith

end Putnam2025A1
