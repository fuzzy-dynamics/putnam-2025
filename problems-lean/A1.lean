/-
  Putnam 2025 Problem A1 - Formalized Problem Statement

  Problem: Let m_0 and n_0 be distinct positive integers. For every positive integer k,
  define m_k and n_k to be the relatively prime positive integers such that
    m_k / n_k = (2*m_{k-1} + 1) / (2*n_{k-1} + 1)

  Prove that 2*m_k + 1 and 2*n_k + 1 are relatively prime for all but
  finitely many positive integers k.
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

namespace Putnam2025A1

/-- Main structure: the recurrence relation for the sequence -/
structure PutnamSeq where
  m : Nat → Nat
  n : Nat → Nat
  m_pos : ∀ k, 0 < m k
  n_pos : ∀ k, 0 < n k
  coprime : ∀ k, 0 < k → Nat.Coprime (m k) (n k)  -- Only for k > 0
  recurrence : ∀ k, (m (k+1)) * (2 * n k + 1) = (n (k+1)) * (2 * m k + 1)
  distinct_init : m 0 ≠ n 0

/-- Define a_k = 2*m_k + 1 -/
def a (s : PutnamSeq) (k : Nat) : Nat := 2 * s.m k + 1

/-- Define b_k = 2*n_k + 1 -/
def b (s : PutnamSeq) (k : Nat) : Nat := 2 * s.n k + 1

/-- Putnam 2025 A1: Eventually gcd(2*m_k + 1, 2*n_k + 1) = 1 -/
theorem putnam_2025_A1 (s : PutnamSeq) :
    ∃ K : Nat, ∀ k, K ≤ k → Nat.Coprime (a s k) (b s k) := by
  sorry

end Putnam2025A1
