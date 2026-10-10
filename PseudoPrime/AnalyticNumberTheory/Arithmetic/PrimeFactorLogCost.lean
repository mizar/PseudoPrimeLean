/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactors
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Combined logarithmic and cardinality costs of distinct prime factors

The negative logarithmic contribution of every prime at least five absorbs its
cardinality cost. Only two and three remain in the resulting uniform bound.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For a natural number at least five, a nonnegative scale `A` and a cost `t ≤ A/2`,
the logarithmic correction plus `t` is nonpositive. The denominator is at least
four and the prime's logarithm exceeds one, so the negative contribution is
at least `A/2`. This removes large primes from combined quotient costs. -/
private theorem prime_log_cost_nonpos {p : ℕ} (hp5 : 5 ≤ p) {A t : ℝ} (hA : 0 ≤ A)
    (ht : 2 * t ≤ A) : A * (2 * Real.log p / (p - 1) - Real.log p) + t ≤ 0 := by
  have hpcast : (5 : ℝ) ≤ p := by exact_mod_cast hp5
  have hd : (0 : ℝ) < p - 1 := by linarith only [hpcast]
  have hl : (1 : ℝ) ≤ Real.log p := by
    have h :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 3)
        (le_trans (by norm_num only : (3 : ℝ) ≤ 5) hpcast)
    linarith only [h, Real.log_three_gt_d9]
  have hf : (2 : ℝ) / (p - 1) ≤ 1 / 2 := (div_le_iff₀ hd).mpr (by linarith only [hpcast])
  have hm : 2 * Real.log p / (p - 1) ≤ Real.log p / 2 := by
    have h := mul_le_mul_of_nonneg_right hf (zero_le_one.trans hl)
    simp only [div_eq_mul_inv] at h ⊢
    nlinarith only [h]
  have hs : 2 * Real.log p / (p - 1) - Real.log p ≤ -(1 / 2 : ℝ) := by linarith only [hm, hl]
  have ha := mul_le_mul_of_nonneg_left hs hA
  nlinarith only [ha, ht]

/-- For a nonzero natural number, a nonnegative scale `A`, and a nonnegative
cost `t ≤ A/2`, twice the prime-factor logarithmic weight minus the level logarithm,
scaled by `A`, plus `t` per prime factor is at most `A log 2 + 2t`.
The product of distinct primes bounds the logarithmic term, primes at least five
have nonpositive combined cost, and only two and three can contribute positively.
This combines level-change errors without an unbounded prime-factor count. -/
theorem primeFactorLogCost_le {n : ℕ} (hn : n ≠ 0) {A t : ℝ} (hA : 0 ≤ A) (ht0 : 0 ≤ t)
    (ht : 2 * t ≤ A) :
    A * (2 * primeFactorLogSum n - Real.log n) + (n.primeFactors.card : ℝ) * t ≤
      A * Real.log 2 + 2 * t := by
  have hlog := sum_log_primeFactors_le_log hn
  have hsum :
    A * (2 * primeFactorLogSum n - ∑ p ∈ n.primeFactors, Real.log p) +
        (n.primeFactors.card : ℝ) * t =
      ∑ p ∈ n.primeFactors, (A * (2 * Real.log p / (p - 1) - Real.log p) + t) := by
    simp only [primeFactorLogSum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [mul_sub]
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have hpoint (p : ℕ) (hp : p ∈ n.primeFactors) :
    A * (2 * Real.log p / (p - 1) - Real.log p) + t ≤
      (if p = 2 then A * Real.log 2 + t else 0) + (if p = 3 then t else 0) := by
    by_cases h2 : p = 2
    · subst p
      norm_num only
      simp only [ite_true, ite_false, add_zero, div_one]
      linarith only []
    by_cases h3 : p = 3
    · subst p
      norm_num only at h2 ⊢
      simp only [ite_true, ite_false, zero_add]
      ring_nf
      exact le_refl _
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hodd := hprime.eq_two_or_odd.resolve_left h2
    have h4 : p ≠ 4 := by
      intro h
      rw [h] at hodd
      norm_num only at hodd
    have hp3 := Nat.succ_le_iff.mpr (lt_of_le_of_ne hprime.two_le (Ne.symm h2))
    have hp4 := Nat.succ_le_iff.mpr (lt_of_le_of_ne hp3 (Ne.symm h3))
    have hp5 := Nat.succ_le_iff.mpr (lt_of_le_of_ne hp4 (Ne.symm h4))
    simp only [ite_eq_right_iff.mpr fun h => (h2 h).elim, ite_eq_right_iff.mpr fun h => (h3 h).elim,
      zero_add]
    exact prime_log_cost_nonpos hp5 hA ht
  have hbound := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq'] at hbound
  have htwo : (if 2 ∈ n.primeFactors then A * Real.log 2 + t else 0) ≤ A * Real.log 2 + t := by
    split
    · exact le_refl _
    · exact add_nonneg (mul_nonneg hA (Real.log_nonneg (by norm_num only))) ht0
  have hthree : (if 3 ∈ n.primeFactors then t else 0) ≤ t := by
    split
    · exact le_refl _
    · exact ht0
  have hscale := mul_le_mul_of_nonneg_left hlog hA
  rw [Finset.sum_add_distrib] at hsum
  rw [← hsum] at hbound
  linarith only [hbound, hscale, htwo, hthree]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
