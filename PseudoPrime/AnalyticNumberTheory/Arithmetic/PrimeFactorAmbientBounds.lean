/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactorSplitBounds

/-! # Ambient logarithmic bounds for the number of distinct prime factors -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For a positive level q at most A, bound its distinct prime count by 16+3log(A)/8.
Keep the small-factor cutoff cost rather than absorbing it into the logarithmic coefficient.
The proof splits at sixteen and uses log 16 at least 8/3; later analytic comparisons choose
their own coefficient and entrance scale without assuming a lower bound on log q. -/
theorem primeFactors_card_le_three_eighths_ambient_log {q A : ℕ} (hq : 0 < q) (hqA : q ≤ A) :
    (q.primeFactors.card : ℝ) ≤ 16 + (3 / 8 : ℝ) * Real.log A := by
  have hc := primeFactors_card_le_cutoff_add_log_div hq.ne' (show (1 : ℝ) < 16 by norm_num only)
  have h16 : (8 / 3 : ℝ) ≤ Real.log 16 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_gt_d9]
  have hp : 0 < Real.log 16 := by linarith only [h16]
  have hlog := Real.log_le_log (Nat.cast_pos.mpr hq) (Nat.cast_le.mpr hqA)
  have hL0 : 0 ≤ Real.log A :=
    Real.log_nonneg (Nat.one_le_cast.mpr (Nat.succ_le_of_lt (hq.trans_le hqA)))
  have hdiv : Real.log q / Real.log 16 ≤ (3 / 8 : ℝ) * Real.log A := by
    apply (div_le_iff₀ hp).mpr
    have h := mul_le_mul_of_nonneg_right h16 hL0
    nlinarith only [h, hlog]
  linarith only [hc, hdiv]

/-- For positive q at most A with log A at least 128, the number of distinct prime
factors of q is at most log(A)/2. Split the prime support at sixteen and use
log 16 at least 8/3. This uniform estimate covers small q as well and needs no RH. -/
theorem primeFactors_card_le_half_ambient_log {q A : ℕ} (hq : 0 < q) (hqA : q ≤ A)
    (hL : 128 ≤ Real.log A) : (q.primeFactors.card : ℝ) ≤ Real.log A / 2 := by
  have h := primeFactors_card_le_three_eighths_ambient_log hq hqA
  linarith only [h, hL]

/-- For a positive level q at most A with log A at least 640, bound its distinct prime count
by 2log(A)/5. Absorb the retained cutoff cost into the logarithmic budget.
This strengthens the half-logarithm estimate in finite-scale negative-witness comparisons. -/
theorem primeFactors_card_le_two_fifths_ambient_log {q A : ℕ} (hq : 0 < q) (hqA : q ≤ A)
    (hL : 640 ≤ Real.log A) : (q.primeFactors.card : ℝ) ≤ (2 / 5 : ℝ) * Real.log A := by
  have h := primeFactors_card_le_three_eighths_ambient_log hq hqA
  linarith only [h, hL]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
