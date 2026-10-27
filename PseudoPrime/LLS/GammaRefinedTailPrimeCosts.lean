/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaRefinedTailErrorBounds
public import PseudoPrime.LLS.GammaQuadraticLocalBudget

/-! # Prime-factor ramp costs in the refined logarithmic tail -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For odd n with log n at least 15000 and shifts from ten to fifteen,
the prime-factor ramp cost of level 4n is at most five. Retain the elementary
omega bound's loglog denominator and the cutoff bound by twice loglog n.
This supplies a uniform local budget for the refined tail profiles. -/
theorem gamma_tail_original_prime_factor_cost {n : ℕ} (hn : Odd n) (hL : 15000 ≤ Real.log n) {c : ℝ}
    (hc : 10 ≤ c) (hcu : c ≤ 15) :
    ((4 * n).primeFactors.card : ℝ) *
          Real.log ((99 / 40 : ℝ) * Analysis.gammaTailProfileScale (Real.log n) c) /
        Real.sqrt (Analysis.gammaTailProfileScale (Real.log n) c) ≤
      5 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Odd.pos hn
  have hn750 : 750 ≤ n := by
    have hself := Real.log_le_self hnR.le
    have hr : (750 : ℝ) ≤ n := by linarith only [hL, hself]
    exact_mod_cast hr
  have hL0 : 0 < Real.log n := by linarith only [hL]
  have hlogq := log_original_quadratic_level (Odd.pos hn)
  have hqlo : Real.log n ≤ Real.log (4 * n : ℕ) := by
    rw [hlogq]
    linarith only [Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 4)]
  have hqhi : Real.log (4 * n : ℕ) ≤ Real.log n + 2 := by
    rw [hlogq]
    linarith only [log_four_le_two]
  have hdpos : 0 < Real.log (Real.log (4 * n : ℕ)) := Real.log_pos (by linarith only [hqlo, hL])
  have hloglo := Real.log_le_log hL0 hqlo
  have hcut := Analysis.gamma_tail_cutoff_log_le_twice_log hL hc hcu
  have hcutden :
    Real.log ((99 / 40 : ℝ) * Analysis.gammaTailProfileScale (Real.log n) c) ≤
      2 * Real.log (Real.log (4 * n : ℕ)) := by
    linarith only [hcut, hloglo]
  have hw := AnalyticNumberTheory.Arithmetic.elementaryOmegaStatement n hn hn750
  change
    ((4 * n).primeFactors.card : ℝ) ≤
      (7 / 5 : ℝ) * Real.log (4 * n : ℕ) / Real.log (Real.log (4 * n : ℕ)) at hw
  have hwmul := (le_div_iff₀ hdpos).mp hw
  have hterm :=
    mul_le_mul_of_nonneg_left hcutden
      (Nat.cast_nonneg (4 * n).primeFactors.card : (0 : ℝ) ≤ (4 * n).primeFactors.card)
  have hbudget :
    ((4 * n).primeFactors.card : ℝ) *
        Real.log ((99 / 40 : ℝ) * Analysis.gammaTailProfileScale (Real.log n) c) ≤
      (14 / 5 : ℝ) * Real.log (4 * n : ℕ) := by
    nlinarith only [hwmul, hterm]
  have hroot := Analysis.gamma_tail_scale_sqrt_lower hL hc
  have hs : 0 < Real.sqrt (Analysis.gammaTailProfileScale (Real.log n) c) := by
    linarith only [hroot, hL]
  rw [div_le_iff₀ hs]
  nlinarith only [hbudget, hqhi, hroot, hL]

/-- For the same odd input and tail profile, the prime-factor cost of n
is at most five. Its prime factors form a subset of those of 4n and the
cutoff logarithm is nonnegative. This matches the finite coarse comparison. -/
theorem gamma_tail_input_prime_factor_cost {n : ℕ} (hn : Odd n) (hL : 15000 ≤ Real.log n) {c : ℝ}
    (hc : 10 ≤ c) (hcu : c ≤ 15) :
    (n.primeFactors.card : ℝ) *
        (Real.log ((99 / 40 : ℝ) * Analysis.gammaTailProfileScale (Real.log n) c) /
          Real.sqrt (Analysis.gammaTailProfileScale (Real.log n) c)) ≤
      5 := by
  have hn0 : n ≠ 0 := (Odd.pos hn).ne'
  have hcard : (n.primeFactors.card : ℝ) ≤ (4 * n).primeFactors.card := by
    exact_mod_cast
      Finset.card_le_card
        (Nat.primeFactors_mono (dvd_mul_left n 4)
          (mul_ne_zero (by norm_num only : (4 : ℕ) ≠ 0) hn0))
  have hx := Analysis.gamma_tail_scale_large hL hc
  have hX : 1 ≤ (99 / 40 : ℝ) * Analysis.gammaTailProfileScale (Real.log n) c := by
    nlinarith only [hx]
  have hnonneg :=
    div_nonneg (Real.log_nonneg hX)
      (Real.sqrt_nonneg (Analysis.gammaTailProfileScale (Real.log n) c))
  have hm := mul_le_mul_of_nonneg_right hcard hnonneg
  have hb := gamma_tail_original_prime_factor_cost hn hL hc hcu
  rw [mul_div_assoc] at hb
  exact hm.trans hb

end PseudoPrime.LLS
