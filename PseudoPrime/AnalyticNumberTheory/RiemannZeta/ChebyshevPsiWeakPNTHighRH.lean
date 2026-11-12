/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountConjugation
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevScaleError
import PseudoPrime.Analysis.PreciseLogTaylorBounds
import PseudoPrime.Analysis.NumericalLogBounds

/-! # Weak square-logarithmic psi estimate on the upper half-line -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH and the coarse positive-height zero count, the two-sided psi error
is at most `sqrt x * log x ^ 2 / 12` for `x ≥ 1000000`. Use the normalized
explicit formula with width `2 * sqrt x` and zero cutoff `sqrt x`. -/
theorem psi_error_square_twelve_high (hRH : RiemannHypothesis) {x : ℝ} (hx : 1000000 ≤ x)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          Real.log t) :
    |Chebyshev.psi x - x| ≤ Real.sqrt x * (Real.log x ^ 2 / 12) := by
  have hx0 : 0 < x := by linarith only [hx]
  let r : ℝ := Real.sqrt x
  have hr : (1000 : ℝ) ≤ r := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hx]
  have hr0 : 0 < r := by linarith only [hr]
  have hrsq : r ^ 2 = x := Real.sq_sqrt hx0.le
  let δ : ℝ := 2 / r
  let h : ℝ := 2 * r
  have hd0 : 0 < δ := div_pos (by norm_num only) hr0
  have hd : δ ≤ 1 / 500 := by
    dsimp only [δ]
    apply (div_le_iff₀ hr0).2
    linarith only [hr]
  have hd2 : δ ≤ 1 / 2 := by linarith only [hd]
  have hh : 0 < h := mul_pos (by norm_num only) hr0
  have hmid : 1 < x - h := by
    dsimp only [h]; nlinarith only [hr, hrsq]
  have hT_eq : (2 : ℝ) / δ = r := by
    dsimp only [δ]
    exact div_div_cancel₀ (by norm_num only : (2 : ℝ) ≠ 0)
  have hT : 1000 ≤ 2 / δ := by
    rw [hT_eq]; exact hr
  have hwidth : h = x * δ := by
    dsimp only [h, δ]
    rw [← mul_div_assoc]
    apply (eq_div_iff hr0.ne').2
    nlinarith only [hrsq]
  have hn := psi_error_normalized_coarse hRH hx0 hh hmid hT hd0 hd2 hwidth hQ
  have hc : Analysis.preciseLogCheck 1000 10 32 6 7 = true := by decide +kernel
  have hl := (Analysis.preciseLogCheck_sound hc).1
  norm_num only [Rat.cast_ofNat] at hl
  have hu : (6 : ℝ) ≤ Real.log r := hl.trans (Real.log_le_log (by norm_num only) hr)
  have hu0 : 0 ≤ Real.log r := by linarith only [hu]
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  have hp1 : 1 ≤ 2 * Real.pi := by linarith only [Real.pi_gt_three]
  have hA0 : 0 ≤ Real.log (r / (2 * Real.pi)) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hp).2
    linarith only [hr, Real.pi_lt_four]
  have hAr : r / (2 * Real.pi) ≤ r := div_le_self hr0.le hp1
  have hA : Real.log (r / (2 * Real.pi)) ≤ Real.log r := Real.log_le_log (div_pos hr0 hp) hAr
  have hs := mul_nonneg (sub_nonneg.mpr hA) (add_nonneg hu0 hA0)
  have hA2 : Real.log (r / (2 * Real.pi)) ^ 2 ≤ Real.log r ^ 2 := by nlinarith only [hs]
  have hAd :=
    div_le_div_of_nonneg_left (sq_nonneg (Real.log (r / (2 * Real.pi))))
      (show (0 : ℝ) < 6 by norm_num only)
      (show (6 : ℝ) ≤ 2 * Real.pi by linarith only [Real.pi_gt_three])
  have hAb : Real.log (r / (2 * Real.pi)) ^ 2 / (2 * Real.pi) ≤ Real.log r ^ 2 / 6 := by
    linarith only [hAd, hA2]
  have hlb : Real.log r / Real.pi ≤ Real.log r / 3 :=
    div_le_div_of_nonneg_left hu0 (by norm_num only) Real.pi_gt_three.le
  have hfirst : h / (2 * r) = 1 := by
    dsimp only [h]
    exact div_self (mul_ne_zero (by norm_num only) hr0.ne')
  have hsecond : Real.log (2 * Real.pi) / r ≤ (1 / 500 : ℝ) := by
    apply (div_le_iff₀ hr0).2
    linarith only [hr, Analysis.log_two_mul_pi_lt]
  have hh2000 : (2000 : ℝ) ≤ h := by
    dsimp only [h]; linarith only [hr]
  have hprod := mul_le_mul hh2000 hr (by norm_num only : (0 : ℝ) ≤ 1000) hh.le
  have hlast : 1 / (h * r) ≤ (1 / 2000000 : ℝ) := by
    apply (div_le_iff₀ (mul_pos hh hr0)).2
    linarith only [hprod]
  have hAdiv0 : 0 ≤ Real.log (r / (2 * Real.pi)) ^ 2 / (2 * Real.pi) :=
    div_nonneg (sq_nonneg _) hp.le
  have hmA :=
    mul_le_mul (show 1 + δ / 2 ≤ (1001 / 1000 : ℝ) by linarith only [hd]) (add_le_add_right hAb 1)
      (by linarith only [hAdiv0]) (by norm_num only : (0 : ℝ) ≤ 1001 / 1000)
  have hB0 : 0 ≤ Real.log r / Real.pi := div_nonneg hu0 Real.pi_pos.le
  have hmB :=
    mul_le_mul (show 1 + δ ≤ (501 / 500 : ℝ) by linarith only [hd]) hlb hB0
      (by norm_num only : (0 : ℝ) ≤ 501 / 500)
  have hmB' : (1 + δ) * Real.log r / Real.pi ≤ (501 / 500 : ℝ) * (Real.log r / 3) := by
    rw [mul_div_assoc]
    exact hmB
  have hbudget :
    (1 : ℝ) + 1 / 500 + (1001 / 1000) * (Real.log r ^ 2 / 6 + 1) + (501 / 500) * (Real.log r / 3) +
        1 / 2000000 ≤
      Real.log r ^ 2 / 3 := by
    nlinarith only [hu, sq_nonneg (Real.log r - 6)]
  change
    |Chebyshev.psi x - x| / r ≤
      h / (2 * r) + Real.log (2 * Real.pi) / r +
        (1 + δ / 2) * (Real.log ((2 / δ) / (2 * Real.pi)) ^ 2 / (2 * Real.pi) + 1) +
        (1 + δ) * Real.log (2 / δ) / Real.pi +
        1 / (h * r) at hn
  rw [hT_eq] at hn
  have hnorm : |Chebyshev.psi x - x| / r ≤ Real.log r ^ 2 / 3 := by
    nlinarith only [hn, hfirst, hsecond, hmA, hmB', hlast, hbudget]
  have hlog : Real.log x = 2 * Real.log r := by
    have h := Real.log_sqrt hx0.le
    change Real.log r = Real.log x / 2 at h
    linarith only [h]
  have hfinal := (div_le_iff₀ hr0).mp hnorm
  change |Chebyshev.psi x - x| ≤ r * (Real.log x ^ 2 / 12)
  rw [hlog]
  nlinarith only [hfinal]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
