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

/-! # Weak square-logarithmic psi estimate on the middle range -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH and the coarse positive-height zero count, the two-sided psi error
is at most `sqrt x * log x ^ 2 / 12` for `50000 ≤ x ≤ 1000000`. Use the
normalized explicit formula with width `x / 500` and zero cutoff `1000`. -/
theorem psi_error_square_twelve_middle (hRH : RiemannHypothesis) {x : ℝ} (ha : 50000 ≤ x)
    (hb : x ≤ 1000000)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          Real.log t) :
    |Chebyshev.psi x - x| ≤ Real.sqrt x * (Real.log x ^ 2 / 12) := by
  have hx0 : 0 < x := by linarith only [ha]
  let r : ℝ := Real.sqrt x
  have hrlo : (200 : ℝ) ≤ r := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [ha]
  have hrhi : r ≤ 1000 := by
    have h := Real.sqrt_le_sqrt (show x ≤ (1000 : ℝ) ^ 2 by nlinarith only [hb])
    rw [Real.sqrt_sq (by norm_num only)] at h
    exact h
  have hr0 : 0 < r := by linarith only [hrlo]
  have hrsq : r ^ 2 = x := Real.sq_sqrt hx0.le
  let δ : ℝ := 1 / 500
  let h : ℝ := x / 500
  have hd0 : 0 < δ := by
    dsimp only [δ]; norm_num only
  have hd2 : δ ≤ 1 / 2 := by
    dsimp only [δ]; norm_num only
  have hh : 0 < h := by
    dsimp only [h]; exact div_pos hx0 (by norm_num only)
  have hmid : 1 < x - h := by
    dsimp only [h]; linarith only [ha]
  have hT : 1000 ≤ 2 / δ := by
    dsimp only [δ]; norm_num only
  have hwidth : h = x * δ := by
    dsimp only [h, δ]; ring
  have hn := psi_error_normalized_coarse hRH hx0 hh hmid hT hd0 hd2 hwidth hQ
  have hc5 : Analysis.preciseLogCheck 50000 16 32 (54 / 5) 11 = true := by decide +kernel
  have hl5 := (Analysis.preciseLogCheck_sound hc5).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hl5
  have hlx : (54 / 5 : ℝ) ≤ Real.log x := hl5.trans (Real.log_le_log (by norm_num only) ha)
  have hc1 : Analysis.preciseLogCheck 1000 10 32 6 7 = true := by decide +kernel
  have hl1 := (Analysis.preciseLogCheck_sound hc1).2
  norm_num only [Rat.cast_ofNat] at hl1
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  have hA0 : 0 ≤ Real.log (1000 / (2 * Real.pi)) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hp).2
    linarith only [Real.pi_lt_four]
  have hA : Real.log (1000 / (2 * Real.pi)) ≤ (11 / 2 : ℝ) := by
    rw [Real.log_div (by norm_num only) hp.ne']
    linarith only [hl1, Analysis.log_two_mul_pi_gt]
  have hA2 : Real.log (1000 / (2 * Real.pi)) ^ 2 ≤ (121 / 4 : ℝ) := by nlinarith only [hA0, hA]
  have hAd :=
    div_le_div_of_nonneg_left (sq_nonneg (Real.log (1000 / (2 * Real.pi))))
      (show (0 : ℝ) < 6 by norm_num only)
      (show (6 : ℝ) ≤ 2 * Real.pi by linarith only [Real.pi_gt_three])
  have hAb : Real.log (1000 / (2 * Real.pi)) ^ 2 / (2 * Real.pi) ≤ (121 / 24 : ℝ) := by
    linarith only [hAd, hA2]
  have hl10 : 0 ≤ Real.log (1000 : ℝ) := Real.log_nonneg (by norm_num only)
  have hld := div_le_div_of_nonneg_left hl10 (show (0 : ℝ) < 3 by norm_num only) Real.pi_gt_three.le
  have hlb : Real.log (1000 : ℝ) / Real.pi ≤ (7 / 3 : ℝ) := by linarith only [hld, hl1]
  have hfirst : h / (2 * r) ≤ 1 := by
    apply (div_le_one₀ (mul_pos (by norm_num only) hr0)).2
    dsimp only [h]
    have hm := mul_nonneg hr0.le (sub_nonneg.mpr hrhi)
    nlinarith only [hrsq, hm]
  have hsecond : Real.log (2 * Real.pi) / r ≤ (1 / 100 : ℝ) := by
    apply (div_le_iff₀ hr0).2
    linarith only [hrlo, Analysis.log_two_mul_pi_lt]
  have hh100 : (100 : ℝ) ≤ h := by
    dsimp only [h]; linarith only [ha]
  have hprod := mul_le_mul hh100 hrlo (by norm_num only : (0 : ℝ) ≤ 200) hh.le
  have hlast : 1 / (h * r) ≤ (1 / 16000 : ℝ) := by
    apply (div_le_iff₀ (mul_pos hh hr0)).2
    linarith only [hprod]
  change
    |Chebyshev.psi x - x| / r ≤
      h / (2 * r) + Real.log (2 * Real.pi) / r +
        (1 + δ / 2) * (Real.log ((2 / δ) / (2 * Real.pi)) ^ 2 / (2 * Real.pi) + 1) +
        (1 + δ) * Real.log (2 / δ) / Real.pi +
        1 / (h * r) at hn
  norm_num only [δ] at hn
  rw [mul_div_assoc] at hn
  have hnorm : |Chebyshev.psi x - x| / r ≤ (450997 / 48000 : ℝ) := by
    linarith only [hn, hfirst, hsecond, hAb, hlb, hlast]
  have hlog2 : (54 / 5 : ℝ) ^ 2 ≤ Real.log x ^ 2 := by nlinarith only [hlx]
  have hL : (450997 / 48000 : ℝ) ≤ Real.log x ^ 2 / 12 := by nlinarith only [hlog2]
  have hfinal := (div_le_iff₀ hr0).mp (hnorm.trans hL)
  change |Chebyshev.psi x - x| ≤ r * (Real.log x ^ 2 / 12)
  exact hfinal.trans_eq (mul_comm _ _)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
