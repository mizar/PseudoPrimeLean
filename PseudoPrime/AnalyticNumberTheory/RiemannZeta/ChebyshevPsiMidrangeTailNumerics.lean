/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiMidrangeMain
import PseudoPrime.Analysis.LogTaylorBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Rational estimates for the initial midrange tail -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The positive zero-tail coefficient in the initial midrange is at most
191/50. Rational logarithm and π bounds control its quadratic numerator. -/
theorem midrange_tail_coefficient {L : ℝ} (hl : (13815 / 1000 : ℝ) ≤ L) (hu : L ≤ 1386 / 100) :
    let a := L / 2 - Real.log (5 * L / 6)
    (a ^ 2 + 2 * a + 2) / (2 * Real.pi) - 143 / 125 ≤ (191 / 50 : ℝ) := by
  dsimp only
  let a := L / 2 - Real.log (5 * L / 6)
  have hL : 0 < L := by linarith only [hl]
  have harg : (23 / 2 : ℝ) ≤ 5 * L / 6 := by linarith only [hl]
  have hc :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck (23 / 2) 3 64 (244 / 100) (245 / 100) = true from by
        decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have hloglo := Real.log_le_log (by norm_num only : (0 : ℝ) < 23 / 2) harg
  have hloghi :=
    Real.log_le_log (by linarith only [hL] : 0 < 5 * L / 6)
      (show 5 * L / 6 ≤ L by linarith only [hL])
  have hab := midrange_log_bounds hl
  have ha0 : 0 ≤ a := by
    dsimp only [a]; linarith only [hloghi, hab.2, hL]
  have hau : a ≤ 449 / 100 := by
    dsimp only [a]; linarith only [hu, hloglo, hc.1]
  have hasq := pow_le_pow_left₀ ha0 hau 2
  have hb : (a ^ 2 + 2 * a + 2) / (2 * Real.pi) ≤ (191 / 50 : ℝ) + 143 / 125 := by
    apply (div_le_iff₀ (by nlinarith only [Real.pi_pos] : 0 < 2 * Real.pi)).2
    nlinarith only [hau, hasq, Real.pi_gt_d4]
  change (a ^ 2 + 2 * a + 2) / (2 * Real.pi) - 143 / 125 ≤ _
  linarith only [hb]

/-- The logarithmic smoothing constant is at most 1838/1000, as certified by
a rational logarithm interval and an upper bound for π. -/
theorem midrange_log_two_pi_le : Real.log (2 * Real.pi) ≤ (1838 / 1000 : ℝ) := by
  have hc :=
    Analysis.rationalLogIntervalCheck_sound
      (show
        Analysis.rationalLogIntervalCheck (62832 / 10000) 2 64 (1837 / 1000) (1838 / 1000) = true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have hp : (2 * Real.pi : ℝ) ≤ 62832 / 10000 := by linarith only [Real.pi_lt_d4]
  have hl := Real.log_le_log (by nlinarith only [Real.pi_pos] : (0 : ℝ) < 2 * Real.pi) hp
  linarith only [hl, hc.2]

/-- Explicit bounds for width, height, and the tail coefficient make the
initial normalized remainder at most 9/500 after retaining the cutoff gain. -/
theorem midrange_remainder_arithmetic {δ B c s x : ℝ} (hd : (7 / 2000 : ℝ) ≤ δ)
    (hdu : δ ≤ 37 / 10000) (hB : B ≤ 191 / 50) (hc : c ≤ 1838 / 1000) (hs : 1000 ≤ s)
    (hx : 1000000 ≤ x) :
    c / s + δ * (127 / 250) / 4 + 527 / 250000 + δ * B - 21 / 32000 + (1 + δ) * δ ^ 2 / 60 +
        1 / (x * δ * s) ≤
      (9 / 500 : ℝ) := by
  have hδ0 : 0 < δ := by linarith only [hd]
  have hs0 : 0 < s := by linarith only [hs]
  have hx0 : 0 < x := by linarith only [hx]
  have hcs : c / s ≤ (1838 / 1000000 : ℝ) := by
    apply (div_le_iff₀ hs0).2
    linarith only [hc, hs]
  have hterm := mul_le_mul_of_nonneg_left hB hδ0.le
  have hδB : δ * B ≤ (7067 / 500000 : ℝ) := by nlinarith only [hterm, hdu]
  have hsq : δ ^ 2 ≤ (37 / 10000 : ℝ) ^ 2 := by nlinarith only [hδ0, hdu]
  have hmul :=
    mul_le_mul (show 1 + δ ≤ (10037 / 10000 : ℝ) by linarith only [hdu]) hsq (sq_nonneg δ)
      (by norm_num only : (0 : ℝ) ≤ 10037 / 10000)
  have hsmall : (1 + δ) * δ ^ 2 / 60 ≤ (1 / 4000000 : ℝ) := by nlinarith only [hmul]
  have hxδ := mul_le_mul hx hd (by norm_num only : (0 : ℝ) ≤ 7 / 2000) hx0.le
  have hxδs := mul_le_mul hxδ hs (by norm_num only : (0 : ℝ) ≤ 1000) (mul_nonneg hx0.le hδ0.le)
  have hden : (0 : ℝ) < x * δ * s := mul_pos (mul_pos hx0 hδ0) hs0
  have hrem : 1 / (x * δ * s) ≤ (1 / 3500000 : ℝ) := by
    apply (div_le_iff₀ hden).2
    nlinarith only [hxδs]
  nlinarith only [hcs, hδB, hsmall, hrem, hdu]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
