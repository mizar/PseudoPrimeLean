/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiMidrangeMain
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiMidrangeScaleRH
import PseudoPrime.Analysis.LogTaylorBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Rational estimates through log height 20 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Canonical width is at most 1/500 in the extended interval. -/
theorem midrange_post20_delta_upper {x : ℝ} (hl : (1596 / 100 : ℝ) ≤ Real.log x)
    (hu : Real.log x ≤ (20 : ℝ)) (hx : 0 < x) :
    (5 * Real.log x / (6 * Real.pi)) / Real.sqrt x ≤ (1 / 500 : ℝ) := by
  let q := 5 * Real.log x / (6 * Real.pi)
  let s := Real.sqrt x
  have hs : 0 < s := Real.sqrt_pos.2 hx
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx.le
  have hc :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 2800 12 64 (793 / 100) (794 / 100) = true from by
        decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have he : Real.log ((2800 : ℝ) ^ 2) = 2 * Real.log 2800 := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hxlow : (2800 : ℝ) ^ 2 ≤ x := by
    apply (Real.log_le_log_iff (by norm_num only : (0 : ℝ) < (2800 : ℝ) ^ 2) hx).mp
    linarith only [hl, hc.2, he]
  have hslow : 2800 ≤ s := by nlinarith only [hs, hs2, hxlow]
  have hq : q ≤ 28 / 5 := by
    dsimp only [q]
    apply (div_le_iff₀ (by nlinarith only [Real.pi_pos] : 0 < 6 * Real.pi)).2
    nlinarith only [hu, Real.pi_gt_three]
  change q / s ≤ _
  apply (div_le_iff₀ hs).2
  linarith only [hq, hslow]

/-- Canonical width is at least 1/10000 on the later midrange. -/
theorem midrange_post20_delta_lower {x : ℝ} (ha : 1000000 ≤ x) (hu : Real.log x ≤ (20 : ℝ)) :
    (1 / 10000 : ℝ) ≤ (5 * Real.log x / (6 * Real.pi)) / Real.sqrt x := by
  let q := 5 * Real.log x / (6 * Real.pi)
  let s := Real.sqrt x
  have hx : 0 < x := by linarith only [ha]
  have hs : 0 < s := Real.sqrt_pos.2 hx
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx.le
  have hc :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 23000 15 64 (10 : ℚ) (101 / 10) = true from by
        decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have he : Real.log ((23000 : ℝ) ^ 2) = 2 * Real.log 23000 := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hxupper : x ≤ (23000 : ℝ) ^ 2 := by
    apply (Real.log_le_log_iff hx (by norm_num only : (0 : ℝ) < (23000 : ℝ) ^ 2)).mp
    linarith only [hu, hc.1, he]
  have hsupper : s ≤ 23000 := by nlinarith only [hs, hs2, hxupper]
  have hq : (23 / 10 : ℝ) ≤ q := by
    dsimp only [q]
    apply (le_div_iff₀ (by nlinarith only [Real.pi_pos] : 0 < 6 * Real.pi)).2
    have hll := log_million_lower ha
    nlinarith only [hll, Real.pi_lt_d4]
  change _ ≤ q / s
  apply (le_div_iff₀ hs).2
  linarith only [hq, hsupper]

/-- The later midrange zero-tail coefficient is at most eleven. -/
theorem midrange_post20_tail_coefficient {L : ℝ} (hl : (1596 / 100 : ℝ) ≤ L) (hu : L ≤ 20) :
    let a := L / 2 - Real.log (5 * L / 6)
    (a ^ 2 + 2 * a + 2) / (2 * Real.pi) - 143 / 125 ≤ (11 : ℝ) := by
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
  have hab := midrange_log_bounds (show (13815 / 1000 : ℝ) ≤ L by linarith only [hl])
  have ha0 : 0 ≤ a := by
    dsimp only [a]; linarith only [hloghi, hab.2, hL]
  have hau : a ≤ 189 / 25 := by
    dsimp only [a]; linarith only [hu, hloglo, hc.1]
  have hasq := pow_le_pow_left₀ ha0 hau 2
  have hb : (a ^ 2 + 2 * a + 2) / (2 * Real.pi) ≤ (11 : ℝ) + 143 / 125 := by
    apply (div_le_iff₀ (by nlinarith only [Real.pi_pos] : 0 < 2 * Real.pi)).2
    nlinarith only [hau, hasq, Real.pi_gt_d4]
  change (a ^ 2 + 2 * a + 2) / (2 * Real.pi) - 143 / 125 ≤ _
  linarith only [hb]

/-- The extended midrange smoothing remainder is at most 3/100. -/
theorem midrange_post20_remainder {δ B c s x : ℝ} (hd : (1 / 10000 : ℝ) ≤ δ) (hdu : δ ≤ 1 / 500)
    (hB : B ≤ 11) (hc : c ≤ 1838 / 1000) (hs : 1000 ≤ s) (hx : 1000000 ≤ x) :
    c / s + δ * (61 / 100) / 4 + 613 / 250000 + δ * B + (1 + δ) * δ ^ 2 / 60 + 1 / (x * δ * s) ≤
      (3 / 100 : ℝ) := by
  have hδ0 : 0 < δ := by linarith only [hd]
  have hs0 : 0 < s := by linarith only [hs]
  have hx0 : 0 < x := by linarith only [hx]
  have hcs : c / s ≤ (1838 / 1000000 : ℝ) := by
    apply (div_le_iff₀ hs0).2
    linarith only [hc, hs]
  have hterm := mul_le_mul_of_nonneg_left hB hδ0.le
  have hδB : δ * B ≤ (11 / 500 : ℝ) := by nlinarith only [hterm, hdu]
  have hsq : δ ^ 2 ≤ (1 / 500 : ℝ) ^ 2 := by nlinarith only [hδ0, hdu]
  have hmul :=
    mul_le_mul (show 1 + δ ≤ (501 / 500 : ℝ) by linarith only [hdu]) hsq (sq_nonneg δ)
      (by norm_num only : (0 : ℝ) ≤ 501 / 500)
  have hsmall : (1 + δ) * δ ^ 2 / 60 ≤ (1 / 1000000 : ℝ) := by nlinarith only [hmul]
  have hxδ := mul_le_mul hx hd (by norm_num only : (0 : ℝ) ≤ 1 / 10000) hx0.le
  have hxδs := mul_le_mul hxδ hs (by norm_num only : (0 : ℝ) ≤ 1000) (mul_nonneg hx0.le hδ0.le)
  have hden : (0 : ℝ) < x * δ * s := mul_pos (mul_pos hx0 hδ0) hs0
  have hrem : 1 / (x * δ * s) ≤ (1 / 100000 : ℝ) := by
    apply (div_le_iff₀ hden).2
    nlinarith only [hxδs]
  nlinarith only [hcs, hδB, hsmall, hrem, hdu]

/-- The phase main-term gap at 15.96 exceeds 23/100. -/
theorem midrange_main_gap_at_1596 :
    (23 / 100 : ℝ) < leeNosalPsiLog (1596 / 100) - midrangePhaseMain (1596 / 100) := by
  have hL :=
    Analysis.rationalLogIntervalCheck_sound
      (show
        Analysis.rationalLogIntervalCheck (1596 / 100) 4 64 (277008 / 100000) (277009 / 100000) =
          true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hL
  have hk :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck (6 / 5) 0 64 (18232 / 100000) (18233 / 100000) = true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hk
  have ha0 : 0 ≤ (1596 / 200 : ℝ) - Real.log (1596 / 100) + Real.log (6 / 5) := by
    linarith only [hL.2, hk.1]
  have hau :
    (1596 / 200 : ℝ) - Real.log (1596 / 100) + Real.log (6 / 5) ≤
      (1596 / 200 : ℝ) - 277008 / 100000 + 18233 / 100000 := by
    linarith only [hL.1, hk.2]
  have hasq := pow_le_pow_left₀ ha0 hau 2
  have hcomp :
    (-3743 / 10000 : ℝ) < leeNosalPsiLog (1596 / 100) - integratedPsiMain (1596 / 100) := by
    rw [integrated_main_gap_eq (by norm_num only : (0 : ℝ) < 1596 / 100)]
    apply (lt_div_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 8) Real.pi_pos)).2
    nlinarith only [hL.2, hk.2, hau, hasq, Real.pi_gt_d4]
  rw [midrange_main_eq]
  linarith only [hcomp]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
