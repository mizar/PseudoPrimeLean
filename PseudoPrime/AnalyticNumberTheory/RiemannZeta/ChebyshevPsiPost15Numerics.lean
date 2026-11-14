/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiMidrangeTo15RH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevIntegratedMargin20RH
import PseudoPrime.Analysis.LogTaylorBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Rational estimates immediately above log height 15 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Canonical width is at most 1/250 near log height 15. -/
theorem midrange_post15_delta_upper {x : ℝ} (hl : (1423 / 100 : ℝ) ≤ Real.log x)
    (hu : Real.log x ≤ (151 / 10 : ℝ)) (hx : 0 < x) :
    (5 * Real.log x / (6 * Real.pi)) / Real.sqrt x ≤ (1 / 250 : ℝ) := by
  let q := 5 * Real.log x / (6 * Real.pi)
  let s := Real.sqrt x
  have hs : 0 < s := Real.sqrt_pos.2 hx
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx.le
  have hc :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 1229 10 64 (711 / 100) (7115 / 1000) = true from by
        decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have he : Real.log ((1229 : ℝ) ^ 2) = 2 * Real.log 1229 := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hxlow : (1229 : ℝ) ^ 2 ≤ x := by
    apply (Real.log_le_log_iff (by norm_num only : (0 : ℝ) < (1229 : ℝ) ^ 2) hx).mp
    linarith only [hl, hc.2, he]
  have hslow : 1229 ≤ s := by nlinarith only [hs, hs2, hxlow]
  have hq : q ≤ 9 / 2 := by
    dsimp only [q]
    apply (div_le_iff₀ (by nlinarith only [Real.pi_pos] : 0 < 6 * Real.pi)).2
    nlinarith only [hu, Real.pi_gt_three]
  change q / s ≤ _
  apply (div_le_iff₀ hs).2
  linarith only [hq, hslow]

/-- Canonical width is at least 1/1000 on the later midrange. -/
theorem midrange_post15_delta_lower {x : ℝ} (ha : 1000000 ≤ x) (hu : Real.log x ≤ (151 / 10 : ℝ)) :
    (1 / 1000 : ℝ) ≤ (5 * Real.log x / (6 * Real.pi)) / Real.sqrt x := by
  let q := 5 * Real.log x / (6 * Real.pi)
  let s := Real.sqrt x
  have hx : 0 < x := by linarith only [ha]
  have hs : 0 < s := Real.sqrt_pos.2 hx
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx.le
  have hc :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 2000 11 64 (76 / 10) (77 / 10) = true from by
        decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have he : Real.log ((2000 : ℝ) ^ 2) = 2 * Real.log 2000 := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hxupper : x ≤ (2000 : ℝ) ^ 2 := by
    apply (Real.log_le_log_iff hx (by norm_num only : (0 : ℝ) < (2000 : ℝ) ^ 2)).mp
    linarith only [hu, hc.1, he]
  have hsupper : s ≤ 2000 := by nlinarith only [hs, hs2, hxupper]
  have hq : (2 : ℝ) ≤ q := by
    dsimp only [q]
    apply (le_div_iff₀ (by nlinarith only [Real.pi_pos] : 0 < 6 * Real.pi)).2
    have hll := log_million_lower ha
    nlinarith only [hll, Real.pi_lt_d4]
  change _ ≤ q / s
  apply (le_div_iff₀ hs).2
  linarith only [hq, hsupper]

/-- The later midrange zero-tail coefficient is at most five. -/
theorem midrange_post15_tail_coefficient {L : ℝ} (hl : (1423 / 100 : ℝ) ≤ L) (hu : L ≤ 151 / 10) :
    let a := L / 2 - Real.log (5 * L / 6)
    (a ^ 2 + 2 * a + 2) / (2 * Real.pi) - 143 / 125 ≤ (5 : ℝ) := by
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
  have hau : a ≤ 511 / 100 := by
    dsimp only [a]; linarith only [hu, hloglo, hc.1]
  have hasq := pow_le_pow_left₀ ha0 hau 2
  have hb : (a ^ 2 + 2 * a + 2) / (2 * Real.pi) ≤ (5 : ℝ) + 143 / 125 := by
    apply (div_le_iff₀ (by nlinarith only [Real.pi_pos] : 0 < 2 * Real.pi)).2
    nlinarith only [hau, hasq, Real.pi_gt_d4]
  change (a ^ 2 + 2 * a + 2) / (2 * Real.pi) - 143 / 125 ≤ _
  linarith only [hb]

/-- The main-term gap at 15 exceeds 7/50. -/
theorem midrange_main_gap_at_15 : (7 / 50 : ℝ) < leeNosalPsiLog (15) - midrangePhaseMain (15) := by
  have hL :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 15 4 64 (270805 / 100000) (270806 / 100000) = true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hL
  have hk :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck (6 / 5) 0 64 (18232 / 100000) (18233 / 100000) = true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hk
  have ha0 : 0 ≤ (15 / 2 : ℝ) - Real.log (15) + Real.log (6 / 5) := by linarith only [hL.2, hk.1]
  have hau :
    (15 / 2 : ℝ) - Real.log (15) + Real.log (6 / 5) ≤
      (15 / 2 : ℝ) - 270805 / 100000 + 18233 / 100000 := by
    linarith only [hL.1, hk.2]
  have hasq := pow_le_pow_left₀ ha0 hau 2
  have hcomp : (-4643 / 10000 : ℝ) < leeNosalPsiLog (15) - integratedPsiMain (15) := by
    rw [integrated_main_gap_eq (by norm_num only : (0 : ℝ) < 15)]
    apply (lt_div_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 8) Real.pi_pos)).2
    nlinarith only [hL.2, hk.2, hau, hasq, Real.pi_gt_d4]
  rw [midrange_main_eq]
  linarith only [hcomp]

/-- Every positive `x` with logarithm at least 15 is at least one million.
A rational interval for `log 10` certifies the comparison. -/
theorem million_le_of_log_fifteen {x : ℝ} (hx : 0 < x) (hL : (15 : ℝ) ≤ Real.log x) :
    1000000 ≤ x := by
  have hc :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 10 3 64 (23025 / 10000) (23027 / 10000) = true from by
        decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have he : Real.log (1000000 : ℝ) = 6 * Real.log 10 := by
    have h : (1000000 : ℝ) = 10 ^ 6 := by norm_num only
    rw [h, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  apply (Real.log_le_log_iff (by norm_num only : (0 : ℝ) < 1000000) hx).mp
  linarith only [hc.2, he, hL]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
