/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiMidrangeMarginRH
import PseudoPrime.Analysis.LogTaylorBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Numerical estimates for the next midrange interval -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Between log heights 13.86 and 14.23, canonical smoothing has relative
width at most 37/10000. A certified logarithm bounds the square root below. -/
theorem midrange_next_delta_upper {x : ℝ} (hl : (1386 / 100 : ℝ) ≤ Real.log x)
    (hu : Real.log x ≤ (1423 / 100 : ℝ)) (hx : 0 < x) :
    (5 * Real.log x / (6 * Real.pi)) / Real.sqrt x ≤ (37 / 10000 : ℝ) := by
  let q := 5 * Real.log x / (6 * Real.pi)
  let s := Real.sqrt x
  have hs : 0 < s := Real.sqrt_pos.2 hx
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx.le
  have hc :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 1022 10 64 (692 / 100) (693 / 100) = true from by
        decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have he : Real.log ((1022 : ℝ) ^ 2) = 2 * Real.log 1022 := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hxlow : (1022 : ℝ) ^ 2 ≤ x := by
    apply (Real.log_le_log_iff (by norm_num only : (0 : ℝ) < (1022 : ℝ) ^ 2) hx).mp
    linarith only [hl, hc.2, he]
  have hslow : 1022 ≤ s := by nlinarith only [hs, hs2, hxlow]
  have hq : q ≤ 189 / 50 := by
    dsimp only [q]
    apply (div_le_iff₀ (by nlinarith only [Real.pi_pos] : 0 < 6 * Real.pi)).2
    nlinarith only [hu, Real.pi_gt_d4]
  change q / s ≤ _
  apply (div_le_iff₀ hs).2
  linarith only [hq, hslow]

/-- Above one million and below log height 14.23, the canonical relative width
is at least 1/500. A certified logarithm bounds the square root above. -/
theorem midrange_next_delta_lower {x : ℝ} (ha : 1000000 ≤ x) (hu : Real.log x ≤ (1423 / 100 : ℝ)) :
    (1 / 500 : ℝ) ≤ (5 * Real.log x / (6 * Real.pi)) / Real.sqrt x := by
  let q := 5 * Real.log x / (6 * Real.pi)
  let s := Real.sqrt x
  have hx : 0 < x := by linarith only [ha]
  have hs : 0 < s := Real.sqrt_pos.2 hx
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx.le
  have hc :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 1500 10 64 (73 / 10) (74 / 10) = true from by
        decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have he : Real.log ((1500 : ℝ) ^ 2) = 2 * Real.log 1500 := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hxupper : x ≤ (1500 : ℝ) ^ 2 := by
    apply (Real.log_le_log_iff hx (by norm_num only : (0 : ℝ) < (1500 : ℝ) ^ 2)).mp
    linarith only [hu, hc.1, he]
  have hsupper : s ≤ 1500 := by nlinarith only [hs, hs2, hxupper]
  have hq : (3 : ℝ) ≤ q := by
    dsimp only [q]
    apply (le_div_iff₀ (by nlinarith only [Real.pi_pos] : 0 < 6 * Real.pi)).2
    have hll := log_million_lower ha
    nlinarith only [hll, Real.pi_lt_d4]
  change _ ≤ q / s
  apply (le_div_iff₀ hs).2
  linarith only [hq, hsupper]

/-- The zero-tail coefficient between log heights 13.86 and 14.23 is at most
83/20. The bound follows from rational logarithm and π estimates. -/
theorem midrange_next_tail_coefficient {L : ℝ} (hl : (1386 / 100 : ℝ) ≤ L) (hu : L ≤ 1423 / 100) :
    let a := L / 2 - Real.log (5 * L / 6)
    (a ^ 2 + 2 * a + 2) / (2 * Real.pi) - 143 / 125 ≤ (83 / 20 : ℝ) := by
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
  have hau : a ≤ 4675 / 1000 := by
    dsimp only [a]; linarith only [hu, hloglo, hc.1]
  have hasq := pow_le_pow_left₀ ha0 hau 2
  have hb : (a ^ 2 + 2 * a + 2) / (2 * Real.pi) ≤ (83 / 20 : ℝ) + 143 / 125 := by
    apply (div_le_iff₀ (by nlinarith only [Real.pi_pos] : 0 < 2 * Real.pi)).2
    nlinarith only [hau, hasq, Real.pi_gt_d4]
  change (a ^ 2 + 2 * a + 2) / (2 * Real.pi) - 143 / 125 ≤ _
  linarith only [hb]

/-- At log height 13.86, the sharper phase main-term gap exceeds 117/2500. -/
theorem midrange_main_gap_at_1386 :
    (117 / 2500 : ℝ) < leeNosalPsiLog (1386 / 100) - midrangePhaseMain (1386 / 100) := by
  have hL :=
    Analysis.rationalLogIntervalCheck_sound
      (show
        Analysis.rationalLogIntervalCheck (1386 / 100) 3 64 (262900 / 100000) (262902 / 100000) =
          true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hL
  have hk :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck (6 / 5) 0 64 (18232 / 100000) (18233 / 100000) = true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hk
  have ha0 : 0 ≤ (1386 / 200 : ℝ) - Real.log (1386 / 100) + Real.log (6 / 5) := by
    linarith only [hL.2, hk.1]
  have hau :
    (1386 / 200 : ℝ) - Real.log (1386 / 100) + Real.log (6 / 5) ≤
      (1386 / 200 : ℝ) - 262900 / 100000 + 18233 / 100000 := by
    linarith only [hL.1, hk.2]
  have hasq := pow_le_pow_left₀ ha0 hau 2
  have hcomp : (-223 / 400 : ℝ) < leeNosalPsiLog (1386 / 100) - integratedPsiMain (1386 / 100) := by
    rw [integrated_main_gap_eq (by norm_num only : (0 : ℝ) < 1386 / 100)]
    apply (lt_div_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 8) Real.pi_pos)).2
    nlinarith only [hL.2, hk.2, hau, hasq, Real.pi_gt_d4]
  rw [midrange_main_eq]
  linarith only [hcomp]

/-- The nonnegative part of the next-block smoothing remainder is at most
99/5000 under the stated rational bounds. -/
theorem midrange_next_remainder {δ B c s x : ℝ} (hd : (1 / 500 : ℝ) ≤ δ) (hdu : δ ≤ 37 / 10000)
    (hB : B ≤ 83 / 20) (hc : c ≤ 1838 / 1000) (hs : 1000 ≤ s) (hx : 1000000 ≤ x) :
    c / s + δ * (51 / 100) / 4 + 527 / 250000 + δ * B + (1 + δ) * δ ^ 2 / 60 + 1 / (x * δ * s) ≤
      (99 / 5000 : ℝ) := by
  have hδ0 : 0 < δ := by linarith only [hd]
  have hs0 : 0 < s := by linarith only [hs]
  have hx0 : 0 < x := by linarith only [hx]
  have hcs : c / s ≤ (1838 / 1000000 : ℝ) := by
    apply (div_le_iff₀ hs0).2
    linarith only [hc, hs]
  have hterm := mul_le_mul_of_nonneg_left hB hδ0.le
  have hδB : δ * B ≤ (3071 / 200000 : ℝ) := by nlinarith only [hterm, hdu]
  have hsq : δ ^ 2 ≤ (37 / 10000 : ℝ) ^ 2 := by nlinarith only [hδ0, hdu]
  have hmul :=
    mul_le_mul (show 1 + δ ≤ (10037 / 10000 : ℝ) by linarith only [hdu]) hsq (sq_nonneg δ)
      (by norm_num only : (0 : ℝ) ≤ 10037 / 10000)
  have hsmall : (1 + δ) * δ ^ 2 / 60 ≤ (1 / 4000000 : ℝ) := by nlinarith only [hmul]
  have hxδ := mul_le_mul hx hd (by norm_num only : (0 : ℝ) ≤ 1 / 500) hx0.le
  have hxδs := mul_le_mul hxδ hs (by norm_num only : (0 : ℝ) ≤ 1000) (mul_nonneg hx0.le hδ0.le)
  have hden : (0 : ℝ) < x * δ * s := mul_pos (mul_pos hx0 hδ0) hs0
  have hrem : 1 / (x * δ * s) ≤ (1 / 2000000 : ℝ) := by
    apply (div_le_iff₀ hden).2
    nlinarith only [hxδs]
  nlinarith only [hcs, hδB, hsmall, hrem, hdu]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
