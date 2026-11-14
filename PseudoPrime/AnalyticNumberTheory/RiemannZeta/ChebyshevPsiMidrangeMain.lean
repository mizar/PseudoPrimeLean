/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevIntegralMain194
import PseudoPrime.Analysis.LogTaylorBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Monotonicity of the initial midrange main-term gap -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- At logarithmic heights at least 13.815, the logarithm lies between 13/5
and one quarter of its argument. The lower endpoint is certified rationally. -/
theorem midrange_log_bounds {L : ℝ} (hL : (13815 / 1000 : ℝ) ≤ L) :
    (13 / 5 : ℝ) ≤ Real.log L ∧ Real.log L ≤ L / 4 := by
  have hc :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck (138 / 10) 3 64 (262 / 100) (263 / 100) = true from by
        decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have hlower :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 138 / 10)
      (show (138 / 10 : ℝ) ≤ L by linarith only [hL])
  have hL0 : 0 < L := by linarith only [hL]
  have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    have he : (8 : ℝ) = 2 ^ 3 := by norm_num only
    rw [he, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have ht := Real.log_le_sub_one_of_pos (div_pos hL0 (by norm_num only : (0 : ℝ) < 8))
  have he : Real.log (L / 8) = Real.log L - Real.log 8 := by
    rw [Real.log_div hL0.ne' (by norm_num only : (8 : ℝ) ≠ 0)]
  rw [he, hlog8] at ht
  constructor
  · linarith only [hlower, hc.1]
  · linarith only [ht, Real.log_two_lt_d9, hL]

/-- The scaled main-term gap is strictly increasing from logarithmic height
13.815, uniformly for a shift between zero and one fifth. -/
theorem midrange_main_gap_strictMono (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1 / 5) :
    StrictMonoOn
      (fun t : ℝ ↦
        t * (t - Real.log t) - (10 / 3 : ℝ) * t -
          4 * ((t / 2 - Real.log t + k) ^ 2 + 2 * (t / 2 - Real.log t + k) + 2))
      (Set.Ici (13815 / 1000 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro t ht
    change (13815 / 1000 : ℝ) ≤ t at ht
    have ht0 : 0 < t := by linarith only [ht]
    exact ((integrated_main_gap_deriv k ht0).continuousAt).continuousWithinAt
  · intro t ht
    have ht' : (13815 / 1000 : ℝ) ≤ t := interior_subset ht
    have ht0 : 0 < t := by linarith only [ht']
    have hl := midrange_log_bounds ht'
    have hfrac : -(1 / 4 : ℝ) ≤ (1 - Real.log t + k) / t := by
      apply (le_div_iff₀ ht0).2
      linarith only [hl.2, hk0]
    rw [(integrated_main_gap_deriv k ht0).deriv]
    have heq : 8 * (1 - Real.log t + k) / t = 8 * ((1 - Real.log t + k) / t) := by ring
    rw [heq]
    linarith only [hl.1, hk1, hfrac]

/-- The main term of the initial phase-based ψ envelope, omitting smoothing
remainders. The phase bound is 127/250 and the reciprocal-zero term is -143/125. -/
@[expose]
noncomputable def midrangePhaseMain (L : ℝ) : ℝ :=
  let a := L / 2 - Real.log (5 * L / 6)
  (5 * L / (6 * Real.pi)) / 2 + (a ^ 2 + 2 * a + 2) / (2 * Real.pi) - 143 / 125 + 127 / 250

/-- The phase main term differs from the integrated main term by a constant. -/
theorem midrange_main_eq (L : ℝ) : midrangePhaseMain L = integratedPsiMain L - 6043 / 10000 := by
  dsimp only [midrangePhaseMain, integratedPsiMain]
  ring

/-- The difference between the Lee–Nosal envelope and the initial phase main
term is strictly increasing from logarithmic height 13.815. -/
theorem midrange_main_gap_mono :
    StrictMonoOn (fun L ↦ leeNosalPsiLog L - midrangePhaseMain L) (Set.Ici (13815 / 1000 : ℝ)) := by
  intro x hx y hy hxy
  have hx' : (13815 / 1000 : ℝ) ≤ x := hx
  have hy' : (13815 / 1000 : ℝ) ≤ y := hy
  have hk := log_six_fifths_bounds
  have hm := midrange_main_gap_strictMono (Real.log (6 / 5)) hk.1 hk.2 hx hy hxy
  have ht : leeNosalPsiLog x - integratedPsiMain x < leeNosalPsiLog y - integratedPsiMain y := by
    rw [integrated_main_gap_eq (by linarith only [hx']),
      integrated_main_gap_eq (by linarith only [hy'])]
    apply div_lt_div_of_pos_right _ (mul_pos (by norm_num only) Real.pi_pos)
    linarith only [hm]
  change leeNosalPsiLog x - midrangePhaseMain x < leeNosalPsiLog y - midrangePhaseMain y
  rw [midrange_main_eq, midrange_main_eq]
  linarith only [ht]

/-- At logarithmic height 13.815, the main-term gap exceeds 43/1000.
Rational logarithm intervals and the lower bound for π certify the comparison. -/
theorem midrange_main_gap_at_start :
    (43 / 1000 : ℝ) < leeNosalPsiLog (13815 / 1000) - midrangePhaseMain (13815 / 1000) := by
  have hL :=
    Analysis.rationalLogIntervalCheck_sound
      (show
        Analysis.rationalLogIntervalCheck (13815 / 1000) 3 64 (262575 / 100000) (262576 / 100000) =
          true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hL
  have hk :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck (6 / 5) 0 64 (18232 / 100000) (18233 / 100000) = true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hk
  have ha0 : 0 ≤ (13815 / 2000 : ℝ) - Real.log (13815 / 1000) + Real.log (6 / 5) := by
    linarith only [hL.2, hk.1]
  have hau :
    (13815 / 2000 : ℝ) - Real.log (13815 / 1000) + Real.log (6 / 5) ≤
      (13815 / 2000 : ℝ) - 262575 / 100000 + 18233 / 100000 := by
    linarith only [hL.1, hk.2]
  have hasq := pow_le_pow_left₀ ha0 hau 2
  have hcomp :
    (-5613 / 10000 : ℝ) < leeNosalPsiLog (13815 / 1000) - integratedPsiMain (13815 / 1000) := by
    rw [integrated_main_gap_eq (by norm_num only : (0 : ℝ) < 13815 / 1000)]
    apply (lt_div_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 8) Real.pi_pos)).2
    nlinarith only [hL.2, hk.2, hau, hasq, Real.pi_gt_d4]
  rw [midrange_main_eq]
  linarith only [hcomp]

/-- The initial phase main term lies more than 43/1000 below the Lee–Nosal
logarithmic envelope throughout the half-line beginning at 13.815. -/
theorem midrange_main_gap {L : ℝ} (hL : (13815 / 1000 : ℝ) ≤ L) :
    (43 / 1000 : ℝ) < leeNosalPsiLog L - midrangePhaseMain L := by
  have hm :=
    midrange_main_gap_mono.monotoneOn (Set.mem_Ici.mpr (le_rfl : (13815 / 1000 : ℝ) ≤ 13815 / 1000))
      (Set.mem_Ici.mpr hL) hL
  exact midrange_main_gap_at_start.trans_le hm

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
