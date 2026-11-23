/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiIntegrated194RH
import PseudoPrime.Analysis.LogTaylorBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! # An integrated ψ envelope margin above log height 53/2 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- At logarithmic height 53/2, the difference between the Lee–Nosal target
and the integrated main term exceeds 2069/2000. Rational logarithm intervals
and the upper bound for π certify the endpoint. -/
theorem integrated_main_gap_at_half53 :
    (2069 / 2000 : ℝ) < leeNosalPsiLog (53 / 2) - integratedPsiMain (53 / 2) := by
  have hL :=
    Analysis.rationalLogIntervalCheck_sound
      (show
        Analysis.rationalLogIntervalCheck (53 / 2) 4 64 (327714 / 100000) (327715 / 100000) = true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hL
  have hk :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck (6 / 5) 0 64 (18232 / 100000) (18233 / 100000) = true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hk
  have ha0 : 0 ≤ (53 / 4 : ℝ) - Real.log (53 / 2) + Real.log (6 / 5) := by
    linarith only [hL.2, hk.1]
  have hau :
    (53 / 4 : ℝ) - Real.log (53 / 2) + Real.log (6 / 5) ≤
      (53 / 4 : ℝ) - 327714 / 100000 + 18233 / 100000 := by
    linarith only [hL.1, hk.2]
  have hasq := pow_le_pow_left₀ ha0 hau 2
  rw [integrated_main_gap_eq (by norm_num only : (0 : ℝ) < 53 / 2)]
  apply (lt_div_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 8) Real.pi_pos)).2
  nlinarith only [hL.2, hk.2, hau, hasq, Real.pi_lt_d4]

/-- Above logarithmic height 53/2, the integrated ψ envelope is at least 103/100
below the Lee–Nosal target. The main-term gap is increasing, and the remainder
is at most 9/2000. This comparison requires no zero hypothesis. -/
theorem integrated_envelope_margin_half53 {L : ℝ} (hL : (53 / 2 : ℝ) ≤ L) :
    integratedPsiEnvelope L ≤ leeNosalPsiLog L - 103 / 100 := by
  have hm :=
    integratedPsiMain_gap_mono.monotoneOn
      (Set.mem_Ici.mpr (by norm_num only : (97 / 5 : ℝ) ≤ 53 / 2))
      (Set.mem_Ici.mpr (show (97 / 5 : ℝ) ≤ L by linarith only [hL])) hL
  have hg : (2069 / 2000 : ℝ) < leeNosalPsiLog L - integratedPsiMain L :=
    integrated_main_gap_at_half53.trans_le hm
  have hr := integrated_envelope_remainder_le (show (97 / 5 : ℝ) ≤ L by linarith only [hL])
  linarith only [hg, hr]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
