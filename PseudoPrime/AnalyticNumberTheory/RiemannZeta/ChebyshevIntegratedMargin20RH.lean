/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiIntegrated194RH
import PseudoPrime.Analysis.LogTaylorBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! # An integrated ψ envelope margin above log height 20 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- At logarithmic height 20, the difference between the Lee–Nosal target
and the integrated main term exceeds 169/2000. Rational logarithm intervals
and the upper bound for π certify the endpoint. -/
theorem integrated_main_gap_at_20 :
    (169 / 2000 : ℝ) < leeNosalPsiLog 20 - integratedPsiMain 20 := by
  have hL :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 20 4 64 (299573 / 100000) (299574 / 100000) = true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hL
  have hk :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck (6 / 5) 0 64 (18232 / 100000) (18233 / 100000) = true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hk
  have ha0 : 0 ≤ (10 : ℝ) - Real.log 20 + Real.log (6 / 5) := by linarith only [hL.2, hk.1]
  have hau :
    (10 : ℝ) - Real.log 20 + Real.log (6 / 5) ≤ (10 : ℝ) - 299573 / 100000 + 18233 / 100000 := by
    linarith only [hL.1, hk.2]
  have hasq := pow_le_pow_left₀ ha0 hau 2
  rw [integrated_main_gap_eq (by norm_num only : (0 : ℝ) < 20)]
  apply (lt_div_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 8) Real.pi_pos)).2
  nlinarith only [hL.2, hk.2, hau, hasq, Real.pi_lt_d4]

/-- Above logarithmic height 20, the integrated ψ envelope is at least 2/25
below the Lee–Nosal target. The main-term gap is increasing, and the remainder
is at most 9/2000. This comparison requires no zero hypothesis. -/
theorem integrated_envelope_margin20 {L : ℝ} (hL : (20 : ℝ) ≤ L) :
    integratedPsiEnvelope L ≤ leeNosalPsiLog L - 2 / 25 := by
  have hm :=
    integratedPsiMain_gap_mono.monotoneOn (Set.mem_Ici.mpr (by norm_num only : (97 / 5 : ℝ) ≤ 20))
      (Set.mem_Ici.mpr (show (97 / 5 : ℝ) ≤ L by linarith only [hL])) hL
  have hg : (169 / 2000 : ℝ) < leeNosalPsiLog L - integratedPsiMain L :=
    integrated_main_gap_at_20.trans_le hm
  have hr := integrated_envelope_remainder_le (show (97 / 5 : ℝ) ≤ L by linarith only [hL])
  linarith only [hg, hr]

/-- Under RH and the stated reciprocal-zero constant bound, the integrated
ψ envelope gives a normalized Lee–Nosal margin of 2/25 for `log x ≥ 20`. -/
theorem psi_integrated_margin20_of_constant (hRH : RiemannHypothesis)
    (hC : zeroReciprocalConstant ≤ -(317 / 10000 : ℝ)) {x : ℝ} (hx : 0 < x)
    (hL : (20 : ℝ) ≤ Real.log x) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ leeNosalPsiLog (Real.log x) - 2 / 25 := by
  have h := psi_integrated_envelope_of_constant hRH hC hx (by linarith only [hL])
  exact h.1.trans (integrated_envelope_margin20 hL)

/-- Under RH, the stated height-100 zero count and reciprocal-sum bound give
the normalized Lee–Nosal margin 2/25 for `log x ≥ 20`. -/
theorem psi_integrated_margin20_of_head (hRH : RiemannHypothesis) (hc : zeroCount 100 = 58)
    (hs : zeroReciprocalSum 100 ≤ (11846 / 10000 : ℝ)) {x : ℝ} (hx : 0 < x)
    (hL : (20 : ℝ) ≤ Real.log x) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ leeNosalPsiLog (Real.log x) - 2 / 25 := by
  exact psi_integrated_margin20_of_constant hRH (zeroReciprocalConstant_le_sharp hRH hc hs) hx hL

/-- Under RH, 29 ordered zeros in the stated lower brackets and the height-100
count bound imply the normalized Lee–Nosal margin 2/25 for `log x ≥ 20`. -/
theorem psi_integrated_margin20_of_brackets (hRH : RiemannHypothesis) (g : Fin 29 → ℝ)
    (hmono : StrictMono g) (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hl : LowZero100LowerBounds g) {x : ℝ} (hx : 0 < x)
    (hL : (20 : ℝ) ≤ Real.log x) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ leeNosalPsiLog (Real.log x) - 2 / 25 := by
  exact
    psi_integrated_margin20_of_constant hRH
      (zeroReciprocalConstant_sharp_of_brackets hRH g hmono hpos hheight hzero hcount hl) hx hL

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
