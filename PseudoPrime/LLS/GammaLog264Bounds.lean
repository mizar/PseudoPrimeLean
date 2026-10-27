/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaLog264Certificates

/-! # Certified nearly-unit separation between logarithmic scales 264 and 265 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: RH, a checked cell index and L in that cell.
Claim: the nearly-unit separation is at least 7/60.
Proof: apply the improved prefix transfer and normalize the common scale.
Role: share the quantitative certificate application across three cells. -/
theorem gamma_log264_separation_on_cell (hRH : RiemannHypothesis) (i : Fin 3) {L : ℝ}
    (hlo : ((gammaLog264Certificate i).left : ℝ) ≤ L)
    (hhi : L ≤ ((gammaLog264Certificate i).right : ℝ)) :
    7 / 60 ≤
      gammaFactorFreeSeparation L ((9999 / 10000 : ℝ) * L ^ 2) ((101 / 250 : ℝ) * L ^ 2) := by
  have checks := gamma_log264_certificates_check i
  have h :=
    (gammaLog264Certificate i).separation_asymmetric hRH checks.1 checks.2.1 checks.2.2 hlo hhi
  have hscale : (gammaLog264Certificate i).scale = (101 / 250 : ℚ) := by fin_cases i <;> rfl
  norm_num only [hscale, Rat.cast_div, Rat.cast_ofNat] at h
  have heq : (99 / 40 : ℝ) * ((101 / 250 : ℝ) * L ^ 2) = (9999 / 10000 : ℝ) * L ^ 2 := by ring
  rw [heq] at h
  exact h.2.2

/-- Input: RH and 264 <= L <= 265. Claim: the actual margin is at least 7/60.
Proof: cover the interval by the three checked adjacent cells.
Role: bridge the new entrance to the established half-line from 265. -/
theorem gamma_log264_separation_264_265 (hRH : RiemannHypothesis) {L : ℝ} (hlo : 264 ≤ L)
    (hhi : L ≤ 265) :
    7 / 60 ≤
      gammaFactorFreeSeparation L ((9999 / 10000 : ℝ) * L ^ 2) ((101 / 250 : ℝ) * L ^ 2) := by
  have h0 := gamma_log264_separation_on_cell hRH 0 (L := L)
  have h1 := gamma_log264_separation_on_cell hRH 1 (L := L)
  have h2 := gamma_log264_separation_on_cell hRH 2 (L := L)
  change (264 : ℝ) ≤ L → L ≤ ((1057 / 4 : ℚ) : ℝ) → _ at h0
  change ((1057 / 4 : ℚ) : ℝ) ≤ L → L ≤ ((529 / 2 : ℚ) : ℝ) → _ at h1
  change ((529 / 2 : ℚ) : ℝ) ≤ L → L ≤ (265 : ℝ) → _ at h2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h0 h1 h2
  by_cases hfirst : L ≤ 1057 / 4
  · exact h0 hlo hfirst
  · by_cases hsecond : L ≤ 529 / 2
    · exact h1 (by linarith only [hfirst]) hsecond
    · exact h2 (by linarith only [hsecond]) hhi

end PseudoPrime.LLS
