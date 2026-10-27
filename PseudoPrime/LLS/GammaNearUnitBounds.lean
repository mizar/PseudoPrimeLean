/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaNearUnitCertificates

/-! # Certified nearly-unit separation on the entire bridge [265,290] -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: RH, one checked cell index and L inside that cell.
Claim: the actual nearly-unit margin is at least 7/60. Proof: use the universal certificate
and normalize its common scale. Role: share application code across all five cells. -/
theorem gamma_near_unit_separation_on_cell (hRH : RiemannHypothesis) (i : Fin 5) {L : ℝ}
    (hlo : ((gammaNearUnitCertificate i).left : ℝ) ≤ L)
    (hhi : L ≤ ((gammaNearUnitCertificate i).right : ℝ)) :
    7 / 60 ≤
      gammaFactorFreeSeparation L ((9999 / 10000 : ℝ) * L ^ 2) ((101 / 250 : ℝ) * L ^ 2) := by
  have checks := gamma_near_unit_certificates_check i
  have h := (gammaNearUnitCertificate i).separation hRH checks.1 checks.2.1 checks.2.2 hlo hhi
  have hscale : (gammaNearUnitCertificate i).scale = (101 / 250 : ℚ) := by fin_cases i <;> rfl
  norm_num only [hscale, Rat.cast_div, Rat.cast_ofNat] at h
  have heq : (99 / 40 : ℝ) * ((101 / 250 : ℝ) * L ^ 2) = (9999 / 10000 : ℝ) * L ^ 2 := by ring
  rw [heq] at h
  exact h.2.2

/-- Input: the same cell with its rational endpoints identified with natural numbers.
Claim: the same margin bound. Proof: normalize endpoint casts.
Role: keep the interval-cover proof independent of record reduction details. -/
private theorem gamma_near_unit_separation_of_endpoints (hRH : RiemannHypothesis) (i : Fin 5)
    (a b : ℕ)
    (heq :
      (gammaNearUnitCertificate i).left = (a : ℚ) ∧ (gammaNearUnitCertificate i).right = (b : ℚ))
    {L : ℝ} (hlo : (a : ℝ) ≤ L) (hhi : L ≤ (b : ℝ)) :
    7 / 60 ≤
      gammaFactorFreeSeparation L ((9999 / 10000 : ℝ) * L ^ 2) ((101 / 250 : ℝ) * L ^ 2) := by
  have h := gamma_near_unit_separation_on_cell hRH i (L := L)
  norm_num only [heq.1, heq.2, Rat.cast_natCast] at h
  exact h hlo hhi

/-- Input: RH and 265<=L<=290. Claim: the actual factor-free margin is at least 7/60.
Proof: cover the interval by five certified adjacent cells.
Role: close the analytic bridge for the coefficient 9999/10000 witness half-line. -/
theorem gamma_near_unit_separation_265_290 (hRH : RiemannHypothesis) {L : ℝ} (hlo : 265 ≤ L)
    (hhi : L ≤ 290) :
    7 / 60 ≤
      gammaFactorFreeSeparation L ((9999 / 10000 : ℝ) * L ^ 2) ((101 / 250 : ℝ) * L ^ 2) := by
  by_cases h266 : L ≤ 266
  · exact gamma_near_unit_separation_of_endpoints hRH 0 265 266 (by decide +kernel) hlo h266
  · by_cases h268 : L ≤ 268
    · exact
        gamma_near_unit_separation_of_endpoints hRH 1 266 268 (by decide +kernel)
          (lt_of_not_ge h266).le h268
    · by_cases h270 : L ≤ 270
      · exact
          gamma_near_unit_separation_of_endpoints hRH 2 268 270 (by decide +kernel)
            (lt_of_not_ge h268).le h270
      · by_cases h280 : L ≤ 280
        · exact
            gamma_near_unit_separation_of_endpoints hRH 3 270 280 (by decide +kernel)
              (lt_of_not_ge h270).le h280
        · exact
            gamma_near_unit_separation_of_endpoints hRH 4 280 290 (by decide +kernel)
              (lt_of_not_ge h280).le hhi

end PseudoPrime.LLS
