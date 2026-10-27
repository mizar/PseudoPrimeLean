/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaSignedPrincipalCellCertificate
public import PseudoPrime.LLS.GammaNearUnitCertificateData

/-! # Three compact analytic cells for the signed-principal entrance at log 260 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: one of three indices. Definition: rational data for [260,261],
[261,262] and [262,264], reusing the scale 101/250 and the adaptive local bounds.
Output: a checked-cell candidate. Role: bridge the improved analytic entrance
without storing individual input witnesses or prime-power evaluations. -/
def gammaSignedPrincipalEntranceCertificate (i : Fin 3) : GammaScaledCellCertificate :=
  match i.val with
  | 0 =>
    {
      gammaNearUnitCertificateData 260 261 (3763 / 1000) (573 / 100) (28993 / 10000) (193 / 1250)
        (10223 / 1000) (11149 / 1000) 480 15 with
      leftError := 11 / 80 }
  | 1 =>
    {
      gammaNearUnitCertificateData 261 262 (3773 / 1000) (574 / 100) (29 / 10) (193 / 1250)
        (10231 / 1000) (11157 / 1000) 480 15 with
      leftError := 11 / 80 }
  | _ =>
    {
      gammaNearUnitCertificateData 262 264 (383 / 100) (5797 / 1000) (73 / 25) (39 / 250)
        (1281 / 125) (5587 / 500) 480 15 with
      leftError := 137 / 1000 }

/-- Claim: cell 0 satisfies the scalar, local-row and aggregate checks.
Kernel arithmetic validates only the compact rational cell data and existing
local formulas. Role: certify continuous scale coverage in this cell. -/
theorem gamma_signed_principal_entrance_check0 :
    (gammaSignedPrincipalEntranceCertificate 0).signedPrincipalPrefixCheck (28493 / 5000) = true ∧
      (∀ p ∈ (Finset.Icc 3 (gammaSignedPrincipalEntranceCertificate 0).support).filter Nat.Prime,
        (Analysis.gammaAdaptiveProfileRow (gammaSignedPrincipalEntranceCertificate 0).cell
                p).envelopeCheck
            (gammaSignedPrincipalEntranceCertificate 0).cell =
          true) ∧
      (∑ p ∈ (Finset.Icc 3 (gammaSignedPrincipalEntranceCertificate 0).support).filter Nat.Prime,
          (Analysis.gammaAdaptiveProfileRow (gammaSignedPrincipalEntranceCertificate 0).cell
              p).allowance) ≤
        (gammaSignedPrincipalEntranceCertificate 0).excess := by
  decide +kernel

/-- Claim: cell 1 satisfies the scalar, local-row and aggregate checks.
Kernel arithmetic validates only the compact rational cell data and existing
local formulas. Role: certify continuous scale coverage in this cell. -/
theorem gamma_signed_principal_entrance_check1 :
    (gammaSignedPrincipalEntranceCertificate 1).signedPrincipalPrefixCheck (28493 / 5000) = true ∧
      (∀ p ∈ (Finset.Icc 3 (gammaSignedPrincipalEntranceCertificate 1).support).filter Nat.Prime,
        (Analysis.gammaAdaptiveProfileRow (gammaSignedPrincipalEntranceCertificate 1).cell
                p).envelopeCheck
            (gammaSignedPrincipalEntranceCertificate 1).cell =
          true) ∧
      (∑ p ∈ (Finset.Icc 3 (gammaSignedPrincipalEntranceCertificate 1).support).filter Nat.Prime,
          (Analysis.gammaAdaptiveProfileRow (gammaSignedPrincipalEntranceCertificate 1).cell
              p).allowance) ≤
        (gammaSignedPrincipalEntranceCertificate 1).excess := by
  decide +kernel

/-- Claim: cell 2 satisfies the scalar, local-row and aggregate checks.
Kernel arithmetic validates only the compact rational cell data and existing
local formulas. Role: certify continuous scale coverage in this cell. -/
theorem gamma_signed_principal_entrance_check2 :
    (gammaSignedPrincipalEntranceCertificate 2).signedPrincipalPrefixCheck (28493 / 5000) = true ∧
      (∀ p ∈ (Finset.Icc 3 (gammaSignedPrincipalEntranceCertificate 2).support).filter Nat.Prime,
        (Analysis.gammaAdaptiveProfileRow (gammaSignedPrincipalEntranceCertificate 2).cell
                p).envelopeCheck
            (gammaSignedPrincipalEntranceCertificate 2).cell =
          true) ∧
      (∑ p ∈ (Finset.Icc 3 (gammaSignedPrincipalEntranceCertificate 2).support).filter Nat.Prime,
          (Analysis.gammaAdaptiveProfileRow (gammaSignedPrincipalEntranceCertificate 2).cell
              p).allowance) ≤
        (gammaSignedPrincipalEntranceCertificate 2).excess := by
  decide +kernel

/-- For each of the three cells, combine its separately checked obligations.
Use finite case analysis. Role: supply the generic analytic cell transfer. -/
theorem gamma_signed_principal_entrance_checks (i : Fin 3) :
    (gammaSignedPrincipalEntranceCertificate i).signedPrincipalPrefixCheck (28493 / 5000) = true ∧
      (∀ p ∈ (Finset.Icc 3 (gammaSignedPrincipalEntranceCertificate i).support).filter Nat.Prime,
        (Analysis.gammaAdaptiveProfileRow (gammaSignedPrincipalEntranceCertificate i).cell
                p).envelopeCheck
            (gammaSignedPrincipalEntranceCertificate i).cell =
          true) ∧
      (∑ p ∈ (Finset.Icc 3 (gammaSignedPrincipalEntranceCertificate i).support).filter Nat.Prime,
          (Analysis.gammaAdaptiveProfileRow (gammaSignedPrincipalEntranceCertificate i).cell
              p).allowance) ≤
        (gammaSignedPrincipalEntranceCertificate i).excess := by
  fin_cases i
  · exact gamma_signed_principal_entrance_check0
  · exact gamma_signed_principal_entrance_check1
  · exact gamma_signed_principal_entrance_check2

/-- Under RH and membership in a checked cell, the signed-principal margin
is at least 7/60. Apply the generic prefix transfer and normalize the scale.
Role: connect compact data to the actual scalar witness criterion. -/
theorem gamma_signed_principal_separation_on_cell (hRH : RiemannHypothesis) (i : Fin 3) {L : ℝ}
    (hlo : ((gammaSignedPrincipalEntranceCertificate i).left : ℝ) ≤ L)
    (hhi : L ≤ ((gammaSignedPrincipalEntranceCertificate i).right : ℝ)) :
    7 / 60 ≤
      gammaSignedPrincipalFactorFreeSeparation L ((9999 / 10000 : ℝ) * L ^ 2)
        ((101 / 250 : ℝ) * L ^ 2) := by
  have checks := gamma_signed_principal_entrance_checks i
  have h :=
    (gammaSignedPrincipalEntranceCertificate i).separation_signed_principal_asymmetric hRH checks.1
      checks.2.1 checks.2.2 hlo hhi
  have hscale : (gammaSignedPrincipalEntranceCertificate i).scale = (101 / 250 : ℚ) := by
    fin_cases i <;> rfl
  norm_num only [hscale, Rat.cast_div, Rat.cast_ofNat] at h
  have heq : (99 / 40 : ℝ) * ((101 / 250 : ℝ) * L ^ 2) = (9999 / 10000 : ℝ) * L ^ 2 := by ring
  rw [heq] at h
  exact h.2.2

/-- Under RH and 260 <= L <= 264, the signed-principal margin is at least 7/60.
Cover the interval by the three adjacent cells. Role: connect the improved
entrance to the established half-line beyond 264. -/
theorem gamma_signed_principal_separation_260_264 (hRH : RiemannHypothesis) {L : ℝ} (hlo : 260 ≤ L)
    (hhi : L ≤ 264) :
    7 / 60 ≤
      gammaSignedPrincipalFactorFreeSeparation L ((9999 / 10000 : ℝ) * L ^ 2)
        ((101 / 250 : ℝ) * L ^ 2) := by
  have h0 := gamma_signed_principal_separation_on_cell hRH 0 (L := L)
  have h1 := gamma_signed_principal_separation_on_cell hRH 1 (L := L)
  have h2 := gamma_signed_principal_separation_on_cell hRH 2 (L := L)
  change (260 : ℝ) ≤ L → L ≤ 261 → _ at h0
  change (261 : ℝ) ≤ L → L ≤ 262 → _ at h1
  change (262 : ℝ) ≤ L → L ≤ 264 → _ at h2
  by_cases hfirst : L ≤ 261
  · exact h0 hlo hfirst
  · by_cases hsecond : L ≤ 262
    · exact h1 (by linarith only [hfirst]) hsecond
    · exact h2 (by linarith only [hsecond]) hhi

end PseudoPrime.LLS
