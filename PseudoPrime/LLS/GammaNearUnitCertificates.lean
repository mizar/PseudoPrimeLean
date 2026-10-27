/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaNearUnitCertificateData

/-! # Kernel checks for all five nearly-unit witness bridge cells -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Claim: cell 0 passes its scalar, row and excess-sum checks.
Proof: exact kernel arithmetic. Role: bound each proof within the default resource limit. -/
private theorem gamma_near_unit_cell_0_check :
    let c := gammaNearUnitCertificate 0;
    c.scalarCheck = true ∧
      (∀ p ∈ (Finset.Icc 3 c.support).filter Nat.Prime,
        (Analysis.gammaAdaptiveProfileRow c.cell p).envelopeCheck c.cell = true) ∧
      (∑ p ∈ (Finset.Icc 3 c.support).filter Nat.Prime,
          (Analysis.gammaAdaptiveProfileRow c.cell p).allowance) ≤
        c.excess := by
  decide +kernel

/-- Claim: cell 1 passes its scalar, row and excess-sum checks.
Proof: exact kernel arithmetic. Role: bound each proof within the default resource limit. -/
private theorem gamma_near_unit_cell_1_check :
    let c := gammaNearUnitCertificate 1;
    c.scalarCheck = true ∧
      (∀ p ∈ (Finset.Icc 3 c.support).filter Nat.Prime,
        (Analysis.gammaAdaptiveProfileRow c.cell p).envelopeCheck c.cell = true) ∧
      (∑ p ∈ (Finset.Icc 3 c.support).filter Nat.Prime,
          (Analysis.gammaAdaptiveProfileRow c.cell p).allowance) ≤
        c.excess := by
  decide +kernel

/-- Claim: cell 2 passes its scalar, row and excess-sum checks.
Proof: exact kernel arithmetic. Role: bound each proof within the default resource limit. -/
private theorem gamma_near_unit_cell_2_check :
    let c := gammaNearUnitCertificate 2;
    c.scalarCheck = true ∧
      (∀ p ∈ (Finset.Icc 3 c.support).filter Nat.Prime,
        (Analysis.gammaAdaptiveProfileRow c.cell p).envelopeCheck c.cell = true) ∧
      (∑ p ∈ (Finset.Icc 3 c.support).filter Nat.Prime,
          (Analysis.gammaAdaptiveProfileRow c.cell p).allowance) ≤
        c.excess := by
  decide +kernel

/-- Claim: cell 3 passes its scalar, row and excess-sum checks.
Proof: exact kernel arithmetic. Role: bound each proof within the default resource limit. -/
private theorem gamma_near_unit_cell_3_check :
    let c := gammaNearUnitCertificate 3;
    c.scalarCheck = true ∧
      (∀ p ∈ (Finset.Icc 3 c.support).filter Nat.Prime,
        (Analysis.gammaAdaptiveProfileRow c.cell p).envelopeCheck c.cell = true) ∧
      (∑ p ∈ (Finset.Icc 3 c.support).filter Nat.Prime,
          (Analysis.gammaAdaptiveProfileRow c.cell p).allowance) ≤
        c.excess := by
  decide +kernel

/-- Claim: cell 4 passes its scalar, row and excess-sum checks.
Proof: exact kernel arithmetic. Role: bound each proof within the default resource limit. -/
private theorem gamma_near_unit_cell_4_check :
    let c := gammaNearUnitCertificate 4;
    c.scalarCheck = true ∧
      (∀ p ∈ (Finset.Icc 3 c.support).filter Nat.Prime,
        (Analysis.gammaAdaptiveProfileRow c.cell p).envelopeCheck c.cell = true) ∧
      (∑ p ∈ (Finset.Icc 3 c.support).filter Nat.Prime,
          (Analysis.gammaAdaptiveProfileRow c.cell p).allowance) ≤
        c.excess := by
  decide +kernel

/-- Claim: every listed cell is fully checked. Proof: combine the five kernel certificates.
Role: expose one certificate theorem for the entire bridge [265,290]. -/
theorem gamma_near_unit_certificates_check :
    ∀ i : Fin 5,
      let c := gammaNearUnitCertificate i;
      c.scalarCheck = true ∧
        (∀ p ∈ (Finset.Icc 3 c.support).filter Nat.Prime,
          (Analysis.gammaAdaptiveProfileRow c.cell p).envelopeCheck c.cell = true) ∧
        (∑ p ∈ (Finset.Icc 3 c.support).filter Nat.Prime,
            (Analysis.gammaAdaptiveProfileRow c.cell p).allowance) ≤
          c.excess := by
  intro i
  fin_cases i
  · exact gamma_near_unit_cell_0_check
  · exact gamma_near_unit_cell_1_check
  · exact gamma_near_unit_cell_2_check
  · exact gamma_near_unit_cell_3_check
  · exact gamma_near_unit_cell_4_check

end PseudoPrime.LLS
