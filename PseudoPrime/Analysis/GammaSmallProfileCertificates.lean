/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaMixedEulerCells

/-! # Compact mixed-Euler certificates on the bridge from 290 to 300 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Claim: the displayed profile cell satisfies all checked root and sign conditions.
Proof: kernel rational arithmetic. Role: certify the small-cell geometric invariants. -/
theorem small_cell_290_295_check : (gammaProfileEnvelopeCell 290 295).check = true := by
  decide +kernel

/-- Claim: every supported prime row satisfies the mixed analytic envelope checks.
Proof: exact kernel logarithm and Taylor arithmetic. Role: certify uniform local costs. -/
theorem small_rows_290_295_check :
    ∀ p ∈ (Finset.Icc 3 532).filter Nat.Prime,
      (gammaProfileEnvelopeRow (gammaProfileEnvelopeCell 290 295) p).envelopeCheck
          (gammaProfileEnvelopeCell 290 295) =
        true := by
  decide +kernel

/-- Claim: the total rational prime-row allowance is at most 17/4 on the displayed cell.
Proof: exact kernel arithmetic. Role: provide the excess cap for the actual dual budget. -/
theorem small_sum_290_295_check :
    (∑ p ∈ (Finset.Icc 3 532).filter Nat.Prime,
        (gammaProfileEnvelopeRow (gammaProfileEnvelopeCell 290 295) p).allowance) ≤
      (17 / 4 : ℚ) := by
  decide +kernel

/-- Claim: the displayed profile cell satisfies all checked root and sign conditions.
Proof: kernel rational arithmetic. Role: certify the small-cell geometric invariants. -/
theorem small_cell_295_300_check : (gammaProfileEnvelopeCell 295 300).check = true := by
  decide +kernel

/-- Claim: every supported prime row satisfies the mixed analytic envelope checks.
Proof: exact kernel logarithm and Taylor arithmetic. Role: certify uniform local costs. -/
theorem small_rows_295_300_check :
    ∀ p ∈ (Finset.Icc 3 541).filter Nat.Prime,
      (gammaProfileEnvelopeRow (gammaProfileEnvelopeCell 295 300) p).envelopeCheck
          (gammaProfileEnvelopeCell 295 300) =
        true := by
  decide +kernel

/-- Claim: the total rational prime-row allowance is at most 17/4 on the displayed cell.
Proof: exact kernel arithmetic. Role: provide the excess cap for the actual dual budget. -/
theorem small_sum_295_300_check :
    (∑ p ∈ (Finset.Icc 3 541).filter Nat.Prime,
        (gammaProfileEnvelopeRow (gammaProfileEnvelopeCell 295 300) p).allowance) ≤
      (17 / 4 : ℚ) := by
  decide +kernel

end PseudoPrime.Analysis
