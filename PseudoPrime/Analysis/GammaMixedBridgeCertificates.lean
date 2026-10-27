/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaMixedEulerCells

/-! # Three compact mixed-Euler bridge certificates from logarithmic scale 310 to 550 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Claim: the profile cell [310,350] meets all sign and root conditions.
Proof: kernel rational arithmetic. Role: validate the common bridge-cell invariants. -/
theorem bridge_cell_310_350_check : (gammaProfileEnvelopeCell 310 350).check = true := by
  decide +kernel

/-- Claim: every prime row through 631 passes the mixed envelope check on [310,350].
Proof: exact kernel logarithm and Taylor arithmetic. Role: certify the full local excess cell. -/
theorem bridge_rows_310_350_check :
    ∀ p ∈ (Finset.Icc 3 631).filter Nat.Prime,
      (gammaProfileEnvelopeRow (gammaProfileEnvelopeCell 310 350) p).envelopeCheck
          (gammaProfileEnvelopeCell 310 350) =
        true := by
  decide +kernel

/-- Claim: the mixed row allowances on [310,350] meet the displayed rational cap.
Proof: exact kernel arithmetic. Role: close the finite bridge excess numerical obligation. -/
theorem bridge_sum_310_350_check :
    (∑ p ∈ (Finset.Icc 3 631).filter Nat.Prime,
        (gammaProfileEnvelopeRow (gammaProfileEnvelopeCell 310 350) p).allowance) ≤
      (5 : ℚ) := by
  decide +kernel

/-- Claim: the profile cell [350,450] meets all sign and root conditions.
Proof: kernel rational arithmetic. Role: validate the common bridge-cell invariants. -/
theorem bridge_cell_350_450_check : (gammaProfileEnvelopeCell 350 450).check = true := by
  decide +kernel

/-- Claim: every prime row through 810 passes the mixed envelope check on [350,450].
Proof: exact kernel logarithm and Taylor arithmetic. Role: certify the full local excess cell. -/
theorem bridge_rows_350_450_check :
    ∀ p ∈ (Finset.Icc 3 810).filter Nat.Prime,
      (gammaProfileEnvelopeRow (gammaProfileEnvelopeCell 350 450) p).envelopeCheck
          (gammaProfileEnvelopeCell 350 450) =
        true := by
  decide +kernel

/-- Claim: the mixed row allowances on [350,450] meet the displayed rational cap.
Proof: exact kernel arithmetic. Role: close the finite bridge excess numerical obligation. -/
theorem bridge_sum_350_450_check :
    (∑ p ∈ (Finset.Icc 3 810).filter Nat.Prime,
        (gammaProfileEnvelopeRow (gammaProfileEnvelopeCell 350 450) p).allowance) ≤
      (6 : ℚ) := by
  decide +kernel

/-- Claim: the profile cell [450,550] meets all sign and root conditions.
Proof: kernel rational arithmetic. Role: validate the common bridge-cell invariants. -/
theorem bridge_cell_450_550_check : (gammaProfileEnvelopeCell 450 550).check = true := by
  decide +kernel

/-- Claim: every prime row through 990 passes the mixed envelope check on [450,550].
Proof: exact kernel logarithm and Taylor arithmetic. Role: certify the full local excess cell. -/
theorem bridge_rows_450_550_check :
    ∀ p ∈ (Finset.Icc 3 990).filter Nat.Prime,
      (gammaProfileEnvelopeRow (gammaProfileEnvelopeCell 450 550) p).envelopeCheck
          (gammaProfileEnvelopeCell 450 550) =
        true := by
  decide +kernel

/-- Claim: the mixed row allowances on [450,550] meet the displayed rational cap.
Proof: exact kernel arithmetic. Role: close the finite bridge excess numerical obligation. -/
theorem bridge_sum_450_550_check :
    (∑ p ∈ (Finset.Icc 3 990).filter Nat.Prime,
        (gammaProfileEnvelopeRow (gammaProfileEnvelopeCell 450 550) p).allowance) ≤
      (6 : ℚ) := by
  decide +kernel

end PseudoPrime.Analysis
