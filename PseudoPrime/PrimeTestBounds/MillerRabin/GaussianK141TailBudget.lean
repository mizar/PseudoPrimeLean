/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleTailBudget
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK141LowerCharge
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleTailBudget
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleTailMoment
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassTail

/-! # The fixed K141 Euler tail budget -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The compact numerator row for K141 supplies the mass coefficients. -/
private def inputCoeff (i : ℕ) : ℚ :=
  (poleData.num i : ℚ) / poleData.den

/-- The shifted K141 row at the fixed logarithmic cutoff 20. -/
private def cutoffRow : Array ℚ :=
  middleMassShiftRow 2 20 14 inputCoeff

/-- The normalized main moment at 20 fits the rounded rational cap. -/
private theorem main_check :
    middleK141Norm * middleTailRowMoment 15 (2 - 1 / 2) (fun i ↦ cutoffRow[i]?.getD 0) ≤
      224000000000 := by
  decide +kernel

/-- The normalized boundary and derivative moment at 20 fit the rounded cap. -/
private theorem error_check :
    middleK141Norm * middleTailRowError 15 2 20 (fun i ↦ cutoffRow[i]?.getD 0) ≤
      162000000000000 := by
  decide +kernel

/-- The normalized RH Abel envelope at the K141 left cutoff is at most a tenth. -/
public theorem middle_k141_tail_budget :
    4 * (middleK141Norm : ℝ) * middleMassTailCost middleK141Kernel 2 14 (Real.exp 20) ≤ 1 / 10 := by
  have h :=
    middle_mass_tail_budget middleK141Kernel 2 20 middleK141Norm 14 inputCoeff
      middle_k141_kernel_degree (fun _ hi ↦ (poleData.poly_coeff hi).symm) 2400 3200
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) 224000000000
      162000000000000 (1 / 10) (by decide) (by decide) main_check error_check (by decide +kernel)
  simpa only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_one] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
