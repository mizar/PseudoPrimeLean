/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleTailBudget
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156LowerCharge
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleTailBudget
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleTailMoment
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassTail

/-! # The fixed K156 Euler tail budget -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The compact numerator row for K156 supplies the mass coefficients. -/
private def inputCoeff (i : ℕ) : ℚ :=
  (poleData.num i : ℚ) / poleData.den

/-- The shifted K156 row at the fixed logarithmic cutoff 24. -/
private def cutoffRow : Array ℚ :=
  middleMassShiftRow (49 / 20) 24 24 inputCoeff

/-- The normalized main moment at 24 fits the rounded rational cap. -/
private theorem main_check :
    middleK156Norm * middleTailRowMoment 25 (49 / 20 - 1 / 2) (fun i ↦ cutoffRow[i]?.getD 0) ≤
      48000000000000000000 := by
  decide +kernel

/-- The normalized boundary and derivative moment at 24 fit the rounded cap. -/
private theorem error_check :
    middleK156Norm * middleTailRowError 25 (49 / 20) 24 (fun i ↦ cutoffRow[i]?.getD 0) ≤
      49000000000000000000000 := by
  decide +kernel

/-- The normalized RH Abel envelope at the K156 left cutoff is at most one. -/
public theorem middle_k156_tail_budget_24 :
    4 * (middleK156Norm : ℝ) * middleMassTailCost middleK156Kernel (49 / 20) 24 (Real.exp 24) ≤
      1 := by
  have h :=
    middle_mass_tail_budget middleK156Kernel (49 / 20) 24 middleK156Norm 24 inputCoeff
      middle_k156_kernel_degree (fun _ hi ↦ (poleData.poly_coeff hi).symm) 3744 4704
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      48000000000000000000 49000000000000000000000 1 (by decide) (by decide) main_check error_check
      (by decide +kernel)
  simpa only [Rat.cast_ofNat, Rat.cast_one] using h

/-- The shifted K156 row at the fixed logarithmic cutoff 29. -/
private def lateRow : Array ℚ :=
  middleMassShiftRow (49 / 20) 29 24 inputCoeff

/-- The normalized main moment at 29 fits the rounded rational cap. -/
private theorem late_main_check :
    middleK156Norm * middleTailRowMoment 25 (49 / 20 - 1 / 2) (fun i ↦ lateRow[i]?.getD 0) ≤
      12400000000000000000000 := by
  decide +kernel

/-- The normalized boundary and derivative moment at 29 fit the rounded cap. -/
private theorem late_error_check :
    middleK156Norm * middleTailRowError 25 (49 / 20) 29 (fun i ↦ lateRow[i]?.getD 0) ≤
      24000000000000000000000000 := by
  decide +kernel

/-- The normalized RH Abel envelope at logarithmic cutoff 29 is at most a sixtieth. -/
public theorem middle_k156_tail_budget_29 :
    4 * (middleK156Norm : ℝ) * middleMassTailCost middleK156Kernel (49 / 20) 24 (Real.exp 29) ≤
      1 / 60 := by
  have h :=
    middle_mass_tail_budget middleK156Kernel (49 / 20) 29 middleK156Norm 24 inputCoeff
      middle_k156_kernel_degree (fun _ hi ↦ (poleData.poly_coeff hi).symm) 4524 5684
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      12400000000000000000000 24000000000000000000000000 (1 / 60) (by decide) (by decide)
      late_main_check late_error_check (by decide +kernel)
  simpa only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_one] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
