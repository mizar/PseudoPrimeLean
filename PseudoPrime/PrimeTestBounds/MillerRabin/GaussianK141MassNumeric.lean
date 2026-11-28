/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassCoeffs
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleXiNumeric
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassTail
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK141LowerCharge
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK141LowerCharge
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassCoeffs
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleXiNumeric
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassTail

/-! # K141 absolute mass coefficient certificate -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Read the original compact numerator from its common-denominator row. -/
private def inputCoeff (i : ℕ) : ℚ :=
  (poleData.num i : ℚ) / poleData.den

/-- The computed constant term supplies the exact conductor normalization. -/
private theorem central_check :
    middleK141Norm * (middleMassCoeffRow (2) 14 inputCoeff)[0]?.getD 0 = 3 / 8 := by decide +kernel

/-- The normalized central Mellin profile of K141 is exactly three sixteenths. -/
public theorem middle_k141_mass_center :
    (middleK141Norm : ℝ) * middleMassProfile middleK141Kernel (2) 14 1 = 3 / 16 := by
  have hc :=
    middle_mass_coeff_row_eq middleK141Kernel (2) 14 inputCoeff middle_k141_kernel_degree
      (fun _ hi ↦ (poleData.poly_coeff hi).symm) (i := 0) (by decide)
  have h := central_check
  rw [hc] at h
  rw [middle_mass_profile_one _ _ _ (by norm_num only)]
  have hr := congrArg (fun q : ℚ ↦ (q : ℝ)) h
  simp only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] at hr
  rw [← mul_div_assoc, hr]
  norm_num only

/-- The rounded principal mass certificate plus the height-100 tail uses 30 ticks. -/
private theorem xi_check : middleXiTicks 2 middleK141Norm 14 inputCoeff ≤ 30 := by decide +kernel

/-- The normalized K141 principal mass is at most 30 millionths under RH. -/
public theorem middle_k141_xi_mass_le (hRH : RiemannHypothesis) :
    (middleK141Norm : ℝ) * (middleXiMass middleK141Kernel 2 14).re ≤ 30 / 10 ^ 6 := by
  have h :=
    middle_xi_le_ticks middleK141Kernel 2 middleK141Norm inputCoeff
      (by norm_num only [Rat.cast_ofNat]) (by decide +kernel) (by decide) middle_k141_kernel_degree
      (fun _ hi ↦ (poleData.poly_coeff hi).symm) hRH
  exact h.trans (div_le_div_of_nonneg_right (by exact_mod_cast xi_check) (by norm_num only))

/-- Both K141 tail sign checks use the same shifted mass coefficient row. -/
private theorem tail_sign_check : middleMassTailSigns (2) 20 14 inputCoeff := by
  unfold middleMassTailSigns
  decide +kernel

/-- The K141 Euler tail is bounded by its RH Abel envelope on the middle range. -/
public theorem middle_k141_mass_tail_le (hRH : RiemannHypothesis) {X : ℝ} (hX : 101 ≤ X)
    (hx : 20 ≤ Real.log X) (α : ℕ → ℝ) (hα : ∀ n, α n ∈ Set.Icc 0 4) :
    2 *
        (∑' n : { n : ℕ // ⌊X⌋₊ < n },
          α n.val *
            (ArithmeticFunction.vonMangoldt n.val / Real.sqrt n.val *
              middleMassProfile middleK141Kernel (2) 14 n.val)) ≤
      4 * middleMassTailCost middleK141Kernel (2) 14 X := by
  exact
    middle_mass_tail_rh middleK141Kernel (2) 20 14 inputCoeff
      (by norm_num only [Rat.cast_div, Rat.cast_ofNat]) middle_k141_kernel_degree
      (fun _ hi ↦ (poleData.poly_coeff hi).symm) tail_sign_check hRH hX
      ((by norm_num only : (1 : ℝ) ≤ 20).trans hx) (by simpa only [Rat.cast_ofNat] using hx) α hα

end PseudoPrime.PrimeTestBounds.MillerRabin
