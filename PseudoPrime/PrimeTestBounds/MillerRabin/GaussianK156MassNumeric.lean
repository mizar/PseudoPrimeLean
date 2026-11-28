/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassCoeffs
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleXiNumeric
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassTail
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156LowerCharge
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156LowerCharge
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassCoeffs
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleXiNumeric
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassTail

/-! # K156 absolute mass coefficient certificate -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Read the original compact numerator from its common-denominator row. -/
private def inputCoeff (i : ℕ) : ℚ :=
  (poleData.num i : ℚ) / poleData.den

/-- The computed constant term supplies the exact conductor normalization. -/
private theorem central_check :
    middleK156Norm * (middleMassCoeffRow (49 / 20) 24 inputCoeff)[0]?.getD 0 = 3 / 8 := by
  decide +kernel

/-- The normalized central Mellin profile of K156 is exactly three sixteenths. -/
public theorem middle_k156_mass_center :
    (middleK156Norm : ℝ) * middleMassProfile middleK156Kernel (49 / 20) 24 1 = 3 / 16 := by
  have hc :=
    middle_mass_coeff_row_eq middleK156Kernel (49 / 20) 24 inputCoeff middle_k156_kernel_degree
      (fun _ hi ↦ (poleData.poly_coeff hi).symm) (i := 0) (by decide)
  have h := central_check
  rw [hc] at h
  rw [middle_mass_profile_one _ _ _ (by norm_num only)]
  have hr := congrArg (fun q : ℚ ↦ (q : ℝ)) h
  simp only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] at hr
  rw [← mul_div_assoc, hr]
  norm_num only

/-- The rounded principal mass certificate plus the height-100 tail uses 45 ticks. -/
private theorem xi_check : middleXiTicks (49 / 20) middleK156Norm 24 inputCoeff ≤ 45 := by
  decide +kernel

/-- The normalized K156 principal mass is at most 45 millionths under RH. -/
public theorem middle_k156_xi_mass_le (hRH : RiemannHypothesis) :
    (middleK156Norm : ℝ) * (middleXiMass middleK156Kernel (49 / 20) 24).re ≤ 45 / 10 ^ 6 := by
  have h :=
    middle_xi_le_ticks middleK156Kernel (49 / 20) middleK156Norm inputCoeff
      (by norm_num only [Rat.cast_div, Rat.cast_ofNat]) (by decide +kernel) (by decide)
      middle_k156_kernel_degree (fun _ hi ↦ (poleData.poly_coeff hi).symm) hRH
  exact h.trans (div_le_div_of_nonneg_right (by exact_mod_cast xi_check) (by norm_num only))

/-- Both K156 tail sign checks use the same shifted mass coefficient row. -/
private theorem tail_sign_check : middleMassTailSigns (49 / 20) 24 24 inputCoeff := by
  unfold middleMassTailSigns
  decide +kernel

/-- The K156 Euler tail is bounded by its RH Abel envelope on the middle range. -/
public theorem middle_k156_mass_tail_le (hRH : RiemannHypothesis) {X : ℝ} (hX : 101 ≤ X)
    (hx : 24 ≤ Real.log X) (α : ℕ → ℝ) (hα : ∀ n, α n ∈ Set.Icc 0 4) :
    2 *
        (∑' n : { n : ℕ // ⌊X⌋₊ < n },
          α n.val *
            (ArithmeticFunction.vonMangoldt n.val / Real.sqrt n.val *
              middleMassProfile middleK156Kernel (49 / 20) 24 n.val)) ≤
      4 * middleMassTailCost middleK156Kernel (49 / 20) 24 X := by
  exact
    middle_mass_tail_rh middleK156Kernel (49 / 20) 24 24 inputCoeff
      (by norm_num only [Rat.cast_div, Rat.cast_ofNat]) middle_k156_kernel_degree
      (fun _ hi ↦ (poleData.poly_coeff hi).symm) tail_sign_check hRH hX
      ((by norm_num only : (1 : ℝ) ≤ 24).trans hx) (by simpa only [Rat.cast_ofNat] using hx) α hα

end PseudoPrime.PrimeTestBounds.MillerRabin
