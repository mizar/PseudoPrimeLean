/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelData
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalCentered
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelData
import all PseudoPrime.LLS.PaperStatements.ShiftedPoleArithmetic

/-! # Centering of the high Gaussian principal profiles -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The real polynomial giving the physical profile of a high Gaussian kernel. -/
@[expose]
public noncomputable def HighGaussianKernel.realProfile (K : HighGaussianKernel) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (2 * K.degree + 1),
    Polynomial.monomial (K.logPower j) ((K.expandedCoeff j : ℝ) / ((K.logPower j).factorial : ℝ))

/-- Evaluation of the real polynomial gives the physical profile used in the Euler sum. -/
public theorem high_real_profile_eval (K : HighGaussianKernel) (z : ℝ) :
    Complex.ofReal (K.realProfile.eval z) = K.profilePoly z := by
  simp only [HighGaussianKernel.realProfile, HighGaussianKernel.profilePoly,
    LLS.PaperStatements.shiftedPolePolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_natCast, Complex.ofReal_ratCast, div_mul_eq_mul_div]

/-- The two endpoint values vanish because every monomial has degree at least three. -/
public theorem high_real_profile_at_zero (K : HighGaussianKernel) :
    K.realProfile.eval 0 = 0 ∧ K.realProfile.derivative.eval 0 = 0 := by
  constructor
  · simp only [HighGaussianKernel.realProfile, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
    exact
      Finset.sum_eq_zero
        (fun j _ ↦ by
          have hj : 3 ≤ K.logPower j := Nat.le_add_left 3 _
          rw [zero_pow (Nat.ne_of_gt ((by decide : 0 < 3).trans_le hj)), mul_zero])
  · simp only [HighGaussianKernel.realProfile, Polynomial.derivative_sum,
      Polynomial.derivative_monomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
    exact
      Finset.sum_eq_zero
        (fun j _ ↦ by
          have hj : 3 ≤ K.logPower j := Nat.le_add_left 3 _
          rw [zero_pow (Nat.ne_of_gt (Nat.sub_pos_of_lt ((by decide : 1 < 3).trans_le hj))),
            mul_zero])

/-- For each high kernel, the centered principal functional annihilates constants. -/
public theorem high_principal_cancel (K : HighGaussianKernel) :
    let d := (K.pole : ℝ) - 1 / 2
    let W := fun u : ℝ ↦ u ^ d * K.realProfile.eval (5 - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    3 * (∫ u in (0 : ℝ)..1, deriv F u) - (∫ u in (1 : ℝ)..Real.exp 5, deriv F u) - 4 * F 1 = 0 := by
  exact
    reflected_principal_cancel K.realProfile (sub_pos.mpr (high_gaussian_pole_gt K))
      (by norm_num only : (0 : ℝ) < 5) (high_real_profile_at_zero K).1
      (high_real_profile_at_zero K).2

end PseudoPrime.PrimeTestBounds.MillerRabin
