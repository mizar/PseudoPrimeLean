/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaCoefficients
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleReflection

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaCoefficients
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaPowers

/-! # A geometric upper bound for the far K186 Gamma coefficients -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- One forward pole and its integral tail give a geometric upper bound.
This avoids generating a separate high-precision inverse-power grid for each order. -/
theorem k186_gamma_coeff_geometric (j : ℕ) : highGammaCoeff .k186 j ≤ 2 * (4 / 7 : ℝ) ^ j := by
  cases j with
  | zero =>
    have h := (high_gamma_zero_bounds .k186).2
    have hc : (highGammaZeroBounds .k186).2 ≤ 2 := by
      unfold highGammaZeroBounds
      decide +kernel
    simpa only [pow_zero, mul_one, Rat.cast_ofNat] using h.trans (Rat.cast_le.mpr hc)
  | succ j =>
    have h := (high_gamma_higher_bounds .k186 j 0).2
    let F := gammaPolePowerBounds (7 / 4) j 0
    let R := gammaPolePowerBounds (13 / 4) j 0
    let p := (-1 : ℚ) ^ (j + 1)
    have hh : highGammaCoeff .k186 (j + 1) ≤ ((-min (p * F.1) (p * F.2) - R.1 : ℚ) : ℝ) := by
      convert h using 2
      norm_num only [highGammaHigherBounds, HighGaussianKernel.pole, F, R, p]
    have hf : 0 ≤ F.1 := by
      dsimp only [F, gammaPolePowerBounds]
      apply add_nonneg
      · exact Finset.sum_nonneg fun _ _ ↦ one_div_nonneg.mpr (pow_nonneg (by positivity) _)
      · positivity
    have hF : 0 ≤ F.2 := by
      dsimp only [F, gammaPolePowerBounds]
      apply add_nonneg
      · exact Finset.sum_nonneg fun _ _ ↦ one_div_nonneg.mpr (pow_nonneg (by positivity) _)
      · positivity
    have hR : 0 ≤ R.1 := by
      dsimp only [R, gammaPolePowerBounds]
      apply add_nonneg
      · exact Finset.sum_nonneg fun _ _ ↦ one_div_nonneg.mpr (pow_nonneg (by positivity) _)
      · positivity
    have hmin : -(F.2) ≤ min (p * F.1) (p * F.2) := by
      have hle : F.1 ≤ F.2 := by
        have hb := gamma_pole_power_bounds_cast (d := 7 / 4) (by norm_num only) j 0
        exact (Rat.cast_le (K := ℝ)).mp (hb.1.trans hb.2)
      have hp : -1 ≤ p := by
        have hab : |p| = 1 := by simp only [p, abs_pow, abs_neg, abs_one, one_pow]
        exact (abs_le.mp hab.le).1
      exact
        le_min
          ((neg_le_neg hle).trans
            (by simpa only [neg_one_mul] using mul_le_mul_of_nonneg_right hp hf))
          (by simpa only [neg_one_mul] using mul_le_mul_of_nonneg_right hp hF)
    refine
      hh.trans
        ((Rat.cast_le.mpr
              (show -min (p * F.1) (p * F.2) - R.1 ≤ F.2 by linarith only [hmin, hR])).trans
          ?_)
    simp only [F, gammaPolePowerBounds, Nat.zero_add, Finset.sum_range_one, Nat.cast_zero,
      Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast,
      Rat.cast_one, mul_zero, add_zero]
    have hn : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith only [Nat.cast_nonneg (α := ℝ) j]
    have htwo : 1 / (2 * ((j : ℝ) + 1)) ≤ (1 / 2 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num only) (by linarith only [hn])
    have he :
      (1 / (7 / 4 : ℝ) ^ (j + 2)) + 1 / (2 * ((j : ℝ) + 1) * (7 / 4 : ℝ) ^ (j + 1)) =
        (4 / 7 + 1 / (2 * ((j : ℝ) + 1))) * (4 / 7 : ℝ) ^ (j + 1) := by
      rw [← one_div_mul_one_div]
      simp only [← one_div_pow, show 1 / (7 / 4 : ℝ) = 4 / 7 by norm_num only,
        pow_succ (4 / 7 : ℝ) (j + 1)]
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (by linarith only [htwo]) (pow_nonneg (by norm_num only) _)

/-- The geometric derivative sum used in the common-contour majorant. -/
noncomputable def k186GammaGeometricPoly : Polynomial ℝ :=
  let P := HighGaussianKernel.k186.realProfile
  ∑ j ∈ Finset.range (P.natDegree + 1),
    Polynomial.C (2 * (4 / 7 : ℝ) ^ j) * (Polynomial.derivative^[j]) P

/-- The geometric derivative sum does not raise the physical profile degree. -/
theorem k186_gamma_geometric_degree :
    k186GammaGeometricPoly.natDegree ≤ HighGaussianKernel.k186.realProfile.natDegree := by
  unfold k186GammaGeometricPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact
    Polynomial.natDegree_mul_le.trans
      (by
        simpa only [Polynomial.natDegree_C, zero_add] using
          ((Polynomial.natDegree_iterate_derivative _ _).trans (Nat.sub_le _ _)))

/-- After translating the cutoff, the geometric derivative polynomial is
seven halves times one Laplace moment at rate seven quarters. -/
theorem k186_gamma_geometric_translate (o : ℝ) :
    k186GammaGeometricPoly.comp (Polynomial.X + Polynomial.C o) =
      Polynomial.C (7 / 2 : ℝ) *
        middleMomentPoly HighGaussianKernel.k186.realProfile (7 / 4) o := by
  apply Polynomial.funext
  intro t
  rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  simp only [k186GammaGeometricPoly, middleMomentPoly, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj :=
    congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℝ) (k := j))
      HighGaussianKernel.k186.realProfile
  have hd := congrArg (fun P : Polynomial ℝ ↦ P.eval (t + o)) hj
  change
    (j.factorial • Polynomial.hasseDeriv j HighGaussianKernel.k186.realProfile).eval (t + o) =
      _ at hd
  simp only [nsmul_eq_mul, Polynomial.eval_natCast_mul] at hd
  have hv : (4 / 7 : ℝ) ^ j = 1 / (7 / 4 : ℝ) ^ j := by
    rw [← one_div_pow, show 1 / (7 / 4 : ℝ) = 4 / 7 by norm_num only]
  rw [← hd, hv, pow_succ]
  field_simp [pow_ne_zero j (by norm_num only : (7 / 4 : ℝ) ≠ 0)]
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
