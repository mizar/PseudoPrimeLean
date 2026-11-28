/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassXi
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleXiNumeric
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelData
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassPole
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassExtension
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassXi
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleXiNumeric
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassCoeffs
import Mathlib.Tactic.FinCases

/-! # A coarse Xi mass budget for K186 from a single height evaluation -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The high Xi mass is the normalized version of the shared rational zero mass. -/
private theorem high_xi_eq_middle (K : HighGaussianKernel) :
    K.xiMass.re = (K.normalization : ℝ) * (middleXiMass K.polynomial K.pole K.degree).re := by
  rw [← Complex.re_ofReal_mul, Complex.ofReal_ratCast]
  unfold HighGaussianKernel.xiMass middleXiMass
  rw [← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro ρ
  simp only [HighGaussianKernel.massExtension, middleMassExtension]
  ring

/-- All tabulated low zero brackets exceed fourteen. -/
private theorem k186_zero_bracket (i : Fin 29) : (14 : ℝ) ≤ middleZeroLower i := by
  have h : (14 : ℚ) ≤ AnalyticNumberTheory.RiemannZeta.lowZero100Lower i := by
    fin_cases i <;> decide +kernel
  simpa only [middleZeroLower, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr h

/-- The row calculation uses one head ordinate for all 29 low zeros. -/
private def k186XiCap : ℚ :=
  let K := HighGaussianKernel.k186
  let row := middleNormTable K.pole K.degree (compactCoeff K)
  K.normalization * (58 * headRat K.pole K.degree row 14 + tailRat K.degree row * (13 / 1000))

/-- The single-height cap is below one hundredth by exact rational arithmetic. -/
private theorem k186_xi_cap_check : k186XiCap ≤ 1 / 100 := by decide +kernel

/-- The K186 Xi contribution is at most one hundredth under RH. A single
head ordinate suffices for the far budget, so the 29 mass evaluations are shared. -/
public theorem k186_xi_mass_le (hRH : RiemannHypothesis) :
    HighGaussianKernel.k186.xiMass.re ≤ 1 / 100 := by
  let K := HighGaussianKernel.k186
  let row := middleNormTable K.pole K.degree (compactCoeff K)
  have hdeg := high_gaussian_polynomial_degree K
  have hrow (j : ℕ) (hj : j ∈ Finset.range (K.degree + 1)) :
    row[j]?.getD 0 = (normSqPolynomial K.pole K.polynomial).coeff j :=
    middle_norm_coeff K.polynomial K.pole K.degree (compactCoeff K) hdeg
      (fun i _ ↦ (compact_coeff_eq K i).symm) j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  have hh :
    (headRat K.pole K.degree row 14 : ℝ) = middleMassHeightCap K.polynomial K.pole K.degree 14 := by
    simp only [headRat, middleMassHeightCap, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_add,
      Rat.cast_max, Rat.cast_zero, Rat.cast_ofNat]
    exact Finset.sum_congr rfl fun j hj ↦ by rw [hrow j hj]
  have ht : (tailRat K.degree row : ℝ) = middleMassHeightTail K.polynomial K.pole K.degree 100 := by
    simp only [tailRat, middleMassHeightTail, Rat.cast_sum, Rat.cast_div, Rat.cast_pow,
      Rat.cast_max, Rat.cast_zero, Rat.cast_ofNat]
    exact Finset.sum_congr rfl fun j hj ↦ by rw [hrow j hj]
  have hhead :
    (∑ i : Fin 29, middleMassHeightCap K.polynomial K.pole K.degree (middleZeroLower i)) ≤
      29 * middleMassHeightCap K.polynomial K.pole K.degree 14 := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat] using
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 29)))
        (fun i _ ↦
          middle_mass_height_antitone K.polynomial (a := K.pole) K.degree (by norm_num only)
            (k186_zero_bracket i))
  have h :=
    middle_xi_mass_le K.polynomial K.pole
      (by norm_num only [K, HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat]) (by decide) hdeg
      hRH
  rw [high_xi_eq_middle]
  have hc := (Rat.cast_le (K := ℝ)).mpr k186_xi_cap_check
  simp only [k186XiCap, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_add,
    Rat.cast_one] at hc
  change
    (K.normalization : ℝ) *
        (58 * (headRat K.pole K.degree row 14 : ℝ) + (tailRat K.degree row : ℝ) * (13 / 1000)) ≤
      1 / 100 at hc
  rw [hh, ht] at hc
  exact
    (mul_le_mul_of_nonneg_left
          (show
            _ ≤
              58 * middleMassHeightCap K.polynomial K.pole K.degree 14 +
                middleMassHeightTail K.polynomial K.pole K.degree 100 * (13 / 1000)
            by linarith only [h, hhead])
          (Rat.cast_nonneg.mpr (high_gaussian_normalization_pos K).le)).trans
      hc

end PseudoPrime.PrimeTestBounds.MillerRabin
