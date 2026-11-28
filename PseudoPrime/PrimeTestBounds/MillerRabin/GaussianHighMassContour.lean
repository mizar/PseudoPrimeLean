/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianBalancedPoleKernel
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianBalancedPoleKernel
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighZeroMass
import PseudoPrime.LLS.PaperStatements.MellinKernelSignedFormula
import Mathlib.Tactic.LinearCombination

/-! # Signed contour formula for the high Gaussian absolute mass -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The mass of the high Gaussian zero weights satisfies the signed contour formula
obtained by summing the admissible balanced pole components at unit scale. -/
public theorem high_gaussian_mass_zero_contours (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) :
    let B := fun j ↦ balancedPoleKernel K.pole (high_gaussian_pole_ge_two K) (K.degree + 1 - j)
    let c := fun j ↦ (K.normalization : ℂ) * ((normSqPolynomial K.pole K.polynomial).coeff j : ℂ)
    let s := Finset.range (K.degree + 1)
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    (∑' ρ : ℂ, ∑ j ∈ s, c j * (B j).oscillatingZeroTerm χ 1 ρ) =
      d *
            (∫ t : ℝ,
              ∑ j ∈ s,
                c j * (-logDeriv χ.completedLFunction (l t + 1 / 2) * (B j).function (l t))) +
          d *
            (∫ t : ℝ,
              ∑ j ∈ s, c j * (logDeriv χ.gammaFactor (r t + 1 / 2) * (B j).function (r t))) -
        (∑' n : ℕ, ∑ j ∈ s, c j * (B j).summand χ 1 n) := by
  intro B c s l r d
  have h :=
    LLS.PaperStatements.MellinKernel.tsum_signed_kernel_contours s B c hq hg hp hne
      (inv_ne_one.mpr hne) (a := (-9 / 16 : ℝ)) (b := 9 / 16) (x := 1) (by norm_num only)
      (fun j _ ↦ by
        rw [show (B j).delta = 1 / 8 from balanced_pole_delta _ _ _]; norm_num only)
      (fun j _ ↦ by
        rw [show (B j).delta = 1 / 8 from balanced_pole_delta _ _ _]; norm_num only)
      (by norm_num only) (by norm_num only) le_rfl (by norm_num only) (by norm_num only)
  have hz (j : ℕ) (F : ℂ → ℂ) : (B j).weightedResidue F 1 (-1 / 2) = 0 := by
    simp only [LLS.PaperStatements.MellinKernel.weightedResidue, ite_true]
    change -logDeriv F (-1 / 2) * (((-1 / 2 : ℂ) + 1 / 2) * _ * _) = 0
    rw [neg_div, neg_add_cancel, zero_mul, zero_mul, mul_zero]
  dsimp only at h
  simp only [hz, Complex.ofReal_one, Complex.one_cpow, mul_one, mul_zero, Finset.sum_const_zero,
    zero_sub] at h
  linear_combination h

/-- At unit scale the signed balanced components give the exact absolute mass
at each zero, with the completed-L multiplicity retained. -/
public theorem high_gaussian_mass_zero_weight (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (ρ : ℂ) :
    let B := fun j ↦ balancedPoleKernel K.pole (high_gaussian_pole_ge_two K) (K.degree + 1 - j)
    let c := fun j ↦ (K.normalization : ℂ) * ((normSqPolynomial K.pole K.polynomial).coeff j : ℂ)
    (∑ j ∈ Finset.range (K.degree + 1), c j * (B j).oscillatingZeroTerm χ 1 ρ) =
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) *
        K.massExtension (Complex.I * (ρ.im : ℂ)) := by
  intro B c
  have ha := (by norm_num only : (0 : ℝ) < 2).trans_le (high_gaussian_pole_ge_two K)
  have hre : (Complex.I * (ρ.im : ℂ)).re = 0 := by
    simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
  rw [high_gaussian_balanced_sum K (z := Complex.I * (ρ.im : ℂ))
      (by
        rw [hre]; exact neg_lt_zero.mpr ha)
      (by
        rw [hre]; exact ha),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [LLS.PaperStatements.MellinKernel.oscillatingZeroTerm,
    LLS.PaperStatements.MellinKernel.kernelZeroTerm, Complex.ofReal_one, Complex.one_cpow, mul_one]
  rw [mul_left_comm]

/-- The real absolute zero mass of the shifted-pole combination equals the
unit-scale balanced contour series, for every positive cutoff. -/
public theorem high_gaussian_absolute_zero_mass (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) {x : ℝ} (hx : 0 < x) :
    let B := fun j ↦ balancedPoleKernel K.pole (high_gaussian_pole_ge_two K) (K.degree + 1 - j)
    let c := fun j ↦ (K.normalization : ℂ) * ((normSqPolynomial K.pole K.polynomial).coeff j : ℂ)
    ((∑' ρ : ℂ, ‖K.zeroTerm χ x ρ‖ : ℝ) : ℂ) =
      ∑' ρ : ℂ, ∑ j ∈ Finset.range (K.degree + 1), c j * (B j).oscillatingZeroTerm χ 1 ρ := by
  intro B c
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro ρ
  rw [high_gaussian_zero_term_norm K hne hx, high_gaussian_mass_zero_weight K χ ρ,
    Complex.ofReal_mul, Complex.ofReal_intCast, high_gaussian_mass_extension_line,
    Complex.ofReal_re]

end PseudoPrime.PrimeTestBounds.MillerRabin
