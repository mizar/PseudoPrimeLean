/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassProfileContour
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassProfileContour
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianBalancedPoleKernel
import PseudoPrime.LLS.PaperStatements.MellinKernelZetaContourLimits
import Mathlib.Tactic.LinearCombination

/-! # Xi contour identity for the high Gaussian mass -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Xi's signed contour formula for one balanced reciprocal power at unit scale. -/
private theorem balanced_xi_contour {a : ℝ} (ha : 2 ≤ a) (m : ℕ) (hRH : RiemannHypothesis) :
    let B := balancedPoleKernel a ha m
    let F := fun s : ℂ ↦
      -logDeriv (AnalyticNumberTheory.RiemannXi.riemannXi) (s + 1 / 2) * B.function s
    (∑' ρ, B.zetaOscillatingZeroTerm 1 ρ) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((∫ t : ℝ, F (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) -
          ∫ t : ℝ, F (((9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
  intro B F
  have h :=
    LLS.PaperStatements.MellinKernel.xiContourIdentity B hRH (a := (-9 / 16 : ℝ)) (b := 9 / 16)
      (x := 1)
      (by
        rw [show B.delta = 1 / 8 from balanced_pole_delta _ _ _]; norm_num only)
      (by
        rw [show B.delta = 1 / 8 from balanced_pole_delta _ _ _]; norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only) le_rfl
  have hz (G : ℂ → ℂ) : B.weightedResidue G 1 (-1 / 2) = 0 := by
    simp only [LLS.PaperStatements.MellinKernel.weightedResidue, ite_true]
    change -logDeriv G (-1 / 2) * (((-1 / 2 : ℂ) + 1 / 2) * _ * _) = 0
    rw [neg_div, neg_add_cancel, zero_mul, zero_mul, mul_zero]
  dsimp only at h
  simp only [hz, zero_sub, Complex.ofReal_one, Complex.one_cpow, mul_one] at h
  rw [mul_comm (2 * (Real.pi : ℂ)) Complex.I, mul_assoc] at h
  have he := mul_left_cancel₀ Complex.I_ne_zero h
  rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat, one_div]
  simp only [mul_comm Complex.I]
  rw [eq_inv_mul_iff_mul_eq₀ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))]
  linear_combination he

/-- The Xi zero mass of the rational continuation, counted with multiplicity. -/
public noncomputable def HighGaussianKernel.xiMass (K : HighGaussianKernel) : ℂ :=
  ∑' ρ : AnalyticNumberTheory.RiemannXi.Zero,
    (AnalyticNumberTheory.RiemannXi.riemannXiZeroMultiplicity (ρ : ℂ) : ℂ) *
      K.massExtension (Complex.I * (ρ : ℂ).im)

/-- The two Xi contours give the absolute mass of the high kernel at the zeta zeros. -/
public theorem high_gaussian_xi_mass_contours (K : HighGaussianKernel) (hRH : RiemannHypothesis) :
    let F := fun z : ℂ ↦
      -logDeriv (AnalyticNumberTheory.RiemannXi.riemannXi) (z + 1 / 2) * K.massExtension z
    K.xiMass =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((∫ t : ℝ, F (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) -
          ∫ t : ℝ, F (((9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
  intro F
  let s := Finset.range (K.degree + 1)
  let a := (K.pole : ℝ)
  have ha := high_gaussian_pole_ge_two K
  let B := fun j ↦ balancedPoleKernel a ha (K.degree + 1 - j)
  let c := fun j ↦ (K.normalization : ℂ) * ((normSqPolynomial K.pole K.polynomial).coeff j : ℂ)
  let G := fun j z ↦
    -logDeriv (AnalyticNumberTheory.RiemannXi.riemannXi) (z + 1 / 2) * (B j).function z
  have H (z : ℂ) (hl : -a < z.re) (hr : z.re < a) : F z = ∑ j ∈ s, c j * G j z :=
    (mass_integrand K hl hr _).symm
  have HE (b t : ℝ) : ((b : ℂ) + Complex.I * (t : ℂ)).re = b := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, add_zero]
  have HP (b : ℝ) (hb₁ : -1 ≤ b) (hb₂ : b ≤ 1) (t : ℝ) :
    F ((b : ℂ) + Complex.I * (t : ℂ)) = ∑ j ∈ s, c j * G j ((b : ℂ) + Complex.I * (t : ℂ)) :=
    H _
      (by
        rw [HE]; linarith only [ha, hb₁])
      (by
        rw [HE]; linarith only [ha, hb₂])
  have hb (j : ℕ) : (B j).delta = 1 / 8 := balanced_pole_delta _ _ _
  have hL (j : ℕ) :
    MeasureTheory.Integrable (fun t : ℝ ↦ c j * G j (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
    have h :=
      (B j).integrable_xi_left_line (x := 1) (c := -9 / 16)
        (by
          rw [hb]; norm_num only)
        (by norm_num only) (by norm_num only) zero_lt_one
    simpa only [G, Complex.ofReal_one, Complex.one_cpow, mul_one] using h.const_mul (c j)
  have hR (j : ℕ) :
    MeasureTheory.Integrable (fun t : ℝ ↦ c j * G j (((9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
    have h :=
      (B j).integrable_xi_right_line (x := 1) (c := 9 / 16) (by norm_num only)
        (by
          rw [hb]; norm_num only)
        (by norm_num only) zero_lt_one
    simpa only [G, Complex.ofReal_one, Complex.one_cpow, mul_one] using h.const_mul (c j)
  simp_rw [HP (-9 / 16) (by norm_num only) (by norm_num only),
    HP (9 / 16) (by norm_num only) (by norm_num only)]
  rw [MeasureTheory.integral_finsetSum s (fun j _ ↦ hL j),
    MeasureTheory.integral_finsetSum s (fun j _ ↦ hR j)]
  simp only [MeasureTheory.integral_const_mul, ← Finset.sum_sub_distrib, Finset.mul_sum, ← mul_sub,
    mul_left_comm (((1 / (2 * Real.pi) : ℝ) : ℂ))]
  have hh (j : ℕ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((∫ t : ℝ, G j (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) -
          ∫ t : ℝ, G j (((9 / 16 : ℝ) : ℂ) + Complex.I * t)) =
      ∑' ρ, (B j).zetaOscillatingZeroTerm 1 ρ :=
    (balanced_xi_contour ha (K.degree + 1 - j) hRH).symm
  have hc (j : ℕ) :
    c j * (∑' ρ, (B j).zetaOscillatingZeroTerm 1 ρ) =
      ∑' ρ, c j * (B j).zetaOscillatingZeroTerm 1 ρ :=
    (((B j).summable_zetaOscillatingZeroTerm hRH zero_lt_one).tsum_mul_left (c j)).symm
  simp only [hh, hc]
  rw [←
    Summable.tsum_finsetSum
      (fun j _ ↦ ((B j).summable_zetaOscillatingZeroTerm hRH zero_lt_one).mul_left (c j))]
  unfold HighGaussianKernel.xiMass
  apply tsum_congr
  intro ρ
  have hre : (Complex.I * ((ρ : ℂ).im : ℂ)).re = 0 := by
    simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
  rw [high_gaussian_balanced_sum K (z := Complex.I * (ρ : ℂ).im)
      (by
        rw [hre]; linarith only [ha])
      (by
        rw [hre]; linarith only [ha]),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [LLS.PaperStatements.MellinKernel.zetaOscillatingZeroTerm,
    LLS.PaperStatements.MellinKernel.zetaKernelZeroTerm, Complex.ofReal_one, Complex.one_cpow,
    mul_one]
  rw [mul_left_comm]

/-- Even primitive characters and the level-one character have the same
archimedean integral for the high Gaussian mass function. -/
public theorem high_gaussian_even_mass_gamma (K : HighGaussianKernel) {q : ℕ}
    {χ : DirichletCharacter ℂ q} (he : χ.Even) :
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    (∫ t : ℝ, logDeriv χ.gammaFactor (r t + 1 / 2) * K.massExtension (r t)) =
      ∫ t : ℝ,
        logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor (r t + 1 / 2) *
          K.massExtension (r t) := by
  intro r
  have hg : χ.gammaFactor = (1 : DirichletCharacter ℂ 1).gammaFactor := by
    funext z
    rw [he.gammaFactor_def,
      AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even.gammaFactor_def]
  rw [hg]

end PseudoPrime.PrimeTestBounds.MillerRabin
