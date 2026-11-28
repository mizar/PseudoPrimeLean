/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassGammaCancel
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassGammaCancel
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianBalancedPoleKernel
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosinePoles644
import PseudoPrime.LLS.PaperStatements.MellinKernelVerticalIntegrability
import Mathlib.Tactic.Linarith

/-! # Simple-pole jumps for the high Gaussian mass -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A balanced reciprocal power is analytic between the two contour lines. -/
private theorem balanced_pole_analytic {a : ℝ} (ha : 2 ≤ a) (n : ℕ) (z : ℂ) (hl : -9 / 16 ≤ z.re)
    (hr : z.re ≤ 9 / 16) : AnalyticAt ℂ (balancedPoleKernel a ha n).function z := by
  let U := Complex.re ⁻¹' Set.Ioo (-(3 / 4 : ℝ)) (3 / 4)
  have hU : IsOpen U := isOpen_Ioo.preimage Complex.continuous_re
  have hd : DifferentiableOn ℂ (balancedPoleKernel a ha n).function U := by
    intro w hw
    exact
      (balanced_diff ha n
          (abs_le.mpr ⟨by linarith only [hw.1], by linarith only [hw.2]⟩)).differentiableWithinAt
  exact (hd.analyticOnNhd hU) z ⟨by linarith only [hl], by linarith only [hr]⟩

/-- The normalized simple-pole integral of the combined high Gaussian mass. -/
public noncomputable def highMassPoleIntegral (K : HighGaussianKernel) (b p : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ,
      (1 / ((b : ℂ) + Complex.I * (t : ℂ) - (p : ℂ))) *
        K.massExtension ((b : ℂ) + Complex.I * (t : ℂ))

/-- On either comparison line, the integral of the mass is the weighted sum
of the balanced simple-pole integrals. -/
private theorem high_mass_pole_fold (K : HighGaussianKernel) {b p : ℝ} (hb₁ : -(5 / 8 : ℝ) < b)
    (hb₂ : b ≤ 5 / 8) (hb : b ≠ -1 / 2) (hp : b ≠ p) :
    highMassPoleIntegral K b p =
      ∑ j ∈ Finset.range (K.degree + 1),
        ((K.normalization : ℂ) * ((normSqPolynomial K.pole K.polynomial).coeff j : ℂ)) *
          quarterCosinePole
            (balancedPoleKernel K.pole (high_gaussian_pole_ge_two K) (K.degree + 1 - j)) b p 1 := by
  let r := fun t : ℝ ↦ (b : ℂ) + Complex.I * (t : ℂ)
  let g := fun t ↦ 1 / (r t - (p : ℂ))
  let B := fun j ↦ balancedPoleKernel K.pole (high_gaussian_pole_ge_two K) (K.degree + 1 - j)
  let c := fun j ↦ (K.normalization : ℂ) * ((normSqPolynomial K.pole K.polynomial).coeff j : ℂ)
  let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hre (t : ℝ) : (r t).re = b := by
    simp only [r, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have ha := high_gaussian_pole_ge_two K
  have hl (t : ℝ) : -(K.pole : ℝ) < (r t).re := by
    rw [hre]; linarith only [ha, hb₁]
  have hr (t : ℝ) : (r t).re < (K.pole : ℝ) := by
    rw [hre]; linarith only [ha, hb₂]
  have hi (j : ℕ) : MeasureTheory.Integrable (fun t ↦ g t * (B j).function (r t)) := by
    have hd : (B j).delta = 1 / 8 := balanced_pole_delta _ _ _
    simpa only [g, r, Complex.ofReal_one, Complex.one_cpow, mul_one] using
      (B j).integrable_pole_power_line (x := 1) (c := b) (p := p)
        (by
          rw [hd]; linarith only [hb₁])
        (by
          rw [hd]; linarith only [hb₂])
        hb hp zero_lt_one
  change
    d * (∫ t : ℝ, g t * K.massExtension (r t)) =
      ∑ j ∈ Finset.range (K.degree + 1), c j * quarterCosinePole (B j) b p 1
  rw [← fold_mass_integrals K r hl hr g hi, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [quarterCosinePole, Complex.ofReal_one, Complex.one_cpow, mul_one]
  exact mul_left_comm _ _ _

/-- Moving an interior simple pole across the strip contributes the mass
function evaluated at the pole, by linearity of the balanced decomposition. -/
public theorem high_gaussian_mass_pole_shift (K : HighGaussianKernel) {p : ℝ} (hl : -9 / 16 < p)
    (hr : p < 9 / 16) :
    highMassPoleIntegral K (9 / 16) p - highMassPoleIntegral K (-9 / 16) p =
      K.massExtension (p : ℂ) := by
  rw [high_mass_pole_fold K (by norm_num only) (by norm_num only) (by norm_num only) hr.ne',
    high_mass_pole_fold K (by norm_num only) (by norm_num only) (by norm_num only) hl.ne]
  rw [← Finset.sum_sub_distrib]
  have ha := high_gaussian_pole_ge_two K
  rw [high_gaussian_balanced_sum K
      (by
        rw [Complex.ofReal_re]; linarith only [ha, hl])
      (by
        rw [Complex.ofReal_re]; linarith only [ha, hr])]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_sub,
    quarter_cosine_pole_diff _ (balanced_pole_delta _ _ _) (balanced_pole_analytic ha _) le_rfl hl
      hr]
  simp only [Complex.ofReal_one, Complex.one_cpow, mul_one]

/-- The two poles at one half and minus one half together contribute twice
the certified rational pole term of the high Gaussian mass. -/
public theorem high_gaussian_mass_two_poles (K : HighGaussianKernel) :
    (highMassPoleIntegral K (9 / 16) (1 / 2) - highMassPoleIntegral K (-9 / 16) (1 / 2)) +
        (highMassPoleIntegral K (9 / 16) (-1 / 2) - highMassPoleIntegral K (-9 / 16) (-1 / 2)) =
      2 * (K.massPole : ℂ) := by
  rw [high_gaussian_mass_pole_shift K (by norm_num only) (by norm_num only),
    high_gaussian_mass_pole_shift K (by norm_num only) (by norm_num only)]
  simp only [neg_div, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat, high_gaussian_mass_even, high_gaussian_mass_extension_half, two_mul]

end PseudoPrime.PrimeTestBounds.MillerRabin
