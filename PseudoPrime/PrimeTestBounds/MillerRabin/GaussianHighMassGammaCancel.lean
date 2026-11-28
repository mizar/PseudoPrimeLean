/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassXi
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassProfileContour
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftZeta
import PseudoPrime.LLS.PaperStatements.MellinKernelSignedFormula
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! # Common gamma cancellation in the high Gaussian zero mass -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Integrals of the balanced components recombine into the mass function
as long as the weight is integrable against each component on the line. -/
private theorem fold_mass_integrals (K : HighGaussianKernel) (r : ℝ → ℂ)
    (hl : ∀ t, -(K.pole : ℝ) < (r t).re) (hr : ∀ t, (r t).re < (K.pole : ℝ)) (g : ℝ → ℂ) :
    let B := fun j ↦ balancedPoleKernel K.pole (high_gaussian_pole_ge_two K) (K.degree + 1 - j)
    let c := fun j ↦ (K.normalization : ℂ) * ((normSqPolynomial K.pole K.polynomial).coeff j : ℂ)
    (∀ j, MeasureTheory.Integrable (fun t ↦ g t * (B j).function (r t))) →
      (∑ j ∈ Finset.range (K.degree + 1), c j * (∫ t : ℝ, g t * (B j).function (r t))) =
        ∫ t : ℝ, g t * K.massExtension (r t) := by
  intro B c hi
  simp_rw [← MeasureTheory.integral_const_mul]
  rw [← MeasureTheory.integral_finsetSum _ (fun j _ ↦ (hi j).const_mul (c j))]
  exact
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun t ↦ mass_integrand K (hl t) (hr t) (g t)))

/-- The right Xi contour at unit scale splits the level-one Mangoldt sum into
the two rational poles and the common even gamma integral. -/
public theorem high_gaussian_xi_right_split (K : HighGaussianKernel) :
    let χ₁ := (1 : DirichletCharacter ℂ 1)
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    (∑' n : ℕ,
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ₁ n * (K.massProfile n : ℂ)) =
      d *
          ((∫ t : ℝ,
              -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (r t + 1 / 2) *
                K.massExtension (r t)) +
            (∫ t : ℝ, (1 / (r t - ((-1 / 2 : ℝ) : ℂ))) * K.massExtension (r t)) +
            ∫ t : ℝ, (1 / (r t - ((1 / 2 : ℝ) : ℂ))) * K.massExtension (r t)) +
        d * ∫ t : ℝ, logDeriv χ₁.gammaFactor (r t + 1 / 2) * K.massExtension (r t) := by
  intro χ₁ r d
  let B := fun j ↦ balancedPoleKernel K.pole (high_gaussian_pole_ge_two K) (K.degree + 1 - j)
  let c := fun j ↦ (K.normalization : ℂ) * ((normSqPolynomial K.pole K.polynomial).coeff j : ℂ)
  let F := fun t ↦ -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (r t + 1 / 2)
  let P := fun (p : ℝ) t ↦ 1 / (r t - (p : ℂ))
  let G := fun t ↦ logDeriv χ₁.gammaFactor (r t + 1 / 2)
  have hd (j : ℕ) : (B j).delta = 1 / 8 := balanced_pole_delta _ _ _
  have hb (j : ℕ) : (9 / 16 : ℝ) ≤ 1 / 2 + (B j).delta := by
    rw [hd]; norm_num only
  have hre (t : ℝ) : (r t).re = 9 / 16 := by
    simp only [r, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have ha := high_gaussian_pole_ge_two K
  have hl (t : ℝ) : -(K.pole : ℝ) < (r t).re := by
    rw [hre]; linarith only [ha]
  have hr (t : ℝ) : (r t).re < (K.pole : ℝ) := by
    rw [hre]; linarith only [ha]
  have hF (j : ℕ) : MeasureTheory.Integrable (fun t ↦ F t * (B j).function (r t)) := by
    simpa only [F, r, Complex.ofReal_one, Complex.one_cpow, mul_one] using
      (B j).integrable_xi_right_line (x := 1) (by norm_num only) (hb j) (by norm_num only)
        zero_lt_one
  have hP (p : ℝ) (hp : (9 / 16 : ℝ) ≠ p) (j : ℕ) :
    MeasureTheory.Integrable (fun t ↦ P p t * (B j).function (r t)) := by
    simpa only [P, r, Complex.ofReal_one, Complex.one_cpow, mul_one] using
      (B j).integrable_pole_power_line (x := 1)
        (by
          rw [hd]; norm_num only)
        (hb j) (by norm_num only) hp zero_lt_one
  have hG (j : ℕ) : MeasureTheory.Integrable (fun t ↦ G t * (B j).function (r t)) := by
    simpa only [G, r, Complex.ofReal_one, Complex.one_cpow, mul_one] using
      (B j).integrable_gammaFactor_power_line χ₁ (x := 1) (by norm_num only) (hb j)
        (by norm_num only) zero_lt_one
  have hh (j : ℕ) :
    (∑' n : ℕ, (B j).summand χ₁ 1 n) =
      d *
          ((∫ t : ℝ, F t * (B j).function (r t)) + (∫ t : ℝ, P (-1 / 2) t * (B j).function (r t)) +
            ∫ t : ℝ, P (1 / 2) t * (B j).function (r t)) +
        d * ∫ t : ℝ, G t * (B j).function (r t) := by
    have h := twoShift_level_one_forward (B j) (hd j) (x := 1) zero_lt_one
    simpa only [F, P, G, r, d, χ₁, Complex.ofReal_one, Complex.one_cpow, mul_one] using h
  have hA :
    (∑' n : ℕ,
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ₁ n * (K.massProfile n : ℂ)) =
      ∑ j ∈ Finset.range (K.degree + 1), c j * ∑' n : ℕ, (B j).summand χ₁ 1 n := by
    rw [← LLS.PaperStatements.MellinKernel.tsum_kernel_finset_sum _ B c χ₁ zero_lt_one]
    exact (tsum_congr (mass_arithmetic K χ₁)).symm
  change
    _ =
      d *
          ((∫ t : ℝ, F t * K.massExtension (r t)) +
            (∫ t : ℝ, P (-1 / 2) t * K.massExtension (r t)) +
            ∫ t : ℝ, P (1 / 2) t * K.massExtension (r t)) +
        d * ∫ t : ℝ, G t * K.massExtension (r t)
  rw [hA]
  simp only [hh, mul_add, mul_left_comm (c _) d, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [fold_mass_integrals K r hl hr F hF,
    fold_mass_integrals K r hl hr (P (-1 / 2)) (hP _ (by norm_num only)),
    fold_mass_integrals K r hl hr (P (1 / 2)) (hP _ (by norm_num only)),
    fold_mass_integrals K r hl hr G hG]

/-- For an even primitive nonprincipal character, the right gamma integrals
cancel in the difference between the Dirichlet and Xi zero masses. -/
public theorem high_gaussian_mass_gamma_cancel (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hRH : RiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (he : χ.Even) {x : ℝ} (hx : 0 < x) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    ((∑' ρ : ℂ, ‖K.zeroTerm χ x ρ‖ : ℝ) : ℂ) - K.xiMass =
      d *
            ((∫ t : ℝ, -logDeriv χ.completedLFunction (l t + 1 / 2) * K.massExtension (l t)) -
              (∫ t : ℝ,
                -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (l t + 1 / 2) *
                  K.massExtension (l t)) -
              (∫ t : ℝ, (1 / (r t - ((-1 / 2 : ℝ) : ℂ))) * K.massExtension (r t)) -
              ∫ t : ℝ, (1 / (r t - ((1 / 2 : ℝ) : ℂ))) * K.massExtension (r t)) +
          (∑' n : ℕ,
            ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
              (1 : DirichletCharacter ℂ 1) n *
              (K.massProfile n : ℂ)) -
        (∑' n : ℕ,
          ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n *
            (K.massProfile n : ℂ)) := by
  intro l r d
  have hc := high_gaussian_mass_profile_contours K hq hg hp hne hx
  have hz := high_gaussian_xi_mass_contours K hRH
  have hG := high_gaussian_even_mass_gamma K he
  have hA := high_gaussian_xi_right_split K
  dsimp only at hc hz hG hA
  rw [hc, hz, hG]
  linear_combination -hA

end PseudoPrime.PrimeTestBounds.MillerRabin
