/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassXi
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassContour
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftZeta
import PseudoPrime.LLS.PaperStatements.MellinKernelSignedFormula

/-! # Cancellation of the shared Gamma integral in the middle Gaussian mass -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Integrals of the balanced components recombine into the mass function
as long as the weight is integrable against each component on the line. -/
private theorem fold_middle_mass_integrals (Q : Polynomial ℚ) (a : ℚ) {d : ℕ} (ha : 2 ≤ (a : ℝ))
    (hd : 1 ≤ d) (hQ : Q.natDegree ≤ d) (r : ℝ → ℂ) (hl : ∀ t, -(a : ℝ) < (r t).re)
    (hr : ∀ t, (r t).re < (a : ℝ)) (g : ℝ → ℂ) :
    let B := fun j ↦ balancedPoleKernel a ha (d + 1 - j)
    let c := fun j ↦ ((normSqPolynomial a Q).coeff j : ℂ)
    (∀ j, MeasureTheory.Integrable (fun t ↦ g t * (B j).function (r t))) →
      (∑ j ∈ Finset.range (d + 1), c j * (∫ t : ℝ, g t * (B j).function (r t))) =
        ∫ t : ℝ, g t * middleMassExtension Q a (d + 2) (r t) := by
  intro B c hi
  simp_rw [← MeasureTheory.integral_const_mul]
  rw [← MeasureTheory.integral_finsetSum _ (fun j _ ↦ (hi j).const_mul (c j))]
  apply MeasureTheory.integral_congr_ae
  exact
    Filter.Eventually.of_forall fun t ↦ by
      dsimp only
      rw [middle_mass_balanced_sum Q a ha hd hQ (hl t) (hr t), Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ mul_left_comm _ _ _

/-- The right Xi contour at unit scale splits the level-one Mangoldt sum into
the two rational poles and the common even gamma integral. -/
public theorem middle_xi_right_split (Q : Polynomial ℚ) (a : ℚ) {d₀ : ℕ} (ha : 2 ≤ (a : ℝ))
    (hd₀ : 1 ≤ d₀) (hQ : Q.natDegree ≤ d₀) :
    let χ₁ := (1 : DirichletCharacter ℂ 1)
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    (∑' n : ℕ,
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ₁ n *
          (middleMassProfile Q a d₀ n : ℂ)) =
      d *
          ((∫ t : ℝ,
              -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (r t + 1 / 2) *
                middleMassExtension Q a (d₀ + 2) (r t)) +
            (∫ t : ℝ, (1 / (r t - ((-1 / 2 : ℝ) : ℂ))) * middleMassExtension Q a (d₀ + 2) (r t)) +
            ∫ t : ℝ, (1 / (r t - ((1 / 2 : ℝ) : ℂ))) * middleMassExtension Q a (d₀ + 2) (r t)) +
        d *
          ∫ t : ℝ,
            logDeriv χ₁.gammaFactor (r t + 1 / 2) * middleMassExtension Q a (d₀ + 2) (r t) := by
  intro χ₁ r d
  let B := fun j ↦ balancedPoleKernel a ha (d₀ + 1 - j)
  let c := fun j ↦ ((normSqPolynomial a Q).coeff j : ℂ)
  let F := fun t ↦ -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (r t + 1 / 2)
  let P := fun (p : ℝ) t ↦ 1 / (r t - (p : ℂ))
  let G := fun t ↦ logDeriv χ₁.gammaFactor (r t + 1 / 2)
  have hd (j : ℕ) : (B j).delta = 1 / 8 := balanced_pole_delta _ _ _
  have hb (j : ℕ) : (9 / 16 : ℝ) ≤ 1 / 2 + (B j).delta := by
    rw [hd]; norm_num only
  have hre (t : ℝ) : (r t).re = 9 / 16 := by
    simp only [r, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hl (t : ℝ) : -(a : ℝ) < (r t).re := by
    rw [hre]; linarith only [ha]
  have hr (t : ℝ) : (r t).re < (a : ℝ) := by
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
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ₁ n *
          (middleMassProfile Q a d₀ n : ℂ)) =
      ∑ j ∈ Finset.range (d₀ + 1), c j * ∑' n : ℕ, (B j).summand χ₁ 1 n := by
    rw [← LLS.PaperStatements.MellinKernel.tsum_kernel_finset_sum _ B c χ₁ zero_lt_one]
    exact (tsum_congr (middle_mass_mangoldt Q a d₀ ha χ₁)).symm
  change
    _ =
      d *
          ((∫ t : ℝ, F t * middleMassExtension Q a (d₀ + 2) (r t)) +
            (∫ t : ℝ, P (-1 / 2) t * middleMassExtension Q a (d₀ + 2) (r t)) +
            ∫ t : ℝ, P (1 / 2) t * middleMassExtension Q a (d₀ + 2) (r t)) +
        d * ∫ t : ℝ, G t * middleMassExtension Q a (d₀ + 2) (r t)
  rw [hA]
  simp only [hh, mul_add, mul_left_comm (c _) d, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [fold_middle_mass_integrals Q a ha hd₀ hQ r hl hr F hF,
    fold_middle_mass_integrals Q a ha hd₀ hQ r hl hr (P (-1 / 2)) (hP _ (by norm_num only)),
    fold_middle_mass_integrals Q a ha hd₀ hQ r hl hr (P (1 / 2)) (hP _ (by norm_num only)),
    fold_middle_mass_integrals Q a ha hd₀ hQ r hl hr G hG]

/-- For an even primitive nonprincipal character, the right gamma integrals
cancel in the difference between the Dirichlet and Xi zero masses. -/
public theorem middle_mass_gamma_cancel (Q : Polynomial ℚ) (a : ℚ) {d₀ : ℕ} (ha : 2 ≤ (a : ℝ))
    (hd₀ : 1 ≤ d₀) (hQ : Q.natDegree ≤ d₀) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hRH : RiemannHypothesis) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (he : χ.Even) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) *
            middleMassExtension Q a (d₀ + 2) (Complex.I * ρ.im)) -
        middleXiMass Q a d₀ =
      d *
            ((∫ t : ℝ,
                -logDeriv χ.completedLFunction (l t + 1 / 2) *
                  middleMassExtension Q a (d₀ + 2) (l t)) -
              (∫ t : ℝ,
                -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (l t + 1 / 2) *
                  middleMassExtension Q a (d₀ + 2) (l t)) -
              (∫ t : ℝ, (1 / (r t - ((-1 / 2 : ℝ) : ℂ))) * middleMassExtension Q a (d₀ + 2) (r t)) -
              ∫ t : ℝ, (1 / (r t - ((1 / 2 : ℝ) : ℂ))) * middleMassExtension Q a (d₀ + 2) (r t)) +
          (∑' n : ℕ,
            ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
              (1 : DirichletCharacter ℂ 1) n *
              (middleMassProfile Q a d₀ n : ℂ)) -
        (∑' n : ℕ,
          ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n *
            (middleMassProfile Q a d₀ n : ℂ)) := by
  intro l r d
  have hc := middle_mass_contour_identity Q a ha hd₀ hQ hq hg hp hne
  have hz := middle_xi_mass_contours Q a ha hd₀ hQ hRH
  have hG : χ.gammaFactor = (1 : DirichletCharacter ℂ 1).gammaFactor := by
    funext z
    rw [he.gammaFactor_def,
      AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even.gammaFactor_def]
  have hA := middle_xi_right_split Q a ha hd₀ hQ
  dsimp only at hc hz hA
  rw [hG] at hc
  rw [hc, hz]
  linear_combination -hA

end PseudoPrime.PrimeTestBounds.MillerRabin
