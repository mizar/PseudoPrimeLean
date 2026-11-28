/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterKernel644
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleSignedPoisson

/-! # Completed-zero mass for the section 122 sixth-pole kernel -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At ordinate t the normalized kernel has the cubed resolvent norm at pole 107/100. -/
theorem quarter_zero_norm_644 (t : ℝ) :
    ‖quarterKernel644.function (Complex.I * t)‖ =
      (107 / 100 : ℝ) ^ 5 / ((107 / 100 : ℝ) ^ 2 + t ^ 2) ^ 3 := by
  change ‖Analysis.rationalPoleFunction 3 (50 / 107) (2687 / 2000) (Complex.I * t)‖ = _
  rw [Analysis.norm_rationalPoleFunction 3 (by norm_num only : (0 : ℝ) < 50 / 107)]
  have h : (107 / 100 : ℝ) ^ 2 + t ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (by norm_num only) (sq_nonneg t))
  have hd : 1 + (2 * (50 / 107 : ℝ) * t) ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (by norm_num only) (sq_nonneg _))
  apply (div_eq_div_iff (pow_ne_zero 3 hd) (pow_ne_zero 3 h)).2
  ring

/-- Under individual RH the section 122 zero mass is the
second-order Poisson operator at 107/100. -/
theorem quarter_poisson_formula_644 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) :
    8 *
        (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ‖quarterKernel644.function (Complex.I * ρ.im)‖) =
      3 * refinedPoissonZeroSum χ (107 / 100) -
          3 * (107 / 100 : ℝ) * deriv (refinedPoissonZeroSum χ) (107 / 100) +
        (107 / 100 : ℝ) ^ 2 * deriv (deriv (refinedPoissonZeroSum χ)) (107 / 100) := by
  rw [refined_poisson_deriv hq hRH hp hne hinv (by norm_num only),
    refined_poisson_deriv_two hq hRH hp hne hinv (by norm_num only)]
  have h := sixth_pole_zero_series_identity hq hRH hp hne hinv (a := 107 / 100) (by norm_num only)
  apply Eq.trans _ h
  rw [← tsum_mul_left]
  apply tsum_congr
  intro ρ
  rw [quarter_zero_norm_644]
  ring

/-- The signed analytic Poisson formula retains the Gamma and Euler contributions. -/
theorem quarter_signed_formula_644 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) :
    8 *
        (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ‖quarterKernel644.function (Complex.I * ρ.im)‖) =
      3 * refinedPoissonAnalytic χ (107 / 100) -
          3 * (107 / 100 : ℝ) * deriv (refinedPoissonAnalytic χ) (107 / 100) +
        (107 / 100 : ℝ) ^ 2 * deriv (deriv (refinedPoissonAnalytic χ)) (107 / 100) := by
  have ha : (1 / 2 : ℝ) < 107 / 100 := by norm_num only
  have he : refinedPoissonZeroSum χ =ᶠ[nhds (107 / 100 : ℝ)] refinedPoissonAnalytic χ := by
    filter_upwards [Ioi_mem_nhds ha] with u hu
    exact refined_poisson_eq_signed hq hRH hp hne hinv hu
  have hd :
    deriv (refinedPoissonZeroSum χ) =ᶠ[nhds (107 / 100 : ℝ)] deriv (refinedPoissonAnalytic χ) := by
    filter_upwards [Ioi_mem_nhds ha] with u hu
    have hu' : refinedPoissonZeroSum χ =ᶠ[nhds u] refinedPoissonAnalytic χ := by
      filter_upwards [Ioi_mem_nhds hu] with v hv
      exact refined_poisson_eq_signed hq hRH hp hne hinv hv
    exact hu'.deriv_eq
  have h := quarter_poisson_formula_644 hq hRH hp hne hinv
  rw [he.eq_of_nhds, he.deriv_eq, hd.deriv_eq] at h
  exact h

/-- For a primitive nonprincipal character under individual RH, eight times its zero mass
contains exactly three halves of the conductor logarithm. -/
theorem quarter_conductor_formula_644 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) :
    8 *
        (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ‖quarterKernel644.function (Complex.I * ρ.im)‖) =
      (3 / 2 : ℝ) * Real.log q + 3 * refinedPoissonRemainder χ (107 / 100) -
          3 * (107 / 100 : ℝ) * deriv (refinedPoissonRemainder χ) (107 / 100) +
        (107 / 100 : ℝ) ^ 2 * deriv (deriv (refinedPoissonRemainder χ)) (107 / 100) := by
  have he : refinedPoissonAnalytic χ = fun u ↦ Real.log q / 2 + refinedPoissonRemainder χ u := by
    funext u
    simp only [refinedPoissonAnalytic, refinedPoissonRemainder]
    ring
  have hd : deriv (refinedPoissonAnalytic χ) = deriv (refinedPoissonRemainder χ) := by
    rw [he]
    funext u
    exact deriv_const_add (Real.log q / 2)
  have h := quarter_signed_formula_644 hq hRH hp hne hinv
  rw [hd, he] at h
  simp only at h
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
