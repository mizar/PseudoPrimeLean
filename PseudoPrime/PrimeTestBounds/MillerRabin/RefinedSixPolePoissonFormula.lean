/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPolePoissonDerivative
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleZeroIdentity

/-! # Differentiated Poisson identity for the refined kernel -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The real Poisson series of completed zeros at a variable pole distance.
The multiplicity is the completed L-function divisor. At positive distances
its convergence and two derivatives are established under individual RH. -/
noncomputable def refinedPoissonZeroSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (u : ℝ) :
    ℝ :=
  ∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * (u / (u ^ 2 + ρ.im ^ 2))

/-- Under individual RH, the derivative of the completed Poisson zero sum is
the absolutely convergent series of first termwise derivatives. -/
theorem refined_poisson_deriv {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) {a : ℝ} (ha : 0 < a) :
    deriv (refinedPoissonZeroSum χ) a =
      ∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          ((ρ.im ^ 2 - a ^ 2) / (a ^ 2 + ρ.im ^ 2) ^ 2) := by
  unfold refinedPoissonZeroSum
  exact (hasDerivAt_completed_poisson_sum hq hRH hp hne hinv ha).deriv

/-- Under individual RH, the second derivative of the completed Poisson
zero sum is the absolutely convergent series of second termwise derivatives.
Local agreement of the first derivative with that series permits the second
uniform differentiation. -/
theorem refined_poisson_deriv_two {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) {a : ℝ} (ha : 0 < a) :
    deriv (deriv (refinedPoissonZeroSum χ)) a =
      ∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          (2 * a * (a ^ 2 - 3 * ρ.im ^ 2) / (a ^ 2 + ρ.im ^ 2) ^ 3) := by
  have he :
    (fun u : ℝ ↦ deriv (refinedPoissonZeroSum χ) u) =ᶠ[nhds a]
      (fun u : ℝ ↦
        ∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ((ρ.im ^ 2 - u ^ 2) / (u ^ 2 + ρ.im ^ 2) ^ 2)) := by
    filter_upwards [Ioi_mem_nhds ha] with u hu
    exact refined_poisson_deriv hq hRH hp hne hinv hu
  exact
    ((hasDerivAt_completed_poisson_deriv_sum hq hRH hp hne hinv ha).congr_of_eventuallyEq he).deriv

/-- Under individual RH, the actual refined-kernel zero mass is the exact
combination of the completed Poisson sum and its first two derivatives at
`27/25`. This is the normalized differentiated-Poisson identity needed for
the sharp sixth-pole zero-mass estimate. -/
theorem refined_six_pole_poisson_formula {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    8 *
        (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ‖refinedSixPoleKernel.function (Complex.I * ρ.im)‖) =
      3 * refinedPoissonZeroSum χ (27 / 25) -
          3 * (27 / 25 : ℝ) * deriv (refinedPoissonZeroSum χ) (27 / 25) +
        (27 / 25 : ℝ) ^ 2 * deriv (deriv (refinedPoissonZeroSum χ)) (27 / 25) := by
  rw [refined_poisson_deriv hq hRH hp hne hinv (by norm_num only),
    refined_poisson_deriv_two hq hRH hp hne hinv (by norm_num only)]
  simpa only [refinedPoissonZeroSum] using refined_six_pole_zero_identity hq hRH hp hne hinv

/-- Under individual RH, the completed-zero Poisson sum at a positive
distance equals the real completed logarithmic derivative at `1/2+a` plus
half the conductor logarithm. Convert the ordinate resolvent to the completed
Poisson kernel using the critical-line zero condition. -/
theorem refined_poisson_eq_logDeriv {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) {a : ℝ} (ha : 0 < a) :
    refinedPoissonZeroSum χ a =
      (logDeriv χ.completedLFunction (((1 / 2 : ℝ) + a : ℝ) : ℂ)).re + Real.log q / 2 := by
  have hs : (1 / 2 : ℝ) < (((1 / 2 + a : ℝ) : ℂ)).re := by
    simp only [Complex.ofReal_re]
    linarith only [ha]
  have h :=
    AnalyticNumberTheory.DirichletLFunction.completed_poissonSum_eq_logDeriv_re hq hRH hp hne hinv
      hs
  have hn : (1 / 2 : ℝ) + a - 1 / 2 = a := by ring
  simp only [Complex.ofReal_re, hn] at h
  unfold refinedPoissonZeroSum
  rw [tsum_congr
      (fun ρ ↦
        AnalyticNumberTheory.DirichletLFunction.completed_resolventTerm_eq_poisson hRH hp hne hinv a
          ρ)]
  simpa only [Complex.ofReal_add] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
