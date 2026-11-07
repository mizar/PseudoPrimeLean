/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPolePoissonFormula
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaSignedPoissonIdentity

/-! # Signed analytic side of the refined Poisson identity -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The signed analytic side of the Poisson formula at distance `u`.
It retains the conductor, Gamma and ordinary L-function logarithmic derivatives
without taking absolute values. -/
noncomputable def refinedPoissonAnalytic {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (u : ℝ) :
    ℝ :=
  Real.log q / 2 + (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re +
    (logDeriv χ.LFunction (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re

/-- Under individual RH, the Poisson zero sum equals its signed conductor,
Gamma and ordinary L-function side at every distance above one half. This
retains all signs for the differentiated sixth-pole calculation. -/
theorem refined_poisson_eq_signed {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) {a : ℝ} (ha : 1 / 2 < a) :
    refinedPoissonZeroSum χ a = refinedPoissonAnalytic χ a := by
  have hσ : 1 < (1 / 2 : ℝ) + a := by linarith only [ha]
  have h :=
    AnalyticNumberTheory.DirichletLFunction.poissonSum_eq_signedOrdinary_RH hq hRH hp hne hinv hσ
  have hn : (1 / 2 : ℝ) + a - 1 / 2 = a := by ring
  rw [hn] at h
  unfold refinedPoissonZeroSum refinedPoissonAnalytic
  rw [tsum_congr
      (fun ρ ↦
        AnalyticNumberTheory.DirichletLFunction.completed_resolventTerm_eq_poisson hRH hp hne hinv a
          ρ)]
  simpa only [Complex.ofReal_add] using h

/-- The actual refined sixth-pole zero mass equals the second-order
Poisson differential operator applied to the signed analytic side. Equality
on an open half-line transfers both derivatives at the chosen pole distance. -/
theorem refined_six_pole_signed_formula {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) :
    8 *
        (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ‖refinedSixPoleKernel.function (Complex.I * ρ.im)‖) =
      3 * refinedPoissonAnalytic χ (27 / 25) -
          3 * (27 / 25 : ℝ) * deriv (refinedPoissonAnalytic χ) (27 / 25) +
        (27 / 25 : ℝ) ^ 2 * deriv (deriv (refinedPoissonAnalytic χ)) (27 / 25) := by
  have ha : (1 / 2 : ℝ) < 27 / 25 := by norm_num only
  have he : refinedPoissonZeroSum χ =ᶠ[nhds (27 / 25 : ℝ)] refinedPoissonAnalytic χ := by
    filter_upwards [Ioi_mem_nhds ha] with u hu
    exact refined_poisson_eq_signed hq hRH hp hne hinv hu
  have hd :
    deriv (refinedPoissonZeroSum χ) =ᶠ[nhds (27 / 25 : ℝ)] deriv (refinedPoissonAnalytic χ) := by
    filter_upwards [Ioi_mem_nhds ha] with u hu
    have hu' : refinedPoissonZeroSum χ =ᶠ[nhds u] refinedPoissonAnalytic χ := by
      filter_upwards [Ioi_mem_nhds hu] with v hv
      exact refined_poisson_eq_signed hq hRH hp hne hinv hv
    exact hu'.deriv_eq
  have h := refined_six_pole_poisson_formula hq hRH hp hne hinv
  rw [he.eq_of_nhds, he.deriv_eq, hd.deriv_eq] at h
  exact h

/-- The signed non-conductor part of the Poisson formula, retaining the
Gamma and ordinary L-function logarithmic derivatives together. Its first two
derivatives contribute the nonconstant part of the sixth-pole zero mass. -/
noncomputable def refinedPoissonRemainder {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (u : ℝ) :
    ℝ :=
  (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re +
    (logDeriv χ.LFunction (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re

/-- Under individual RH, the actual refined sixth-pole zero mass has the
exact conductor coefficient `3/16` after division by eight. The remaining
terms are the second-order differential operator applied to the signed Gamma
and ordinary L-function contribution. This keeps the Euler correction signed. -/
theorem refined_six_pole_conductor_formula {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    8 *
        (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ‖refinedSixPoleKernel.function (Complex.I * ρ.im)‖) =
      (3 / 2 : ℝ) * Real.log q + 3 * refinedPoissonRemainder χ (27 / 25) -
          3 * (27 / 25 : ℝ) * deriv (refinedPoissonRemainder χ) (27 / 25) +
        (27 / 25 : ℝ) ^ 2 * deriv (deriv (refinedPoissonRemainder χ)) (27 / 25) := by
  have he : refinedPoissonAnalytic χ = fun u ↦ Real.log q / 2 + refinedPoissonRemainder χ u := by
    funext u
    simp only [refinedPoissonAnalytic, refinedPoissonRemainder]
    ring
  have hd : deriv (refinedPoissonAnalytic χ) = deriv (refinedPoissonRemainder χ) := by
    rw [he]
    funext u
    exact deriv_const_add (Real.log q / 2)
  have h := refined_six_pole_signed_formula hq hRH hp hne hinv
  rw [hd, he] at h
  simp only at h
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
