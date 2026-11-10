/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformFromBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028SharpPrincipal

/-! # Uniform triple cells with an Abel bound for the full principal sum -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The full principal sum's explicit Abel upper bound at scale `X`.
The square-root main term and two certified variation errors are retained. -/
noncomputable def quarterUniformAbel (X : ℝ) : ℝ :=
  Real.sqrt X * (refinedSixPoleKernel.function (1 / 2)).re +
    ((231 / 5000 : ℝ) * ((203 / 1000) * (27 / 25 : ℝ) ^ 5) +
      ((1839 / 1000 : ℝ) * (Real.log X + 21 / 8) + 2) * ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) /
        Real.sqrt X)

/-- A finite principal lower bound and Euler-prefix lower bound yield a
quarter-square witness whenever their cell budget fits the Abel upper bound.
The analytic full-sum bound follows from RH, which is supplied by GRH. -/
theorem quarter_uniform_of_abel {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X U S P H : ℝ} (hX : 1 ≤ X)
    (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X ≤ H) (hU : Real.log n ≤ U)
    (hcut : X ≤ (1 / 4 : ℝ) * Real.log n ^ 2)
    (hS :
      S ≤
        ∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re)
    (hP : P ≤ ∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k)
    (hcert : quarterUniformBudget X U P (quarterUniformAbel X) H ≤ 4 * S) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hfull := (abs_le.mp (target028_full_principal_error hGRH.riemann hX)).2
  have hF :
    (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re ≤
      quarterUniformAbel X := by
    dsimp only [quarterUniformAbel]
    linarith only [hfull]
  exact quarter_uniform_of_bounds hn ho hu hGRH hX hH hU hcut hS hP hF hcert

end PseudoPrime.PrimeTestBounds.MillerRabin
