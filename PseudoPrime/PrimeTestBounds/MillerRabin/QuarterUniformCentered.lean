/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleCenteredNumerics
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformFromBounds

/-! # Uniform triple witnesses from the centered principal gap -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A uniform Korselt triple has a quarter-square rejecting prime when the
centered scalar gap holds at square scale `r²`. GRH supplies the principal
comparison; the remaining scalar hypothesis contains the reflected Euler term
and the Euler prefix and can be bounded separately. -/
theorem quarter_uniform_of_centered {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r H : ℝ} (hr : 34 ≤ r)
    (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) (r ^ 2) ≤ H) (hU : Real.log n ≤ 2 * r)
    (hcut : r ^ 2 ≤ (1 / 4 : ℝ) * Real.log n ^ 2)
    (hcert :
      (4 * r) *
              (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
                (r ^ 2) ^ (-(27 / 25 : ℝ)) *
                ((21 / 8 : ℝ) + Real.log (r ^ 2)) ^ 5) +
            (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
            H +
            (3 / 8 : ℝ) * (2 * r) +
            (65 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 -
          4 *
            ∑ k ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊,
              ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k ≤
        (27 / 25 : ℝ) ^ 5 *
            ((24439 / 50000 : ℝ) * r - (108 / 1000 : ℝ) * Real.sqrt r - (6695 / 100000 : ℝ) -
              (29757 / 10000 : ℝ) / r -
              (526064 / 10000000 : ℝ) / Real.sqrt r) -
          3 * Real.log (2 * Real.pi) * refinedWeight (1 / r ^ 2) / r) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hr2 : (1 : ℝ) ≤ r ^ 2 := by nlinarith only [hr]
  let S : ℝ :=
    ∑ k ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊,
      (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) k).re
  let P : ℝ :=
    ∑ k ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k
  let F : ℝ := (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) k).re
  have hcenter := refined_combined_centered_numeric hGRH.riemann hr
  have hb : quarterUniformBudget (r ^ 2) (2 * r) P F H ≤ 4 * S := by
    dsimp only [quarterUniformBudget, S, P, F]
    linarith only [hcert, hcenter]
  exact quarter_uniform_of_bounds hn ho hu hGRH hr2 hH hU hcut le_rfl le_rfl le_rfl hb

end PseudoPrime.PrimeTestBounds.MillerRabin
