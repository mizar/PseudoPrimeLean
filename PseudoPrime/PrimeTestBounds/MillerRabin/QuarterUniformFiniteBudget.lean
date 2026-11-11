/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredResidual
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformClosedBounds
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredFinite465

/-! # Uniform quarter witnesses from the finite centered budget -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a scalar budget on the certified finite radius range gives a uniform
quarter-bound rejecting prime. The finite Chebyshev and moment bounds supply the
analytic inputs to the closed witness theorem. -/
theorem quarter_uniform_finite_budget {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {r : ℝ} (hr : (997 / 5 : ℝ) ≤ r) (hrU : r ≤ (465 / 2 : ℝ)) (hU : Real.log n ≤ 2 * r)
    (hcut : r ^ 2 ≤ (1 / 4 : ℝ) * Real.log n ^ 2)
    (hcert :
      (4 * r) * quarterReflectedScale r + (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
              quarterMomentScale r +
              (3 / 4 : ℝ) * r -
            (3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
          4 * quarterEulerClosedTailCap (r ^ 2) ≤
        (27 / 25 : ℝ) ^ 5 * ((24439 / 50000 : ℝ) * r - 7 / 200 - (29631 / 200 : ℝ) / r) -
          3 * Real.log (2 * Real.pi) * quarterReflectedScale r) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hr0 : 0 < r := by linarith only [hr]
  have hr2 : (625 : ℝ) ≤ r ^ 2 := by nlinarith only [hr]
  have hRH := hGRH.riemann
  have hm := quarter_moment_bounds_of_integrals hRH quarter_moment_integral_bounds
  have href :
    refinedReflectedEuler (1 : DirichletCharacter ℂ 1) (r ^ 2) ≤ quarterMomentScale r := by
    exact quarter_reflected_of_moments (by linarith only [hr2]) hm
  have hcenter := quarter_combined_finite465 hRH hr hrU
  have hs := quarter_reflected_scale_eq hr0
  simp only [div_eq_mul_inv] at hs hcenter
  rw [show
      3 * Real.log (2 * Real.pi) * refinedWeight (1 * (r ^ 2)⁻¹) * r⁻¹ =
        3 * Real.log (2 * Real.pi) * (refinedWeight (1 * (r ^ 2)⁻¹) * r⁻¹)
      by ring,
    hs] at hcenter
  have hgamma : 0 ≤ quarterGammaFirstCorrection (Real.log (r ^ 2) + 21 / 8) := by
    apply quarter_gamma_first_nonneg
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ r ^ 2 by linarith only [hr2])
    linarith only [hlog]
  apply
    quarter_uniform_bounds_closed hn ho hu hGRH hr2 href hU ∅
      (by
        intro k hk; simp only [Finset.notMem_empty] at hk)
      hcut le_rfl le_rfl
  dsimp only [quarterUniformClosedBudget, quarterReflectedScale] at hcert hcenter ⊢
  simp only [Finset.sum_empty, mul_zero, sub_zero]
  ring_nf at hcenter hcert hgamma ⊢
  linarith only [hcenter, hcert, hgamma]

end PseudoPrime.PrimeTestBounds.MillerRabin
