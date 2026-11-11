/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformAnyCutoff
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredResidual
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredPsiLower

/-! # Uniform witnesses from a log-square Chebyshev lower bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a log-square Chebyshev lower bound at `r²` and a scalar budget
give a uniform rejecting prime bounded by `r²`. The centered Abel estimate
transfers the boundary assumption to the closed witness theorem. -/
theorem uniform_log_square_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ} (hr : 180 ≤ r)
    (hpsi : r ^ 2 - (1 / 12 : ℝ) * r * Real.log (r ^ 2) ^ 2 ≤ Chebyshev.psi (r ^ 2))
    (hcert :
      (2 * Real.log n) * quarterReflectedScale r + (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
              quarterMomentScale r +
              (3 / 8 : ℝ) * Real.log n -
            (3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
          4 * quarterEulerClosedTailCap (r ^ 2) ≤
        (27 / 25 : ℝ) ^ 5 *
            ((24439 / 50000 : ℝ) * r - 7 / 200 - (351 / 200 : ℝ) / r -
              (61 / 3000 : ℝ) * Real.log (r ^ 2) ^ 2) -
          3 * Real.log (2 * Real.pi) * quarterReflectedScale r) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hr0 : 0 < r := by linarith only [hr]
  have hr2 : (625 : ℝ) ≤ r ^ 2 := by nlinarith only [hr]
  have hRH := hGRH.riemann
  have hm := quarter_moment_bounds_of_integrals hRH quarter_moment_integral_bounds
  have href :
    refinedReflectedEuler (1 : DirichletCharacter ℂ 1) (r ^ 2) ≤ quarterMomentScale r := by
    exact quarter_reflected_of_moments (by linarith only [hr2]) hm
  have hM : 0 ≤ (1 / 12 : ℝ) * r * Real.log (r ^ 2) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num only) hr0.le) (sq_nonneg _)
  have hcenter :=
    quarter_combined_of_psi hRH (show (1 : ℝ) ≤ r by linarith only [hr]) hM
      (show -((1 / 12 : ℝ) * r * Real.log (r ^ 2) ^ 2) ≤ Chebyshev.psi (r ^ 2) - r ^ 2 by
        linarith only [hpsi])
  have hs := quarter_reflected_scale_eq hr0
  simp only [div_eq_mul_inv] at hs hcenter
  rw [show
      3 * Real.log (2 * Real.pi) * refinedWeight (1 * (r ^ 2)⁻¹) * r⁻¹ =
        3 * Real.log (2 * Real.pi) * (refinedWeight (1 * (r ^ 2)⁻¹) * r⁻¹)
      by ring,
    hs] at hcenter
  have hcenter' :
    (27 / 25 : ℝ) ^ 5 *
          ((24439 / 50000 : ℝ) * r - 7 / 200 - (351 / 200 : ℝ) / r -
            (61 / 3000 : ℝ) * Real.log (r ^ 2) ^ 2) -
        3 * Real.log (2 * Real.pi) * quarterReflectedScale r ≤
      4 *
          (∑ k ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) k).re) -
        (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) k).re := by
    have hrinv : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0.ne'
    ring_nf at hcenter ⊢
    nlinarith only [hcenter, hrinv]
  have hgamma : 0 ≤ quarterGammaFirstCorrection (Real.log (r ^ 2) + 21 / 8) := by
    apply quarter_gamma_first_nonneg
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ r ^ 2 by linarith only [hr2])
    linarith only [hlog]
  apply
    quarter_uniform_bounds_any hn ho hu hGRH hr2 href le_rfl ∅
      (by
        intro k hk; simp only [Finset.notMem_empty] at hk)
      le_rfl le_rfl
  dsimp only [quarterUniformClosedBudget, quarterReflectedScale] at hcert hcenter' ⊢
  simp only [Finset.sum_empty, mul_zero, sub_zero]
  ring_nf at hcenter' hcert hgamma ⊢
  linarith only [hcenter', hcert, hgamma]

end PseudoPrime.PrimeTestBounds.MillerRabin
