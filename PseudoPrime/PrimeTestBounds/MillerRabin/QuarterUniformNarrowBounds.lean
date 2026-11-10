/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformPrefixBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredNarrowNumeric

/-! # Uniform-triple witness with narrow centered costs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The narrow centered principal bound combines with the Gamma-pole
and reflected Euler savings to yield a uniform-triple witness. -/
theorem quarter_uniform_centered_narrow {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {r H : ℝ} (hr : 180 ≤ r) (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) (r ^ 2) ≤ H)
    (hU : Real.log n ≤ 2 * r) (hcut : r ^ 2 ≤ (1 / 4 : ℝ) * Real.log n ^ 2)
    (hcert :
      (4 * r) *
                  (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
                    (r ^ 2) ^ (-(27 / 25 : ℝ)) *
                    ((21 / 8 : ℝ) + Real.log (r ^ 2)) ^ 5) +
                (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 -
              3 * quarterGammaFirstCorrection (Real.log (r ^ 2) + 21 / 8) -
              4 * ∑ k ∈ Finset.Ioc 0 2701, refinedDualWeight (r ^ 2) k +
            H +
            (3 / 8 : ℝ) * (2 * r) +
            (65 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 -
          4 *
            ∑ k ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊,
              ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k ≤
        (27 / 25 : ℝ) ^ 5 *
            ((24439 / 50000 : ℝ) * r - (529 / 5000 : ℝ) * Real.sqrt r - (7 / 200 : ℝ) -
              (351 / 200 : ℝ) / r -
              (526064 / 10000000 : ℝ) / Real.sqrt r) -
          3 * Real.log (2 * Real.pi) * refinedWeight (1 / r ^ 2) / r) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hr2 : (1 : ℝ) ≤ r ^ 2 := by nlinarith only [hr]
  have ht : ∀ k ∈ Finset.Ioc (0 : ℕ) 2701, (k : ℝ) ≤ r ^ 2 := by
    intro k hk
    have hk' : k ≤ 2701 := (Finset.mem_Ioc.mp hk).2
    have hkr : (k : ℝ) ≤ 2701 := by exact_mod_cast hk'
    nlinarith only [hkr, hr]
  let S : ℝ :=
    ∑ k ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊,
      (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) k).re
  let P : ℝ :=
    ∑ k ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k
  let F : ℝ := (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) k).re
  have hcenter := quarter_combined_centered_numeric hGRH.riemann hr
  have hb :
    quarterUniformBudget (r ^ 2) (2 * r) P F H -
        3 * quarterGammaFirstCorrection (Real.log (r ^ 2) + 21 / 8) -
        4 * ∑ k ∈ Finset.Ioc 0 2701, refinedDualWeight (r ^ 2) k ≤
      4 * S := by
    dsimp only [quarterUniformBudget, S, P, F]
    linarith only [hcert, hcenter]
  exact
    quarter_uniform_bounds_prefix hn ho hu hGRH hr2 hH hU (Finset.Ioc 0 2701) ht hcut le_rfl le_rfl
      le_rfl hb

/-- On radii 180 through 200, the previous residual admits the explicit
narrow-window gain in addition to both certified correction terms. -/
theorem quarter_uniform_residual_narrow {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {r P : ℝ} (hr : 180 ≤ r) (hR : r ≤ 200) (hU : Real.log n ≤ 2 * r)
    (hcut : r ^ 2 ≤ (1 / 4 : ℝ) * Real.log n ^ 2)
    (hP :
      P ≤ ∑ k ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k)
    (hgap :
      quarterCenteredResidual r - 4 * (P - (223 / 125 : ℝ) * (27 / 25 : ℝ) ^ 5) - 57 / 500 -
          7 / 250 -
          (27 / 25 : ℝ) ^ 5 * (33 / 500) ≤
        (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
          (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hr0 : 0 < r := by linarith only [hr]
  have hr2 : (1 : ℝ) ≤ r ^ 2 := by nlinarith only [hr]
  have hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) (r ^ 2) ≤ quarterMomentScale r := by
    exact
      quarter_reflected_of_moments hr2
        (quarter_moment_bounds_of_integrals hGRH.riemann quarter_moment_integral_bounds)
  have hk : 0 ≤ quarterReflectedScale r := by
    dsimp only [quarterReflectedScale]
    have hl : 0 ≤ Real.log (r ^ 2) := Real.log_nonneg hr2
    positivity
  have he :=
    mul_le_mul_of_nonneg_right Analysis.log_two_mul_pi_lt.le
      (show (0 : ℝ) ≤ 3 * quarterReflectedScale r by positivity)
  have hfirst := quarter_first_correction_180_200 hr hR
  have hprefix := quarter_reflected_prefix_180_200 hr hR
  have hs : (13 : ℝ) ≤ Real.sqrt r := Real.le_sqrt_of_sq_le (by nlinarith only [hr])
  have hi := one_div_le_one_div_of_le hr0 hR
  have hgain :
    (33 / 500 : ℝ) ≤ 3195 / 100000 + (12207 / 10000 : ℝ) / r + (11 / 5000 : ℝ) * Real.sqrt r := by
    norm_num only at hi ⊢
    ring_nf at hi ⊢
    linarith only [hi, hs]
  have hgain' := mul_le_mul_of_nonneg_left hgain (show (0 : ℝ) ≤ (27 / 25 : ℝ) ^ 5 by norm_num only)
  apply quarter_uniform_centered_narrow hn ho hu hGRH hr hH hU hcut
  have hw :
    3 * Real.log (2 * Real.pi) * refinedWeight (1 / r ^ 2) / r =
      3 * Real.log (2 * Real.pi) * quarterReflectedScale r := by
    rw [mul_div_assoc, quarter_reflected_scale_eq hr0]
  rw [hw]
  dsimp only [quarterCenteredResidual] at hgap
  change
    (4 * r) * quarterReflectedScale r + (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 -
            3 * quarterGammaFirstCorrection (Real.log (r ^ 2) + 21 / 8) -
            4 * ∑ k ∈ Finset.Ioc 0 2701, refinedDualWeight (r ^ 2) k +
          quarterMomentScale r +
          (3 / 8 : ℝ) * (2 * r) +
          (65 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 -
        4 *
          ∑ k ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k ≤
      _
  ring_nf at hgap hP he hfirst hprefix hgain' ⊢
  linarith only [hgap, hP, he, hfirst, hprefix, hgain']

end PseudoPrime.PrimeTestBounds.MillerRabin
