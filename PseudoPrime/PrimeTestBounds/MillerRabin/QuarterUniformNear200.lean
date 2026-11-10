/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformClosedNegative
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaFirstNear200

/-! # Uniform residual with the improved Gamma correction -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At radii from 199 through 200, the improved first Gamma correction and
closed Euler-tail residual imply a quarter-square witness for a uniform triple. -/
theorem quarter_uniform_residual_near200 {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {r : ℝ} (hr : 199 ≤ r) (hR : r ≤ 200) (hU : Real.log n ≤ 2 * r)
    (hcut : r ^ 2 ≤ (1 / 4 : ℝ) * Real.log n ^ 2)
    (hgap :
      quarterCenteredClosedResidual r - (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 -
          4 * quarterGammaDensity (Real.log (r ^ 2) + 21 / 8) -
          3 / 25 -
          7 / 250 -
          (27 / 25 : ℝ) ^ 5 * (33 / 500) ≤
        (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
          (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hr180 : 180 ≤ r := by linarith only [hr]
  have hy := quarter_shift_log_ge_twelve hr180
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
  have hfirst := quarter_first_correction_199_200 hr hR
  have hprefix := quarter_reflected_prefix_180_200 hr180 hR
  have hs : (13 : ℝ) ≤ Real.sqrt r := Real.le_sqrt_of_sq_le (by nlinarith only [hr])
  have hi := one_div_le_one_div_of_le hr0 hR
  have hgain :
    (33 / 500 : ℝ) ≤ 3195 / 100000 + (12207 / 10000 : ℝ) / r + (11 / 5000 : ℝ) * Real.sqrt r := by
    norm_num only at hi ⊢
    ring_nf at hi ⊢
    linarith only [hi, hs]
  have hgain' := mul_le_mul_of_nonneg_left hgain (show (0 : ℝ) ≤ (27 / 25 : ℝ) ^ 5 by norm_num only)
  apply quarter_uniform_centered_baseline hn ho hu hGRH hr180 hy hH hU hcut
  have hw :
    3 * Real.log (2 * Real.pi) * refinedWeight (1 / r ^ 2) / r =
      3 * Real.log (2 * Real.pi) * quarterReflectedScale r := by
    rw [mul_div_assoc, quarter_reflected_scale_eq hr0]
  rw [hw]
  dsimp only [quarterCenteredClosedResidual] at hgap
  change
    (4 * r) * quarterReflectedScale r -
          3 * quarterGammaFirstCorrection (Real.log (r ^ 2) + 21 / 8) -
          4 * quarterGammaDensity (Real.log (r ^ 2) + 21 / 8) -
          4 * ∑ k ∈ Finset.Ioc 0 2701, refinedDualWeight (r ^ 2) k +
        quarterMomentScale r +
        (3 / 8 : ℝ) * (2 * r) +
        -(3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        4 * quarterEulerClosedTailCap (r ^ 2) ≤
      _
  ring_nf at hgap he hfirst hprefix hgain' ⊢
  linarith only [hgap, he, hfirst, hprefix, hgain']

/-- Replace the Gamma density by the reflected scale in the near-200 residual
criterion to obtain a quarter-square witness. -/
theorem quarter_uniform_near200_scaled {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {r : ℝ} (hr : 199 ≤ r) (hR : r ≤ 200) (hU : Real.log n ≤ 2 * r)
    (hcut : r ^ 2 ≤ (1 / 4 : ℝ) * Real.log n ^ 2)
    (hgap :
      quarterCenteredClosedResidual r - (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 -
          4 * quarterReflectedScale r -
          3 / 25 -
          7 / 250 -
          (27 / 25 : ℝ) ^ 5 * (33 / 500) ≤
        (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
          (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply quarter_uniform_residual_near200 hn ho hu hGRH hr hR hU hcut
  rw [quarter_density_eq_scale (by linarith only [hr])]
  exact hgap

end PseudoPrime.PrimeTestBounds.MillerRabin
