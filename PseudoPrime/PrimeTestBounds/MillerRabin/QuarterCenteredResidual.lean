/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedScale
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentIntegralCaps
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCentered
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerPrefixAt

/-! # Decreasing residual for centered uniform-triple comparisons -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The reflected-moment upper bound at square scale `r²`, using the six
certified Mangoldt moments. This bounds the actual reflected Euler term. -/
noncomputable def quarterMomentScale (r : ℝ) : ℝ :=
  ((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) * (r ^ 2) ^ (-(27 / 25 : ℝ)) *
    quarterMomentPolynomial ((21 / 8 : ℝ) + Real.log (r ^ 2))

/-- The scalar residual after inserting the common 1000-prefix lower bound
and the centered principal comparison. Its nonconstant terms decrease from 34. -/
noncomputable def quarterCenteredResidual (r : ℝ) : ℝ :=
  4 * r * quarterReflectedScale r + (3 * (1839 / 1000 : ℝ)) * quarterReflectedScale r +
    quarterMomentScale r +
    (27 / 25 : ℝ) ^ 5 *
      ((6695 / 100000 : ℝ) + (29757 / 10000 : ℝ) / r + (526064 / 10000000 : ℝ) / Real.sqrt r) +
    (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
    ((65 / 100 : ℝ) - 4 * (223 / 125 : ℝ)) * (27 / 25 : ℝ) ^ 5

/-- The explicit centered residual is nonincreasing for radii at least 34.
This combines the logarithmic-power monotonicity and reciprocal comparisons. -/
theorem quarter_centered_residual_antitone : AntitoneOn quarterCenteredResidual (Set.Ici 34) := by
  intro x hx y hy hxy
  have hx' : (34 : ℝ) ≤ x := hx
  have hx0 : 0 < x := by linarith only [hx']
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hc := quarter_conductor_antitone hx hy hxy
  have hk := quarter_moment_term_antitone 5 (by decide) hx hy hxy
  have hm := quarter_moment_scale_antitone hx hy hxy
  have hi := one_div_le_one_div_of_le hx0 hxy
  have hroot := one_div_le_one_div_of_le hs (Real.sqrt_le_sqrt hxy)
  have hC : 0 ≤ ((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) := by positivity
  have hc' := mul_le_mul_of_nonneg_left hc (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hC)
  have hk' :=
    mul_le_mul_of_nonneg_left hk
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 3 * (1839 / 1000 : ℝ)) hC)
  have hm' := mul_le_mul_of_nonneg_left hm hC
  have hi' :=
    mul_le_mul_of_nonneg_left hi (show (0 : ℝ) ≤ (27 / 25 : ℝ) ^ 5 * (29757 / 10000) by positivity)
  have hs' :=
    mul_le_mul_of_nonneg_left hroot
      (show (0 : ℝ) ≤ (27 / 25 : ℝ) ^ 5 * (526064 / 10000000) by positivity)
  dsimp only [quarterCenteredResidual, quarterReflectedScale, quarterMomentScale]
  ring_nf at hc' hk' hm' hi' hs' ⊢
  linarith only [hc', hk', hm', hi', hs']

/-- If the scalar gap dominates the residual adjusted by an Euler-prefix lower
bound, GRH gives a quarter-square rejecting prime for a uniform Korselt triple.
The reflected moments are supplied by proved bounds. -/
theorem quarter_uniform_of_residual_prefix {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {r P : ℝ} (hr : 34 ≤ r) (hU : Real.log n ≤ 2 * r) (hcut : r ^ 2 ≤ (1 / 4 : ℝ) * Real.log n ^ 2)
    (hP :
      P ≤ ∑ k ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k)
    (hgap :
      quarterCenteredResidual r - 4 * (P - (223 / 125 : ℝ) * (27 / 25 : ℝ) ^ 5) ≤
        (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
          (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hr0 : 0 < r := (by norm_num only : (0 : ℝ) < 34).trans_le hr
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
  have hc :
    (4 * r) * quarterReflectedScale r + (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 + quarterMomentScale r +
          (3 / 8 : ℝ) * (2 * r) +
          (65 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 -
        4 *
          ∑ k ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k ≤
      (27 / 25 : ℝ) ^ 5 *
          ((24439 / 50000 : ℝ) * r - (108 / 1000 : ℝ) * Real.sqrt r - (6695 / 100000 : ℝ) -
            (29757 / 10000 : ℝ) / r -
            (526064 / 10000000 : ℝ) / Real.sqrt r) -
        3 * Real.log (2 * Real.pi) * refinedWeight (1 / r ^ 2) / r := by
    have hw :
      3 * Real.log (2 * Real.pi) * refinedWeight (1 / r ^ 2) / r =
        3 * Real.log (2 * Real.pi) * quarterReflectedScale r := by
      rw [mul_div_assoc, quarter_reflected_scale_eq hr0]
    rw [hw]
    dsimp only [quarterCenteredResidual] at hgap
    ring_nf at hgap hP he ⊢
    linarith only [hgap, hP, he]
  exact quarter_uniform_of_centered hn ho hu hGRH hr hH hU hcut hc

/-- The certified 1000-prefix discharges the Euler hypothesis in the
centered residual criterion for every radius at least 34. -/
theorem quarter_uniform_of_residual {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ} (hr : 34 ≤ r)
    (hU : Real.log n ≤ 2 * r) (hcut : r ^ 2 ≤ (1 / 4 : ℝ) * Real.log n ^ 2)
    (hgap :
      quarterCenteredResidual r ≤
        (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
          (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hr1000 : (1000 : ℝ) ≤ r ^ 2 := by nlinarith only [hr]
  have hP := refined_euler_prefix_1000_at hr1000
  apply quarter_uniform_of_residual_prefix hn ho hu hGRH hr hU hcut hP
  simpa only [sub_self, mul_zero, sub_zero] using hgap

end PseudoPrime.PrimeTestBounds.MillerRabin
