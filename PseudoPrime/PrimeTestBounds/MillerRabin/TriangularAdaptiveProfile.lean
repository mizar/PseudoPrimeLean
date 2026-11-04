/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularAdaptiveCoefficients

/-! # A triangular profile at each high logarithmic scale

The profile uses exact square roots and a quadratic root rather than a table of fixed
coefficients. Its margin retains one unit of strict slack.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For `L ≥ 3 * 10 ^ 10`, the adaptive radius, eighth root and square root form a
`TriangularProfile` with entrance `L`. The three-factor floor supplies the local
conditions and the positive quadratic root supplies the strict margin. Later witness
extraction can therefore use the profile at the actual input scale. -/
noncomputable def triangularAdaptiveProfile (L : ℝ) (hL : 30000000000 ≤ L) : TriangularProfile where
  C := (triangularAdaptiveRadius L) ^ 2
  T := L
  a := triangularAdaptiveRadius L
  m := triangularEighthRoot L
  v := Real.sqrt L
  b :=
    (165000 +
        (4000000000000 * (1001 / 1000) : ℝ) /
          (triangularAdaptiveRadius L * triangularEighthRoot L)) /
      L
  entry := hL
  root := by
    have ha := (triangularAdaptiveRadius_bounds hL).1
    linarith only [ha]
  localBudget := by
    have ha := (triangularAdaptiveRadius_bounds hL).1
    have hp := mul_le_mul_of_nonneg_right ha.le (by linarith only [hL])
    nlinarith only [hp, hL]
  square := le_rfl
  upper := by
    have ha := triangularAdaptiveRadius_bounds hL
    have h0 : 0 ≤ triangularAdaptiveRadius L := by linarith only [ha.1]
    have hs := pow_le_pow_left₀ h0 ha.2 2
    norm_num only [one_pow] at hs
    exact hs
  root16 := triangularAdaptive_root16 hL
  fourth := by
    have h0 : 0 < L := by linarith only [hL]
    exact ⟨Real.sqrt_pos.mpr h0, (Real.sq_sqrt h0.le).le⟩
  cost := by
    have h0 : L ≠ 0 := (show 0 < L by linarith only [hL]).ne'
    rw [div_mul_cancel₀ _ h0]
  triple := by
    have hg := triangularAdaptiveFloor_bounds L
    have hg0 : 0 ≤ triangularAdaptiveFloor L := by
      have hs : (0 : ℝ) ≤ (5313 / 10000) ^ 2 := sq_nonneg _
      linarith only [hg.1, hs]
    have hr : Real.sqrt (triangularAdaptiveFloor L) ≤ triangularAdaptiveRadius L := le_max_left _ _
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hr 2
    rw [Real.sq_sqrt hg0] at hsq
    by_cases h : (1820000000000 : ℝ) ≤ L
    · right
      rw [triangularAdaptiveFloor, ite_eq_left h] at hsq
      exact ⟨hsq, h⟩
    · left
      rw [triangularAdaptiveFloor, ite_eq_right h] at hsq
      exact hsq
  margin := by
    have h0 : 0 < L := by linarith only [hL]
    have hb := triangularAdaptive_root_budget hL
    have hm := mul_le_mul_of_nonneg_right hb h0.le
    have he :
      (triangularAdaptiveA L + triangularAdaptiveD L / triangularAdaptiveRadius L) * L =
        (36 + (1456 + 13 / 10000000) / Real.sqrt L) * L + 165102 +
          (4000000000000 * (1001 / 1000) : ℝ) /
            (triangularAdaptiveRadius L * triangularEighthRoot L) := by
      dsimp only [triangularAdaptiveA, triangularAdaptiveD]
      have hcost :
        ((4000000000000 * (1001 / 1000) : ℝ) / (triangularEighthRoot L * L) /
              triangularAdaptiveRadius L) *
            L =
          (4000000000000 * (1001 / 1000) : ℝ) /
            (triangularAdaptiveRadius L * triangularEighthRoot L) := by
        rw [div_div,
          show
            triangularEighthRoot L * L * triangularAdaptiveRadius L =
              (triangularAdaptiveRadius L * triangularEighthRoot L) * L
            by ring,
          div_mul_eq_div_div, div_mul_cancel₀ _ h0.ne']
      have hconst : (165102 : ℝ) / L * L = 165102 := div_mul_cancel₀ _ h0.ne'
      nlinarith only [hcost, hconst]
    rw [he] at hm
    have hcost :
      ((165000 +
              (4000000000000 * (1001 / 1000) : ℝ) /
                (triangularAdaptiveRadius L * triangularEighthRoot L)) /
            L) *
          L =
        165000 +
          (4000000000000 * (1001 / 1000) : ℝ) /
            (triangularAdaptiveRadius L * triangularEighthRoot L) :=
      div_mul_cancel₀ _ h0.ne'
    nlinarith only [hm, hcost]

end PseudoPrime.PrimeTestBounds.MillerRabin
