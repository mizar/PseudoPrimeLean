/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianTriangularRadius
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularCoreBounds

/-! # Gaussian cutoff with triangular local and large-index budgets -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The Gaussian cutoff radius at scale `L`; its square is the adaptive Gaussian coefficient. -/
noncomputable def gaussianTriangularRadius (L : ℝ) : ℝ :=
  Real.sqrt ((21 / 10) * adaptiveGaussianA L ^ 2)

/-- Above two trillion the Gaussian radius satisfies the triangular local bounds. -/
theorem gaussianTriangular_bounds {L : ℝ} (hL : 2000000000000 ≤ L) :
    (5313 / 10000 : ℝ) < gaussianTriangularRadius L ∧ gaussianTriangularRadius L ≤ 1 := by
  constructor
  · exact gaussianTriangular_radius_gt L hL
  · apply Real.sqrt_le_one.mpr
    have ha := adaptiveGaussianA_lower L hL
    have hb := adaptiveGaussianA_upper L hL
    have hs := pow_le_pow_left₀ (show 0 ≤ adaptiveGaussianA L by linarith only [ha]) hb 2
    nlinarith only [hs]

/-- The Gaussian radius satisfies the triangular quadratic budget above two trillion. -/
theorem gaussianTriangular_root_budget {L : ℝ} (hL : 2000000000000 ≤ L) :
    triangularAdaptiveA L + triangularAdaptiveD L / gaussianTriangularRadius L ≤
      (68 - 3 / 10000) * gaussianTriangularRadius L := by
  have h30 : (30000000000 : ℝ) ≤ L := by linarith only [hL]
  have hb := triangularAdaptive_budget h30
  have hr := triangularPositiveRoot_spec (K := 68 - 3 / 10000) (by norm_num only) hb.1 hb.2.1
  have ha := (gaussianTriangular_bounds hL).1
  have hs := gaussianTriangular_root_le hL
  have hp : 0 < gaussianTriangularRadius L := by linarith only [ha]
  exact triangular_root_budget (by norm_num only) hb.2.1 hr.1 hr.2 (by linarith only [ha, hs]) hp

/-- The eighth-root floor satisfies the triangular sixteenth-power bound. -/
theorem gaussianTriangular_root16 {L : ℝ} (hL : 2000000000000 ≤ L) :
    0 < triangularEighthRoot L ∧
      (triangularEighthRoot L) ^ 16 ≤ (gaussianTriangularRadius L) ^ 2 * L ^ 2 := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hm := triangularEighthRoot_pow hL0
  have hm0 : 0 < triangularEighthRoot L := by
    have hh := triangularEighthRoot_ge_18 (show 30000000000 ≤ L by linarith only [hL])
    linarith only [hh]
  have ha := (gaussianTriangular_bounds hL).1
  have hasq : (5313 / 10000 : ℝ) ^ 2 ≤ (gaussianTriangularRadius L) ^ 2 :=
    pow_le_pow_left₀ (by norm_num only) ha.le 2
  have hmul := mul_le_mul_of_nonneg_right hasq (sq_nonneg L)
  have he : (triangularEighthRoot L) ^ 16 = (5313 / 10000 : ℝ) ^ 2 * L ^ 2 := by
    calc
      _ = ((triangularEighthRoot L) ^ 8) ^ 2 := by ring
      _ = ((5313 / 10000 : ℝ) * L) ^ 2 := by rw [hm.2]
      _ = _ := by ring
  exact ⟨hm0, he.le.trans hmul⟩

/-- The Gaussian radius and triangular error budgets form a core at each eligible scale. -/
noncomputable def gaussianTriangularCore (L : ℝ) (hL : 2000000000000 ≤ L) : TriangularCore where
  C := (gaussianTriangularRadius L) ^ 2
  T := L
  a := gaussianTriangularRadius L
  m := triangularEighthRoot L
  v := Real.sqrt L
  b :=
    (165000 +
        (4000000000000 * (1001 / 1000) : ℝ) /
          (gaussianTriangularRadius L * triangularEighthRoot L)) /
      L
  entry := by linarith only [hL]
  root := by
    have ha := (gaussianTriangular_bounds hL).1
    linarith only [ha]
  localBudget := by
    have ha := (gaussianTriangular_bounds hL).1
    have hp := mul_le_mul_of_nonneg_right ha.le (by linarith only [hL])
    nlinarith only [hp, hL]
  square := le_rfl
  upper := by
    have ha := gaussianTriangular_bounds hL
    have h0 : 0 ≤ gaussianTriangularRadius L := by linarith only [ha.1]
    have hs := pow_le_pow_left₀ h0 ha.2 2
    norm_num only [one_pow] at hs
    exact hs
  root16 := gaussianTriangular_root16 hL
  fourth := by
    have h0 : 0 < L := by linarith only [hL]
    exact ⟨Real.sqrt_pos.mpr h0, (Real.sq_sqrt h0.le).le⟩
  cost := by
    have h0 : L ≠ 0 := (show 0 < L by linarith only [hL]).ne'
    rw [div_mul_cancel₀ _ h0]
  margin := by
    have h0 : 0 < L := by linarith only [hL]
    have hb := gaussianTriangular_root_budget hL
    have hm := mul_le_mul_of_nonneg_right hb h0.le
    have he :
      (triangularAdaptiveA L + triangularAdaptiveD L / gaussianTriangularRadius L) * L =
        (36 + (1456 + 13 / 10000000) / Real.sqrt L) * L + 165102 +
          (4000000000000 * (1001 / 1000) : ℝ) /
            (gaussianTriangularRadius L * triangularEighthRoot L) := by
      dsimp only [triangularAdaptiveA, triangularAdaptiveD]
      have hcost :
        ((4000000000000 * (1001 / 1000) : ℝ) / (triangularEighthRoot L * L) /
              gaussianTriangularRadius L) *
            L =
          (4000000000000 * (1001 / 1000) : ℝ) /
            (gaussianTriangularRadius L * triangularEighthRoot L) := by
        rw [div_div,
          show
            triangularEighthRoot L * L * gaussianTriangularRadius L =
              (gaussianTriangularRadius L * triangularEighthRoot L) * L
            by ring,
          div_mul_eq_div_div, div_mul_cancel₀ _ h0.ne']
      have hconst : (165102 : ℝ) / L * L = 165102 := div_mul_cancel₀ _ h0.ne'
      nlinarith only [hcost, hconst]
    rw [he] at hm
    have hcost :
      ((165000 +
              (4000000000000 * (1001 / 1000) : ℝ) /
                (gaussianTriangularRadius L * triangularEighthRoot L)) /
            L) *
          L =
        165000 +
          (4000000000000 * (1001 / 1000) : ℝ) /
            (gaussianTriangularRadius L * triangularEighthRoot L) :=
      div_mul_cancel₀ _ h0.ne'
    nlinarith only [hm, hcost]

end PseudoPrime.PrimeTestBounds.MillerRabin
