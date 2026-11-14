/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadPhaseInterpolation
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadDistance100

/-! # Phase interpolation at height 100 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For 29 nonnegative ordinates in the certified upper brackets, endpoint
phase bounds B extend across an interval of width at most 1/250 with error
3611/500000. This uses the rational curvature bound from the brackets. -/
theorem phase100_le_of_grid_endpoints (g : Fin 29 → ℝ) (hpos : ∀ i, 0 ≤ g i)
    (hu : LowZero100UpperBounds g) {a b v B : ℝ} (hab : a < b) (hw : b - a ≤ 1 / 250)
    (ha : |zeroHeadPhase g a| ≤ B) (hb : |zeroHeadPhase g b| ≤ B) (hv : v ∈ Set.Icc a b) :
    |zeroHeadPhase g v| ≤ B + 3611 / 500000 := by
  have h :=
    phase_le_of_endpoint_bounds g hab (show (0 : ℝ) ≤ 3611 by norm_num only)
      (lowZero100_phase_curvature g hpos hu).le ha hb hv
  have hs := pow_le_pow_left₀ (sub_nonneg.mpr hab.le) hw 2
  nlinarith only [h, hs]

/-- Uniform endpoint bounds on the grid with step 1/250 give a bound on the
whole closed interval, with interpolation error 3611/500000. The endpoint
is handled directly and all other points lie in a cell selected by a floor. -/
theorem phase100_le_of_grid (g : Fin 29 → ℝ) (hpos : ∀ i, 0 ≤ g i) (hu : LowZero100UpperBounds g)
    {a v B : ℝ} {N : ℕ} (hv : v ∈ Set.Icc a (a + (N : ℝ) / 250))
    (hnodes : ∀ j : ℕ, j ≤ N → |zeroHeadPhase g (a + (j : ℝ) / 250)| ≤ B) :
    |zeroHeadPhase g v| ≤ B + 3611 / 500000 := by
  by_cases he : v = a + (N : ℝ) / 250
  · rw [he]
    have h := hnodes N le_rfl
    linarith only [h]
  · have hl : v < a + (N : ℝ) / 250 := lt_of_le_of_ne hv.2 he
    have hn : 0 ≤ 250 * (v - a) := mul_nonneg (by norm_num only) (sub_nonneg.mpr hv.1)
    have hj : Nat.floor (250 * (v - a)) < N := by
      apply (Nat.floor_lt hn).mpr
      linarith only [hl]
    let j := Nat.floor (250 * (v - a))
    have hju : j + 1 ≤ N := Nat.succ_le_iff.mpr hj
    have hcell : v ∈ Set.Icc (a + (j : ℝ) / 250) (a + ((j + 1 : ℕ) : ℝ) / 250) := by
      have hlo := Nat.floor_le hn
      have hhi := Nat.lt_floor_add_one (250 * (v - a))
      constructor
      · linarith only [hlo]
      · rw [Nat.cast_add, Nat.cast_one]
        linarith only [hhi]
    have hab : a + (j : ℝ) / 250 < a + ((j + 1 : ℕ) : ℝ) / 250 := by
      rw [Nat.cast_add, Nat.cast_one]
      linarith only
    have hw : (a + ((j + 1 : ℕ) : ℝ) / 250) - (a + (j : ℝ) / 250) ≤ 1 / 250 := by
      rw [Nat.cast_add, Nat.cast_one]
      exact le_of_eq (by ring)
    exact phase100_le_of_grid_endpoints g hpos hu hab hw (hnodes j hj.le) (hnodes (j + 1) hju) hcell

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
