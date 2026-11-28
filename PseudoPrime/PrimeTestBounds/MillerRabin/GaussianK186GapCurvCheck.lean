/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapCurvLocal

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapCurvLocal
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186FiniteGap
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapExp

/-! # Scalar curvature comparisons for a normalized K186 cell -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Clip the negative of the lower sum to a nonnegative cost. -/
private def curvPositive (q : ℤ) : Analysis.IntegerInterval :=
  ⟨max 0 (-q), max 0 (-q)⟩

/-- Interpret the clipped integer cost as its real scaled value. -/
private theorem curv_positive_contains (q : ℤ) :
    (curvPositive q).Contains k186GapExpScale (max 0 (-(q : ℝ) / k186GapExpScale)) := by
  have h : (0 : ℝ) ≤ k186GapExpScale := by
    exact (show (0 : ℝ) < k186GapExpScale from Int.cast_pos.mpr (by decide +kernel)).le
  have he : ((max 0 (-q) : ℤ) : ℝ) / k186GapExpScale = max 0 (-(q : ℝ) / k186GapExpScale) := by
    simp only [Int.cast_max, Int.cast_neg, Int.cast_zero, ← max_div_div_right h, zero_div]
  exact ⟨he.le, he.ge⟩

/-- Compute the curvature cap from two signed polynomial bounds and the slope. -/
def k186CurvCapAt (a b : ℕ) : Analysis.IntegerInterval :=
  let w := (b : ℤ) - (a : ℤ)
  let s := (k186GapExp (2 * b)).scaleRatio 7827514344543 20786976620000000000000
  let f :=
    Analysis.roundedProduct k186GapExpScale (k186GapExpNeg (9 * a))
      (curvPositive (k186CurvNineLower a w))
  let g :=
    Analysis.roundedProduct k186GapExpScale (k186GapExpNeg (11 * a))
      (curvPositive (k186CurvElevenLower a w))
  (s.add f).add g

/-- A single rational comparison checks the upper curvature throughout
the closed dyadic interval. -/
theorem k186_curv_le_of_compare {a b : ℕ} (hab : a < b) (h₁ : 0 < (k186GapExp (9 * a)).lower)
    (h₂ : 0 < (k186GapExp (11 * a)).lower) {C : ℚ}
    (hc : ((k186CurvCapAt a b).upper : ℚ) / k186GapExpScale ≤ C) {x : ℝ}
    (hx : x ∈ Set.Icc ((a : ℝ) / 32) ((b : ℝ) / 32)) :
    gaussianMidResidualCurv k186GapSlope (4 * (301 / 20000 + 1 / 6000)) k186GapRates k186GapProfiles
        x ≤
      (C : ℝ) := by
  let w : ℤ := (b : ℤ) - (a : ℤ)
  have hw : 0 < w := sub_pos.mpr (Int.ofNat_lt.mpr hab)
  have hd : (a : ℤ) + w = (b : ℤ) := by
    dsimp only [w]; ring
  have hh :=
    k186_curv_bounds_of_ticks (a := (a : ℤ)) hw
      (show x ∈ Set.Icc (((a : ℤ) : ℝ) / 32) (((a : ℤ) + w : ℤ) / (32 : ℝ)) by
        simpa only [hd, Int.cast_natCast] using hx)
  have hG : 0 < k186GapExpScale := by decide +kernel
  have h9 :=
    Analysis.roundedProduct_contains hG (k186_gap_exp_neg_contains (9 * a) h₁)
      (curv_positive_contains (k186CurvNineLower a w))
  have h11 :=
    Analysis.roundedProduct_contains hG (k186_gap_exp_neg_contains (11 * a) h₂)
      (curv_positive_contains (k186CurvElevenLower a w))
  have hs :=
    Analysis.IntegerInterval.scaleRatio_contains (p := 7827514344543) (d := 20786976620000000000000)
      hG (by decide) (k186_gap_exp_contains (2 * b))
  have h := Analysis.IntegerInterval.add_contains (Analysis.IntegerInterval.add_contains hs h9) h11
  change (k186CurvCapAt a b).Contains k186GapExpScale _ at h
  have hbound := (Rat.cast_le (K := ℝ)).mpr hc
  simp only [Rat.cast_div, Rat.cast_intCast] at hbound
  refine (k186_gap_curv_le_of_polys hx hh.1 hh.2).trans ?_
  refine (show _ ≤ ((k186CurvCapAt a b).upper : ℝ) / k186GapExpScale from ?_).trans hbound
  convert h.2 using 1
  norm_num only [k186GapSlope, gaussianK186FarScale, Nat.cast_mul, Nat.cast_ofNat, Int.cast_ofNat,
    neg_div]
  ring_nf

end PseudoPrime.PrimeTestBounds.MillerRabin
