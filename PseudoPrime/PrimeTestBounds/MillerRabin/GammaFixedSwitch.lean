/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaRefinedEnvelope
/-! # Exact Gamma crossing -/
@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The radius corresponding exactly to witness bound 35000 under the scale 99/40.
This positive square root defines the algebraic Gamma switching point. -/
noncomputable def gammaFixedRadius : ℝ := Real.sqrt ((40 / 99 : ℝ) * 35000)

/-- The unique logarithmic scale where the refined Gamma gap vanishes at the fixed
35000 radius. Solve the affine gap equation in L; the certified location is (208,209).
The interval envelope uses this exact real constant rather than a rounded decimal. -/
noncomputable def gammaFixedSwitch : ℝ :=
  ((87069 / 98800 : ℝ) * gammaFixedRadius -
    (143420077 / 11856000 - 2 * (413 / 100)) - (190 / 3) / gammaFixedRadius) /
    ((11783423 / 25000000 : ℝ) + (7 / 6) / gammaFixedRadius)

/-- The fixed radius lies strictly between 1189/10 and 119.
Square the nonnegative endpoints to reduce both comparisons to rational arithmetic. -/
theorem gammaFixedRadius_bounds : (1189 / 10 : ℝ) < gammaFixedRadius ∧
    gammaFixedRadius < 119 := by
  constructor
  · exact (Real.lt_sqrt (by norm_num only)).mpr (by norm_num only)
  · exact (Real.sqrt_lt (by norm_num only) (by norm_num only)).mpr (by norm_num only)

/-- The fixed radius is positive by its rational lower bound.
This permits division in the switching equation. -/
theorem gammaFixedRadius_pos : 0 < gammaFixedRadius := by
  linarith only [gammaFixedRadius_bounds.1]

/-- For L>=120 and positive radii r<s, the prefix gap strictly increases.
The linear term increases strictly and the reciprocal penalty decreases.
This supplies the reverse root comparison at the exact switching point. -/
theorem prefixGap_strictMono {L C r s : ℝ} (hL : 120 ≤ L) (hr : 0 < r) (hrs : r < s) :
    gammaClippedPrefixGap L C r < gammaClippedPrefixGap L C s := by
  have hA : 0 ≤ (7 / 6 : ℝ) * L + 190 / 3 := by linarith only [hL]
  have hdiv := div_le_div_of_nonneg_left hA hr hrs.le
  have hlin := mul_lt_mul_of_pos_left hrs (by norm_num only : (0 : ℝ) < 87069 / 98800)
  dsimp only [gammaClippedPrefixGap]
  linarith only [hdiv, hlin]

/-- The gap at the fixed radius factors as a positive slope times the distance
from L to the switching point. Expand the affine equation and cancel its nonzero slope. -/
theorem gammaFixedSwitch_gap (L : ℝ) :
    gammaClippedPrefixGap L (413 / 100) gammaFixedRadius =
      ((11783423 / 25000000 : ℝ) + (7 / 6) / gammaFixedRadius) * (gammaFixedSwitch - L) := by
  have hD : (11783423 / 25000000 : ℝ) + (7 / 6) / gammaFixedRadius ≠ 0 :=
    ne_of_gt (add_pos (by norm_num only) (div_pos (by norm_num only) gammaFixedRadius_pos))
  rw [gammaFixedSwitch, mul_sub, mul_div_cancel₀ _ hD]
  dsimp only [gammaClippedPrefixGap]
  ring

/-- The switching point lies strictly between 208 and 209.
Strict radius monotonicity and rational gap evaluations at 1189/10 and 119
give opposite signs at the two logarithmic endpoints. -/
theorem gammaFixedSwitch_bounds : (208 : ℝ) < gammaFixedSwitch ∧ gammaFixedSwitch < 209 := by
  have hD : 0 < (11783423 / 25000000 : ℝ) + (7 / 6) / gammaFixedRadius :=
    add_pos (by norm_num only) (div_pos (by norm_num only) gammaFixedRadius_pos)
  have hlo := prefixGap_strictMono (C := (413 / 100 : ℝ))
    (by norm_num only : (120 : ℝ) ≤ 208) (by norm_num only) gammaFixedRadius_bounds.1
  have hhi := prefixGap_strictMono (C := (413 / 100 : ℝ))
    (by norm_num only : (120 : ℝ) ≤ 209) gammaFixedRadius_pos gammaFixedRadius_bounds.2
  have h0 : 0 < gammaClippedPrefixGap 208 (413 / 100) (1189 / 10) := by
    norm_num only [gammaClippedPrefixGap]
  have h1 : gammaClippedPrefixGap 209 (413 / 100) 119 < 0 := by
    norm_num only [gammaClippedPrefixGap]
  rw [gammaFixedSwitch_gap] at hlo hhi
  constructor
  · nlinarith only [hlo, h0, hD]
  · nlinarith only [hhi, h1, hD]

/-- For 120<=L at or below the switching point, the refined Gamma bound is at most
35000. A nonnegative fixed-radius gap bounds the root, and the prefix floor
is smaller than this radius. -/
theorem gammaRefined_le_fixed {L : ℝ} (hL : 120 ≤ L) (hS : L ≤ gammaFixedSwitch) :
    gamma1000RefinedBound L ≤ 35000 := by
  have hgap : 0 ≤ gammaClippedPrefixGap L (413 / 100) gammaFixedRadius := by
    rw [gammaFixedSwitch_gap]
    exact mul_nonneg (add_nonneg (by norm_num only)
      (div_nonneg (by norm_num only) gammaFixedRadius_pos.le)) (sub_nonneg.mpr hS)
  have hroot := gammaClippedPrefixRoot_le_of_gap_nonneg hL (by norm_num only)
    gammaFixedRadius_pos hgap
  have hfloor : Real.sqrt ((40 / 99 : ℝ) * 1000) ≤ gammaFixedRadius :=
    Real.sqrt_le_sqrt (by norm_num only)
  have hradius : gammaClippedPrefixRadius L 1000 (413 / 100) ≤ gammaFixedRadius :=
    max_le hfloor hroot
  have hpos : 0 ≤ gammaClippedPrefixRadius L 1000 (413 / 100) :=
    (Real.sqrt_nonneg _).trans (le_max_left _ _)
  have hsq := (sq_le_sq₀ hpos gammaFixedRadius_pos.le).mpr hradius
  have hR : gammaFixedRadius ^ 2 = (40 / 99 : ℝ) * 35000 :=
    Real.sq_sqrt (by norm_num only)
  change (99 / 40 : ℝ) * gammaClippedPrefixRadius L 1000 (413 / 100) ^ 2 ≤ 35000
  linarith only [hsq, hR]

/-- For L>=120 at or above the switching point, 35000 is at most the refined Gamma
bound. A nonpositive fixed-radius gap and strict radius monotonicity bound
the root from below. This certifies the fixed branch of the interval envelope. -/
theorem fixed_le_gammaRefined {L : ℝ} (hL : 120 ≤ L) (hS : gammaFixedSwitch ≤ L) :
    (35000 : ℝ) ≤ gamma1000RefinedBound L := by
  have hgap : gammaClippedPrefixGap L (413 / 100) gammaFixedRadius ≤ 0 := by
    rw [gammaFixedSwitch_gap]
    exact mul_nonpos_of_nonneg_of_nonpos (add_nonneg (by norm_num only)
      (div_nonneg (by norm_num only) gammaFixedRadius_pos.le)) (sub_nonpos.mpr hS)
  have hroot : gammaFixedRadius ≤ gammaClippedPrefixRoot L (413 / 100) := by
    by_contra h
    have hz := gammaClippedPrefixGap_root_eq_zero hL (by norm_num only :
      0 ≤ 143420077 / 11856000 - 2 * (413 / 100 : ℝ))
    have hm := prefixGap_strictMono (C := (413 / 100 : ℝ)) hL
      (gammaClippedPrefixRoot_pos hL (by norm_num only :
        0 ≤ 143420077 / 11856000 - 2 * (413 / 100 : ℝ))) (lt_of_not_ge h)
    linarith only [hm, hz, hgap]
  have hradius : gammaFixedRadius ≤ gammaClippedPrefixRadius L 1000 (413 / 100) :=
    hroot.trans (le_max_right _ _)
  have hsq := (sq_le_sq₀ gammaFixedRadius_pos.le
    (gammaFixedRadius_pos.le.trans hradius)).mpr hradius
  have hR : gammaFixedRadius ^ 2 = (40 / 99 : ℝ) * 35000 :=
    Real.sq_sqrt (by norm_num only)
  change (35000 : ℝ) ≤ (99 / 40 : ℝ) * gammaClippedPrefixRadius L 1000 (413 / 100) ^ 2
  linarith only [hsq, hR]

/-- At the exact switching point, the refined Gamma bound equals 35000.
The certified lower scale bound makes both one-sided comparisons applicable.
Antisymmetry proves equality without a numerical crossing assumption. -/
theorem gammaRefined_at_switch : gamma1000RefinedBound gammaFixedSwitch = 35000 := by
  have hL : (120 : ℝ) ≤ gammaFixedSwitch := by
    linarith only [gammaFixedSwitch_bounds.1]
  exact le_antisymm (gammaRefined_le_fixed hL le_rfl) (fixed_le_gammaRefined hL le_rfl)

end PseudoPrime.PrimeTestBounds.MillerRabin
