/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.AdaptiveReciprocalRadius

/-! # Monotonicity of the adaptive local witness radius -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The finer Part 2 radius is nondecreasing on `[7, ∞)`. A tangent bound for
the logarithm limits its increase to less than the increase of the level.
This is the inner monotonicity needed for the adaptive local radius. -/
theorem finer_local_radius_mono {x y : ℝ} (hx : 7 ≤ x) (hxy : x ≤ y) :
    Analysis.finerPart2CutoffRoot x ≤ Analysis.finerPart2CutoffRoot y := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 7) hx
  have hypos : 0 < y := hxpos.trans_le hxy
  have ht := Analysis.log_le_log_add_sub_div hxpos hypos
  have hd : (y - x) / x ≤ (y - x) / 7 :=
    div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) (by norm_num only) hx
  dsimp only [Analysis.finerPart2CutoffRoot]
  linarith only [ht, hd, hxy]

/-- The adaptive correction applied to a finer radius is nondecreasing on
`[7, ∞)`. Bound the inverse difference by the level increment and compare
inverse squares; the positive linear term dominates the possible decrease.
This transfers the local adaptive bound to an upper logarithmic scale. -/
theorem adaptive_bridge_mono {x y : ℝ} (hx : 7 ≤ x) (hxy : x ≤ y) :
    x - 31551 / 10000 + 2 * Analysis.reciprocalLossBridge x ≤
      y - 31551 / 10000 + 2 * Analysis.reciprocalLossBridge y := by
  have hx1 : 0 < x - 1 := by linarith only [hx]
  have hy1 : 0 < y - 1 := by linarith only [hx, hxy]
  have hdiff : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hprod : (36 : ℝ) ≤ (x - 1) * (y - 1) := by
    nlinarith only [hx, hxy, mul_nonneg (sub_nonneg.mpr hx) hdiff]
  have hfrac : (y - x) / ((x - 1) * (y - 1)) ≤ (y - x) / 36 :=
    div_le_div_of_nonneg_left hdiff (by norm_num only) hprod
  have heq : 1 / (x - 1) - 1 / (y - 1) = (y - x) / ((x - 1) * (y - 1)) := by
    rw [div_sub_div 1 1 (ne_of_gt hx1) (ne_of_gt hy1)]
    congr 1
    ring
  have hinv : 1 / (x - 1) - 1 / (y - 1) ≤ (y - x) / 36 := heq ▸ hfrac
  have hx0 : 0 < x := by linarith only [hx]
  have hsq : x ^ 2 ≤ y ^ 2 := (sq_le_sq₀ hx0.le (hx0.le.trans hxy)).mpr hxy
  have hsqi : 1 / y ^ 2 ≤ 1 / x ^ 2 := one_div_le_one_div_of_le (sq_pos_of_pos hx0) hsq
  dsimp only [Analysis.reciprocalLossBridge]
  simp only [div_eq_mul_inv, one_mul] at hinv hsqi ⊢
  linarith only [hinv, hsqi, hxy]

/-- The adaptive Part 2 radius is nondecreasing from logarithmic scale seven.
The finer radius is at least seven there, so its monotonicity composes with the
monotonicity of the adaptive correction. This permits replacing a local level
by a larger common scale in witness bounds. -/
theorem adaptive_local_radius_mono {x y : ℝ} (hx : 7 ≤ x) (hxy : x ≤ y) :
    Analysis.adaptivePart2CutoffRoot x ≤ Analysis.adaptivePart2CutoffRoot y := by
  have hf : 7 ≤ Analysis.finerPart2CutoffRoot x :=
    le_trans (by norm_num only)
      (Analysis.finerPart2Root_ge_36_5_of_639_100_le (by linarith only [hx]))
  exact adaptive_bridge_mono hf (finer_local_radius_mono hx hxy)

end PseudoPrime.PrimeTestBounds.MillerRabin
