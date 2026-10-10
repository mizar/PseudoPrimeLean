/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Integrability from logarithmic growth and quadratic decay

A quarter-power bound on the logarithm gives an integrable Japanese-bracket majorant.
Products of logarithmically growing and quadratically decaying complex functions
are therefore integrable under the stated measurability and pointwise bounds.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For every real `t`, the logarithmic inverse-square weight is bounded by a constant
times `(1+t²)^(-3/4)`. Bound the logarithm by a quarter power and compare its argument
with `5(1+t²)`. This provides the integrable majorant for vertical contour estimates. -/
theorem log_add_abs_div_one_add_sq_le (t : ℝ) :
    (Real.log (4 + |t|) + 1) / (1 + t ^ 2) ≤
      (4 * (5 : ℝ) ^ (1 / 4 : ℝ) + 1) * (1 + t ^ 2) ^ (-3 / 4 : ℝ) := by
  let B := 1 + t ^ 2
  have hB : 0 < B := by
    dsimp only [B]; positivity
  have hB1 : 1 ≤ B := by
    dsimp only [B]; linarith only [sq_nonneg t]
  have ha : |t| ≤ B := by
    have h := sq_nonneg (|t| - 1 / 2)
    dsimp only [B]
    nlinarith only [h, sq_abs t]
  have hbase : 4 + |t| ≤ 5 * B := by linarith only [ha, hB1]
  have hl :=
    Real.log_le_rpow_div (show 0 ≤ 4 + |t| by positivity) (by norm_num only : (0 : ℝ) < 1 / 4)
  have hp :=
    Real.rpow_le_rpow (show 0 ≤ 4 + |t| by positivity) hbase (by norm_num only : (0 : ℝ) ≤ 1 / 4)
  rw [Real.mul_rpow (by norm_num only : (0 : ℝ) ≤ 5) hB.le] at hp
  have hone : 1 ≤ B ^ (1 / 4 : ℝ) := Real.one_le_rpow hB1 (by norm_num only)
  have hnum : Real.log (4 + |t|) + 1 ≤ (4 * (5 : ℝ) ^ (1 / 4 : ℝ) + 1) * B ^ (1 / 4 : ℝ) := by
    nlinarith only [hl, hp, hone]
  have h := div_le_div_of_nonneg_right hnum hB.le
  have he : B ^ (1 / 4 : ℝ) / B = B ^ (-3 / 4 : ℝ) := by
    calc
      _ = B ^ (1 / 4 : ℝ) / B ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = B ^ ((1 / 4 : ℝ) - 1) := (Real.rpow_sub hB _ _).symm
      _ = _ := by norm_num only
  change (Real.log (4 + |t|) + 1) / B ≤ _ at h ⊢
  rw [mul_div_assoc, he] at h
  exact h

/-- The real logarithmic inverse-square weight is absolutely integrable on the whole line.
Its continuity gives measurability and the preceding quarter-power estimate gives an
integrable Japanese-bracket majorant. This controls products of growth and decay factors. -/
theorem integrable_log_add_abs_div_one_add_sq :
    MeasureTheory.Integrable (fun t : ℝ => (Real.log (4 + |t|) + 1) / (1 + t ^ 2)) := by
  have hi : MeasureTheory.Integrable (fun t : ℝ => (1 + t ^ 2) ^ (-3 / 4 : ℝ)) := by
    have h :=
      integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := MeasureTheory.volume) (r := (3 / 2 : ℝ))
        (by norm_num only [Module.finrank_self, Nat.cast_one])
    simpa only [Real.norm_eq_abs, sq_abs, neg_div, div_div,
      show (2 : ℝ) * 2 = 4 by norm_num only] using h
  have hc : Continuous (fun t : ℝ => (Real.log (4 + |t|) + 1) / (1 + t ^ 2)) := by
    have hp : Continuous (fun t : ℝ => 4 + |t|) := continuous_const.add continuous_abs
    exact
      (hp.log (fun t => by positivity)).add continuous_const |>.div
        (continuous_const.add (continuous_id.pow 2)) (fun t => by positivity)
  apply (hi.const_mul (4 * (5 : ℝ) ^ (1 / 4 : ℝ) + 1)).mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs,
    abs_of_nonneg
      (div_nonneg (add_nonneg (Real.log_nonneg (by linarith only [abs_nonneg t])) zero_le_one)
        (by positivity))]
  exact log_add_abs_div_one_add_sq_le t

/-- For two almost-everywhere strongly measurable complex functions, a logarithmic bound
on the first and an inverse-square bound on the second imply integrability of their product.
Multiply the pointwise bounds and compare with the logarithmic inverse-square majorant.
The constants need no separate sign hypotheses because the upper bounds dominate norms.
This is used for gamma-weighted Mellin integrals. -/
theorem integrable_mul_of_log_and_inverseSquare {f g : ℝ → ℂ} {A B : ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f) (hg : MeasureTheory.AEStronglyMeasurable g)
    (hfb : ∀ t : ℝ, ‖f t‖ ≤ A * (Real.log (4 + |t|) + 1)) (hgb : ∀ t : ℝ, ‖g t‖ ≤ B / (1 + t ^ 2)) :
    MeasureTheory.Integrable (fun t => f t * g t) := by
  apply (integrable_log_add_abs_div_one_add_sq.const_mul (A * B)).mono' (hf.mul hg)
  apply Filter.Eventually.of_forall
  intro t
  simp only [Pi.mul_apply, norm_mul]
  calc
    _ ≤ (A * (Real.log (4 + |t|) + 1)) * (B / (1 + t ^ 2)) :=
      mul_le_mul (hfb t) (hgb t) (norm_nonneg _) ((norm_nonneg _).trans (hfb t))
    _ = _ := by ring

end PseudoPrime.Analysis
