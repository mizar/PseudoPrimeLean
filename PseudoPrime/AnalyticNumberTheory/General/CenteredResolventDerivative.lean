/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Differentiation of centered pole series

Uniform inverse-square bounds identify the derivative at the center.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For poles at norm at least one half with summable inverse-square multiplicity mass,
the centered resolvent series is differentiable throughout the radius-one-quarter ball.
Its derivative is the sum of the negative translated inverse-square terms. Uniform pole
separation bounds all term derivatives by four times the summable mass; the base series
vanishes at zero. This local identity permits repeated differentiation of zero expansions. -/
theorem hasDerivAt_centeredResolventSum_of_mem_ball {ι : Type*} (α : ι → ℂ) (m : ι → ℕ)
    (hα : ∀ i, (1 / 2 : ℝ) ≤ ‖α i‖) (hm : Summable (fun i ↦ (m i : ℝ) / ‖α i‖ ^ 2)) {z : ℂ}
    (hz : z ∈ Metric.ball 0 (1 / 4)) :
    HasDerivAt (fun z : ℂ ↦ ∑' i, (m i : ℂ) * (1 / (z - α i) + 1 / α i))
      (∑' i, -(m i : ℂ) / (z - α i) ^ 2) z := by
  let U : Set ℂ := Metric.ball 0 (1 / 4)
  have h0 : (0 : ℂ) ∈ U := by
    rw [Metric.mem_ball, dist_self]
    norm_num only
  have hdist : ∀ i, ∀ z ∈ U, ‖α i‖ / 2 ≤ ‖z - α i‖ := by
    intro i z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    have ht := norm_sub_le z (z - α i)
    rw [sub_sub_cancel] at ht
    have hi := hα i
    linarith only [ht, hz, hi]
  have hne : ∀ i, ∀ z ∈ U, z - α i ≠ 0 := by
    intro i z hz
    apply norm_pos_iff.mp
    have hi := hα i
    have hd := hdist i z hz
    linarith only [hi, hd]
  have hg :
    ∀ i,
      ∀ z ∈ U,
        HasDerivAt (fun w : ℂ ↦ (m i : ℂ) * (1 / (w - α i) + 1 / α i)) (-(m i : ℂ) / (z - α i) ^ 2)
          z := by
    intro i z hz
    have h := (((hasDerivAt_id z).sub_const (α i)).inv (hne i z hz)).add_const (1 / α i)
    have hh := h.const_mul (m i : ℂ)
    convert hh using 1
    · simp only [one_div, Pi.inv_apply, id_eq]
    · dsimp only [id_eq]
      ring
  have hb : ∀ i, ∀ z ∈ U, ‖-(m i : ℂ) / (z - α i) ^ 2‖ ≤ 4 * ((m i : ℝ) / ‖α i‖ ^ 2) := by
    intro i z hz
    rw [norm_div, norm_neg, Complex.norm_natCast, norm_pow]
    have hi : 0 < ‖α i‖ := by linarith only [hα i]
    have hd : 0 < ‖z - α i‖ := norm_pos_iff.mpr (hne i z hz)
    rw [← mul_div_assoc, div_le_div_iff₀ (sq_pos_of_pos hd) (sq_pos_of_pos hi)]
    have hs : ‖α i‖ ^ 2 ≤ 4 * ‖z - α i‖ ^ 2 := by
      have hh := hdist i z hz
      have hs := mul_le_mul hh hh (div_nonneg (norm_nonneg _) zero_le_two) (norm_nonneg _)
      nlinarith only [hs]
    have h := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (m i))
    nlinarith only [h]
  have hbase : Summable (fun i ↦ (m i : ℂ) * (1 / ((0 : ℂ) - α i) + 1 / α i)) := by
    simp only [zero_sub, one_div, inv_neg, neg_add_cancel, mul_zero]
    exact summable_zero
  have hh :=
    hasDerivAt_tsum_of_isPreconnected (hm.mul_left 4) Metric.isOpen_ball
      (convex_ball (0 : ℂ) (1 / 4)).isPreconnected hg hb h0 hbase hz
  exact hh

/-- For poles at norm at least one half with summable inverse-square multiplicity mass,
the centered resolvent series has derivative -sum m/alpha^2 at zero.
Specialize the local ball identity at zero and simplify the squared negative pole.
This center value is used by the completed logarithmic-derivative and Mellin formulas. -/
theorem hasDerivAt_centeredResolventSum_zero {ι : Type*} (α : ι → ℂ) (m : ι → ℕ)
    (hα : ∀ i, (1 / 2 : ℝ) ≤ ‖α i‖) (hm : Summable (fun i ↦ (m i : ℝ) / ‖α i‖ ^ 2)) :
    HasDerivAt (fun z : ℂ ↦ ∑' i, (m i : ℂ) * (1 / (z - α i) + 1 / α i))
      (∑' i, -(m i : ℂ) / (α i) ^ 2) 0 := by
  have hz : (0 : ℂ) ∈ Metric.ball 0 (1 / 4) := by
    rw [Metric.mem_ball, dist_self]
    norm_num only
  simpa only [zero_sub, neg_sq] using hasDerivAt_centeredResolventSum_of_mem_ball α m hα hm hz

end PseudoPrime.AnalyticNumberTheory.General
