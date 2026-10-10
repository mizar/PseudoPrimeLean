/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Integrability of absolutely integrable complex series
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For a countable family of integrable functions from ℝ to ℂ, summability of their
integrated norms implies integrability of their pointwise `tsum`. Measurability is preserved
by countable sums; Tonelli's theorem and the bound by the sum of norms give finite integral.
This supplies integrability of the pole-series sums used in vertical Mellin integrals. -/
theorem integrable_tsum_of_summable_integral_norm {ι : Type*} [Countable ι] (F : ι → ℝ → ℂ)
    (hf : ∀ i, MeasureTheory.Integrable (F i)) (hs : Summable (fun i ↦ ∫ y : ℝ, ‖F i y‖)) :
    MeasureTheory.Integrable (fun y : ℝ ↦ ∑' i, F i y) := by
  refine ⟨MeasureTheory.AEStronglyMeasurable.tsum (fun i ↦ (hf i).aestronglyMeasurable), ?_⟩
  have he (i : ι) : (∫⁻ y : ℝ, ‖F i y‖ₑ) = ‖∫ y : ℝ, ‖F i y‖‖ₑ := by
    dsimp only [enorm]
    rw [MeasureTheory.lintegral_coe_eq_integral _ (hf i).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (MeasureTheory.integral_nonneg (fun _ ↦ norm_nonneg _))]
    simp only [coe_nnnorm]
  apply lt_of_le_of_lt (MeasureTheory.lintegral_mono (fun y ↦ enorm_tsum_le_tsum_enorm))
  rw [MeasureTheory.lintegral_tsum (fun i ↦ (hf i).aestronglyMeasurable.enorm)]
  rw [funext he]
  exact
    lt_top_iff_ne_top.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mpr (NNReal.summable_coe.mp hs.abs))

end PseudoPrime.Analysis
