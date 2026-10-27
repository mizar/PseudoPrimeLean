/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Integrability of absolutely summable complex series in mean -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For countably many integrable complex functions with summable integral norms,
their pointwise series is integrable. Use measurable summation and bound the norm
lintegral by the sum of norm lintegrals. This supplies convergence for Gamma-series
integral decompositions without a separate integrability premise. -/
theorem integrable_complex_tsum_of_summable_integral_norm {F : ℕ → ℝ → ℂ}
    (hi : ∀ n, MeasureTheory.Integrable (F n)) (hs : Summable (fun n ↦ ∫ t : ℝ, ‖F n t‖)) :
    MeasureTheory.Integrable (fun t : ℝ ↦ ∑' n : ℕ, F n t) := by
  refine ⟨MeasureTheory.AEStronglyMeasurable.tsum (fun n ↦ (hi n).aestronglyMeasurable), ?_⟩
  apply MeasureTheory.hasFiniteIntegral_iff_enorm.mpr
  have he (n : ℕ) : (∫⁻ t : ℝ, ‖F n t‖ₑ) = ‖∫ t : ℝ, ‖F n t‖‖ₑ := by
    dsimp only [enorm]
    rw [MeasureTheory.lintegral_coe_eq_integral _ (hi n).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (MeasureTheory.integral_nonneg (fun t ↦ norm_nonneg (F n t)))]
    simp only [coe_nnnorm]
  calc
    (∫⁻ t : ℝ, ‖∑' n : ℕ, F n t‖ₑ) ≤ ∫⁻ t : ℝ, ∑' n : ℕ, ‖F n t‖ₑ :=
      MeasureTheory.lintegral_mono (fun t ↦ enorm_tsum_le_tsum_enorm)
    _ = ∑' n : ℕ, ∫⁻ t : ℝ, ‖F n t‖ₑ :=
      MeasureTheory.lintegral_tsum (fun n ↦ (hi n).aestronglyMeasurable.enorm)
    _ < ⊤ := by
      simp only [he]
      apply lt_top_iff_ne_top.mpr
      exact ENNReal.tsum_coe_ne_top_iff_summable.mpr (NNReal.summable_coe.mp hs.abs)

end PseudoPrime.AnalyticNumberTheory.General
