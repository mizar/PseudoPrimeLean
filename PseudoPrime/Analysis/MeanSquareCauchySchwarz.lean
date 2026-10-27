/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import PseudoPrime.Analysis.FiniteExponentialMeanSquare

/-!
# Cauchy--Schwarz for complex mean-square integrals

General measure and finite-interval forms, with the actual L2 hypotheses supplied
from continuity on compact intervals.
-/

@[expose] public section

namespace PseudoPrime.Analysis.ExponentialMeanSquare

/-- For two L2 complex functions on any measure space, the integral of their product is
bounded by the product of their L2 norms. Use the integral norm inequality and Holder. -/
theorem norm_integral_mul_le_sqrt {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (f g : α → ℂ) (hf : MeasureTheory.MemLp f 2 μ) (hg : MeasureTheory.MemLp g 2 μ) :
    ‖∫ v, f v * g v ∂μ‖ ≤ Real.sqrt (∫ v, ‖f v‖ ^ 2 ∂μ) * Real.sqrt (∫ v, ‖g v‖ ^ 2 ∂μ) := by
  have hf' : MeasureTheory.MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa only [ENNReal.ofReal_ofNat] using hf
  have hg' : MeasureTheory.MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa only [ENNReal.ofReal_ofNat] using hg
  have h := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hf' hg'
  have hn := MeasureTheory.norm_integral_le_integral_norm (fun v ↦ f v * g v) (μ := μ)
  simp only [norm_mul] at hn
  exact hn.trans (by simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using h)

/-- For two L2 complex functions, the squared norm of the product integral is bounded
by the two mean squares. Square the nonnegative Holder bound and evaluate both square roots. -/
theorem norm_integral_mul_sq_le {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (f g : α → ℂ) (hf : MeasureTheory.MemLp f 2 μ) (hg : MeasureTheory.MemLp g 2 μ) :
    ‖∫ v, f v * g v ∂μ‖ ^ 2 ≤ (∫ v, ‖f v‖ ^ 2 ∂μ) * (∫ v, ‖g v‖ ^ 2 ∂μ) := by
  have hi : 0 ≤ ∫ v, ‖f v‖ ^ 2 ∂μ := MeasureTheory.integral_nonneg (fun v ↦ sq_nonneg ‖f v‖)
  have hj : 0 ≤ ∫ v, ‖g v‖ ^ 2 ∂μ := MeasureTheory.integral_nonneg (fun v ↦ sq_nonneg ‖g v‖)
  have h :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr
      (norm_integral_mul_le_sqrt μ f g hf hg)
  simpa only [mul_pow, Real.sq_sqrt hi, Real.sq_sqrt hj] using h

/-- A complex function continuous on a compact real interval belongs to L2 on its Ioc restriction.
Integrate its continuous norm square and restrict from Icc to Ioc. -/
theorem memLp_two_Ioc {a b : ℝ} {f : ℝ → ℂ} (hf : ContinuousOn f (Set.Icc a b)) :
    MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioc a b)) := by
  have hm :=
    (hf.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable (μ := MeasureTheory.volume)
      measurableSet_Ioc
  apply (MeasureTheory.memLp_two_iff_integrable_sq_norm hm).mpr
  exact (hf.norm.pow 2).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

/-- For ordered endpoints and two continuous functions on the closed interval, Cauchy--Schwarz
bounds the complex product integral by their mean squares. Supply actual compact L2 membership. -/
theorem norm_intervalIntegral_mul_sq_le {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℂ}
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b)) :
    ‖∫ v : ℝ in a..b, f v * g v‖ ^ 2 ≤
      (∫ v : ℝ in a..b, ‖f v‖ ^ 2) * (∫ v : ℝ in a..b, ‖g v‖ ^ 2) := by
  simp only [intervalIntegral.integral_of_le hab]
  exact norm_integral_mul_sq_le _ _ _ (memLp_two_Ioc hf) (memLp_two_Ioc hg)

end PseudoPrime.Analysis.ExponentialMeanSquare
