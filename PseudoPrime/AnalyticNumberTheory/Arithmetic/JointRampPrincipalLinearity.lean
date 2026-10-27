/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.JointRampPrincipalErrorBounds

/-! # Linearity of the common ramp-principal error functional -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The common ramp-principal functional commutes with real scalar multiplication.
Move the scalar outside each integral and distribute the signed jumps.
This transports a deterministic correction without putting it in the absolute error. -/
theorem jointRampPrincipalFunctional_const_mul (c : ℝ) (f : ℝ → ℝ) (y : ℝ) :
    jointRampPrincipalFunctional (fun u ↦ c * f u) y = c * jointRampPrincipalFunctional f y := by
  dsimp only [jointRampPrincipalFunctional, exponentialRampVariationFunctional]
  simp only [mul_assoc, intervalIntegral.integral_const_mul]
  ring

/-- For functions continuous on [0,y] with y beyond the ramp, the common functional
is additive. Establish interval integrability on each component, then use integral
linearity and the signed boundary terms. This supports continuous clipped corrections. -/
theorem jointRampPrincipalFunctional_add {f g : ℝ → ℝ} {y : ℝ} (hy : (99 / 40 : ℝ) ≤ y)
    (hf : ContinuousOn f (Set.Icc 0 y)) (hg : ContinuousOn g (Set.Icc 0 y)) :
    jointRampPrincipalFunctional (fun u ↦ f u + g u) y =
      jointRampPrincipalFunctional f y + jointRampPrincipalFunctional g y := by
  have hL : Continuous (fun u : ℝ ↦ (u - 1) * Real.exp (-u)) :=
    (continuous_id.sub continuous_const).mul (Real.continuous_exp.comp continuous_id.neg)
  have hM :
    Continuous
      (fun u : ℝ ↦
        Real.exp (-u) * ((u - 1) * ((99 / 40 - u) / (1 / 200)) + (2 * u - 1) / (1 / 200))) :=
    Analysis.ramp_middle_density_continuous
  have hi (F : ℝ → ℝ) (hF : ContinuousOn F (Set.Icc 0 y)) (Q : ℝ → ℝ) (hQ : Continuous Q) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ y) :
    IntervalIntegrable (fun u ↦ F u * Q u) MeasureTheory.volume a b := by
    have hc : ContinuousOn F (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab]
      exact hF.mono (Set.Icc_subset_Icc ha hb)
    exact (hc.mul hQ.continuousOn).intervalIntegrable
  have hfa :=
    hi f hf _ hL (a := 0) (b := 247 / 100) le_rfl (by norm_num only) (by linarith only [hy])
  have hga :=
    hi g hg _ hL (a := 0) (b := 247 / 100) le_rfl (by norm_num only) (by linarith only [hy])
  have hfm := hi f hf _ hM (a := 247 / 100) (b := 99 / 40) (by norm_num only) (by norm_num only) hy
  have hgm := hi g hg _ hM (a := 247 / 100) (b := 99 / 40) (by norm_num only) (by norm_num only) hy
  have hfy := hi f hf _ hL (a := 0) (b := y) le_rfl (by linarith only [hy]) le_rfl
  have hgy := hi g hg _ hL (a := 0) (b := y) le_rfl (by linarith only [hy]) le_rfl
  dsimp only [jointRampPrincipalFunctional, exponentialRampVariationFunctional,
    Analysis.exponentialRampVariationLeft]
  simp only [add_mul, intervalIntegral.integral_add hfa hga, intervalIntegral.integral_add hfm hgm,
    intervalIntegral.integral_add hfy hgy]
  ring

end PseudoPrime.AnalyticNumberTheory.Arithmetic
