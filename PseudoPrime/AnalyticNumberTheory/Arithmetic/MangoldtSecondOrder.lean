/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.MangoldtLogSum
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeSumBounds
public import Mathlib.Analysis.Asymptotics.Lemmas

/-! Quantitative integral bounds for the second-order Mangoldt error. -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The psi remainder multiplied by the reciprocal logarithmic differentiation kernel.
At cutoff `t`, this is `(psi t - t) * (log t + 1) / (t^2 * (log t)^2)`.
Its integral is the remainder after partial summation of the logarithmic Mangoldt sum;
eventual second-order psi bounds provide an integrable tail majorant. -/
noncomputable def psiLogErrorKernel (t : ℝ) : ℝ :=
  (Chebyshev.psi t - t) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))

/-- The psi logarithmic error kernel is measurable on the real line.
The psi function is monotone, hence measurable; subtraction and the explicitly measurable
logarithmic factors preserve measurability. This allows domination on an infinite tail. -/
theorem measurable_psiLogErrorKernel : Measurable psiLogErrorKernel := by
  exact
    (Chebyshev.psi_mono.measurable.sub measurable_id).mul
      ((Real.measurable_log.add measurable_const).div
        ((measurable_id.pow_const 2).mul (Real.measurable_log.pow_const 2)))

/-- The psi logarithmic error kernel is integrable on every closed interval `[2, x]`.
Subtract the continuous linear main kernel from the integrable psi kernel and distribute
the subtraction. This supplies the finite portion of its half-line integrability. -/
theorem integrableOn_psiLogErrorKernel_Icc (x : ℝ) :
    MeasureTheory.IntegrableOn psiLogErrorKernel (Set.Icc 2 x) := by
  have hs : Set.Icc (2 : ℝ) x ⊆ Set.Ioi 1 := fun _ ht ↦
    (by norm_num only : (1 : ℝ) < 2).trans_le ht.1
  have ht :=
    (continuousOn_id.mul (Analysis.continuousOn_logReciprocalKernel.mono hs)).integrableOn_Icc (μ :=
      MeasureTheory.volume)
  have h := (integrableOn_psi_mul_logReciprocalKernel x).sub ht
  change
    MeasureTheory.IntegrableOn
      (fun t ↦ (Chebyshev.psi t - t) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
      (Set.Icc 2 x)
  convert h using 1
  funext t
  dsimp only [Pi.sub_apply, Pi.mul_apply, id_eq]
  ring

/-- On a tail starting at `x > 1` with `log x ≥ 1`, the second-order psi bound
dominates the norm of its error kernel by `2*B/(t*(log t)^3)` almost everywhere.
Use monotonicity of the logarithm to apply the pointwise kernel estimate on `(x, ∞)`.
This is the common domination needed for integrability and the tail integral bound. -/
private theorem psiLogErrorKernel_bound_ae {B x : ℝ} (hB : 0 ≤ B) (hx : 1 < x) (hl : 1 ≤ Real.log x)
    (hψ : ∀ t : ℝ, x ≤ t → |Chebyshev.psi t - t| ≤ B * t / (Real.log t) ^ 2) :
    ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Ioi x),
      ‖psiLogErrorKernel t‖ ≤ 2 * B / (t * (Real.log t) ^ 3) := by
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs]
  exact
    Analysis.abs_mul_logReciprocalKernel_le hB (zero_lt_one.trans (hx.trans ht))
      (hl.trans (Real.log_le_log (zero_lt_one.trans hx) ht.le)) (hψ t ht.le)

/-- The second-order psi bound makes its error kernel integrable on every sufficiently
large tail. The cutoff satisfies `x > 1` and `log x ≥ 1`, and the bound holds for all `t ≥ x`.
Dominate the measurable error kernel by the integrable cubic logarithmic kernel. -/
theorem integrableOn_psiLogErrorKernel_Ioi_of_bound {B x : ℝ} (hB : 0 ≤ B) (hx : 1 < x)
    (hl : 1 ≤ Real.log x) (hψ : ∀ t : ℝ, x ≤ t → |Chebyshev.psi t - t| ≤ B * t / (Real.log t) ^ 2) :
    MeasureTheory.IntegrableOn psiLogErrorKernel (Set.Ioi x) := by
  have hi := (Analysis.integrableOn_inv_mul_log_cube hx).const_mul (2 * B)
  have hg :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ 2 * B / (t * (Real.log t) ^ 3)) (Set.Ioi x) := by
    simpa only [MeasureTheory.IntegrableOn, mul_one_div] using hi
  exact
    hg.mono' measurable_psiLogErrorKernel.aestronglyMeasurable
      (psiLogErrorKernel_bound_ae hB hx hl hψ)

/-- A second-order psi bound on `t ≥ x` bounds the error-kernel tail by `B/(log x)^2`,
assuming `B ≥ 0`, `x > 1`, and `log x ≥ 1`. Bound the norm of the integral by the
integral of the cubic logarithmic majorant and evaluate that integral explicitly.
This is the quantitative tail estimate used in the Mangoldt second-order bound. -/
theorem abs_integral_psiLogErrorKernel_Ioi_le_of_bound {B x : ℝ} (hB : 0 ≤ B) (hx : 1 < x)
    (hl : 1 ≤ Real.log x) (hψ : ∀ t : ℝ, x ≤ t → |Chebyshev.psi t - t| ≤ B * t / (Real.log t) ^ 2) :
    |∫ t in Set.Ioi x, psiLogErrorKernel t| ≤ B / (Real.log x) ^ 2 := by
  have hi := (Analysis.integrableOn_inv_mul_log_cube hx).const_mul (2 * B)
  have hg :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ 2 * B / (t * (Real.log t) ^ 3)) (Set.Ioi x) := by
    simpa only [MeasureTheory.IntegrableOn, mul_one_div] using hi
  have h := MeasureTheory.norm_integral_le_of_norm_le hg (psiLogErrorKernel_bound_ae hB hx hl hψ)
  rw [Real.norm_eq_abs] at h
  calc
    _ ≤ ∫ t in Set.Ioi x, 2 * B / (t * (Real.log t) ^ 3) := h
    _ = B / (Real.log x) ^ 2 := by
      have hf :
        (fun t : ℝ ↦ 2 * B / (t * (Real.log t) ^ 3)) =
          (fun t ↦ 2 * B * (1 / (t * (Real.log t) ^ 3))) := by
        funext t
        rw [mul_one_div]
      rw [hf, MeasureTheory.integral_const_mul, Analysis.integral_inv_mul_log_cube hx, mul_one_div,
        mul_div_mul_left B ((Real.log x) ^ 2) (by norm_num only : (2 : ℝ) ≠ 0)]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
