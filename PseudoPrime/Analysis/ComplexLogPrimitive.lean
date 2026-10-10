/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Logarithmic primitives on zero-free disks

Normalize a holomorphic primitive of the logarithmic derivative so that its real
part equals the logarithm of the function's norm, without choosing a log branch.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/--
On a positive-radius disk where `f` is analytic and nonvanishing, its logarithmic
derivative has a primitive whose real part equals `log ‖f‖`. Normalize the primitive
at the center and show `exp(h)/f` has zero derivative and equals one.
Borel–Carathéodory estimates use this primitive without a principal-log branch choice.
-/
theorem exists_hasDerivAt_logDeriv_re_eq_log_norm {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hfAn : AnalyticOnNhd ℂ f (Metric.ball c r)) (hfne : ∀ w ∈ Metric.ball c r, f w ≠ 0) :
    ∃ h : ℂ → ℂ,
      (∀ w ∈ Metric.ball c r, HasDerivAt h (logDeriv f w) w) ∧
        ∀ w ∈ Metric.ball c r, (h w).re = Real.log ‖f w‖ := by
  have hfDiffOn : DifferentiableOn ℂ f (Metric.ball c r) := fun w hw =>
    (hfAn w hw).differentiableWithinAt
  have hlogDerivEq : logDeriv f = fun w => deriv f w / f w := by
    funext w
    rw [logDeriv_apply]
  have hlogDerivDiffOn : DifferentiableOn ℂ (logDeriv f) (Metric.ball c r) := by
    rw [hlogDerivEq]
    exact (hfDiffOn.deriv Metric.isOpen_ball).div hfDiffOn hfne
  obtain ⟨h, hhc, hh'⟩ := (hlogDerivDiffOn.isExactOn_ball).with_val_at c (Complex.log (f c))
  set G : ℂ → ℂ := fun w => Complex.exp (h w) * (f w)⁻¹ with hG_def
  have hGhasDerivAt : ∀ w ∈ Metric.ball c r, HasDerivAt G 0 w := by
    intro w hw
    have hhw := hh' w hw
    have hfnew := hfne w hw
    have hderivf : deriv f w = logDeriv f w * f w := by
      have hlog : logDeriv f w = deriv f w / f w := by rw [hlogDerivEq]
      rw [hlog, div_mul_cancel₀]
      exact hfnew
    have hfHasDeriv : HasDerivAt f (logDeriv f w * f w) w := by
      rw [← hderivf]
      exact ((hfDiffOn w hw).differentiableAt (Metric.isOpen_ball.mem_nhds hw)).hasDerivAt
    have hexpw : HasDerivAt (fun w => Complex.exp (h w)) (Complex.exp (h w) * logDeriv f w) w :=
      hhw.cexp
    have hinvw : HasDerivAt (fun w => (f w)⁻¹) (-(logDeriv f w * f w) / (f w) ^ 2) w :=
      hfHasDeriv.inv hfnew
    have hGw :
      HasDerivAt G
        (Complex.exp (h w) * logDeriv f w * (f w)⁻¹ +
          Complex.exp (h w) * (-(logDeriv f w * f w) / (f w) ^ 2))
        w :=
      hexpw.mul hinvw
    have hzero :
      Complex.exp (h w) * logDeriv f w * (f w)⁻¹ +
          Complex.exp (h w) * (-(logDeriv f w * f w) / (f w) ^ 2) =
        0 := by
      field_simp [hfnew]
      ring
    rw [hzero] at hGw
    exact hGw
  have hGDiffOn : DifferentiableOn ℂ G (Metric.ball c r) := fun w hw =>
    (hGhasDerivAt w hw).differentiableAt.differentiableWithinAt
  have hderiv0 : (Metric.ball c r).EqOn (deriv G) 0 := fun w hw => (hGhasDerivAt w hw).deriv
  have hcmem : c ∈ Metric.ball c r := Metric.mem_ball_self hr
  have hfnec := hfne c hcmem
  have hGc : G c = 1 := by
    change Complex.exp (h c) * (f c)⁻¹ = 1
    rw [hhc, Complex.exp_log hfnec, mul_inv_cancel₀ hfnec]
  have hconst := fun w (hw : w ∈ Metric.ball c r) =>
    Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c r).isPreconnected hGDiffOn hderiv0
      hcmem hw
  refine ⟨h, hh', fun w hw => ?_⟩
  have hGw1 : G w = 1 := (hconst w hw).symm.trans hGc
  have hfnew := hfne w hw
  have hexpeq : Complex.exp (h w) = f w := by
    have heq1 : Complex.exp (h w) * (f w)⁻¹ = 1 := hGw1
    field_simp [hfnew] at heq1
    exact heq1
  have hnormeq : Real.exp (h w).re = ‖f w‖ := by rw [← Complex.norm_exp, hexpeq]
  have hpos : (0 : ℝ) < ‖f w‖ := norm_pos_iff.mpr hfnew
  rw [← hnormeq, Real.log_exp]

end PseudoPrime.Analysis
