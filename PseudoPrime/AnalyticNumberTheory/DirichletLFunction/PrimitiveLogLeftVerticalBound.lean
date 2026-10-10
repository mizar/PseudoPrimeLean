/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.VerticalGeometry
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.SmoothedContour
public import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Pointwise logarithmic-kernel bounds on the left vertical line

Given a bound for the ordinary logarithmic derivative, control the logarithmic kernel
by its Mellin power and the common integrable logarithmic envelope. The general
logarithmic contour estimates supply the growth hypothesis and integrate these bounds.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-! ### The left-vertical line's log-kernel geometry -/

/--
Input/assumptions: `x > 0`, `A ≥ 2`, `t : ℝ`, and a bound `‖logDeriv (LFunction χ) (s_A(t))‖ ≤
D ((A + 5)² + 1 + log(|t| + 2))`.
Conclusion: `‖DirichletLFunction.dirichletLogContourKernel x χ (s_A(t))‖ ≤
D x^(-A - 1/2) ((A + 5)² + 1 + log(|t| + 2)) / (1 + t²)`.
Content: unfolds the kernel to `‖logDeriv (LFunction χ) s‖ * ‖x ^ s‖ / ‖s‖²`, then substitutes
`‖x ^ s‖ = x^(-A-1/2)` (`General.norm_cpow_leftVertical_log`) and divides through by the
denominator lower
bound `1 + t² ≤ ‖s‖²` (`General.one_add_sq_le_normSq_leftVertical`).
Role: the log-kernel pointwise bound (K), feeding the absolute-integrability argument.
-/
theorem norm_dirichletLogContourKernel_leftVertical_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {x : ℝ} (hx : 0 < x) {A : ℕ} (hA : 2 ≤ A) {t D : ℝ}
    (hL :
      ‖logDeriv (DirichletCharacter.LFunction χ)
            (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        D * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2))) :
    ‖dirichletLogContourKernel x χ (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      D * x ^ (-(A : ℝ) - 1 / 2) * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) / (1 + t ^ 2) := by
  set s : ℂ := ((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I with hs_def
  have hden := General.one_add_sq_le_normSq_leftVertical A hA t
  rw [← hs_def] at hden
  have hpow := General.norm_cpow_leftVertical_log hx A t
  rw [← hs_def] at hpow
  have hsnorm_pos : (0 : ℝ) < ‖s‖ ^ 2 := by
    have h1t : (0 : ℝ) < 1 + t ^ 2 := by positivity
    linarith only [hden, h1t]
  have hK_eq :
    ‖dirichletLogContourKernel x χ s‖ =
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ (-(A : ℝ) - 1 / 2) / ‖s‖ ^ 2 := by
    have hlogDeriv_eq :
      ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ =
        ‖logDeriv (DirichletCharacter.LFunction χ) s‖ := by
      rw [logDeriv_apply]
    unfold dirichletLogContourKernel
    rw [norm_div, norm_mul, norm_neg, hpow, hlogDeriv_eq, norm_pow]
  rw [hK_eq]
  have hLnn : (0 : ℝ) ≤ ‖logDeriv (DirichletCharacter.LFunction χ) s‖ := norm_nonneg _
  have hxpow_pos : (0 : ℝ) < x ^ (-(A : ℝ) - 1 / 2) := Real.rpow_pos_of_pos hx _
  have h1t_pos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  calc
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ (-(A : ℝ) - 1 / 2) / ‖s‖ ^ 2 ≤
        ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ (-(A : ℝ) - 1 / 2) / (1 + t ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) h1t_pos hden
    _ ≤ D * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) * x ^ (-(A : ℝ) - 1 / 2) / (1 + t ^ 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hL hxpow_pos.le) h1t_pos.le
    _ = D * x ^ (-(A : ℝ) - 1 / 2) * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) / (1 + t ^ 2) :=
      by ring

/--
Input/assumptions: `x > 0`, `A ≥ 2`, `D ≥ 0` with the pointwise `L'/L` bound
`‖logDeriv (LFunction χ) (s_A(t))‖ ≤ D ((A + 5)² + 1 + log(|t| + 2))` for every `t`.
Conclusion: `‖K_x(s_A(t))‖ ≤ D x^{-A-1/2} ((A + 5)² + 1) · General.logQuadraticEnvelope t`.
Content: same algebra as
`DirichletLFunction.norm_dirichletReciprocalContourKernel_leftVertical_envelope_le`,
substituting the log-kernel pointwise bound `(K)` and its `x^{-A-1/2}` power factor.
Role: the log-kernel envelope bound, using the integrable function `logQuadraticEnvelope`.
-/
theorem norm_dirichletLogContourKernel_leftVertical_envelope_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {x : ℝ} (hx : 0 < x) {A : ℕ} (hA : 2 ≤ A) {D : ℝ} (hDnn : 0 ≤ D)
    (hLbound :
      ∀ t : ℝ,
        ‖logDeriv (DirichletCharacter.LFunction χ)
              (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          D * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)))
    (t : ℝ) :
    ‖dirichletLogContourKernel x χ (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      D * x ^ (-(A : ℝ) - 1 / 2) * (((A : ℝ) + 5) ^ 2 + 1) * General.logQuadraticEnvelope t := by
  have hK := norm_dirichletLogContourKernel_leftVertical_le hx hA (hLbound t)
  set BA : ℝ := ((A : ℝ) + 5) ^ 2 + 1 with hBA_def
  have hBA1 : (1 : ℝ) ≤ BA := by
    rw [hBA_def]
    nlinarith only [sq_nonneg ((A : ℝ) + 5)]
  have htlog_nn : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith only [abs_nonneg t])
  have htsq_pos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hxpow_nn : (0 : ℝ) ≤ x ^ (-(A : ℝ) - 1 / 2) := (Real.rpow_pos_of_pos hx _).le
  have hstep : BA + Real.log (|t| + 2) ≤ BA * (1 + Real.log (|t| + 2)) := by
    nlinarith only [hBA1, htlog_nn]
  have hnum :
    D * x ^ (-(A : ℝ) - 1 / 2) * (BA + Real.log (|t| + 2)) ≤
      D * x ^ (-(A : ℝ) - 1 / 2) * (BA * (1 + Real.log (|t| + 2))) :=
    mul_le_mul_of_nonneg_left hstep (mul_nonneg hDnn hxpow_nn)
  unfold General.logQuadraticEnvelope
  calc
    ‖dirichletLogContourKernel x χ (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        D * x ^ (-(A : ℝ) - 1 / 2) * (BA + Real.log (|t| + 2)) / (1 + t ^ 2) :=
      hK
    _ ≤ D * x ^ (-(A : ℝ) - 1 / 2) * (BA * (1 + Real.log (|t| + 2))) / (1 + t ^ 2) :=
      div_le_div_of_nonneg_right hnum htsq_pos.le
    _ = D * x ^ (-(A : ℝ) - 1 / 2) * BA * ((1 + Real.log (|t| + 2)) / (1 + t ^ 2)) := by ring

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
