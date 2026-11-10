/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.IntegratedLogSplit

/-! # Integrated explicit formula with finite zero ledgers

Evaluate the pole terms and retain the exact trivial-zero correction.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `1 < a ≤ b`, evaluate the boundary and integral contributions of
the pole terms. The constant cancels, and the logarithmic integral leaves
`-log (2π) * (b - a)`. -/
theorem pole_eval {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    b *
          (-RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re -
              Real.log (2 * Real.pi) * Real.log b +
            b) -
        a *
          (-RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re -
              Real.log (2 * Real.pi) * Real.log a +
            a) -
        (∫ t in a..b,
          (-RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re -
              Real.log (2 * Real.pi) * Real.log t +
            t)) =
      (b ^ 2 - a ^ 2) / 2 - Real.log (2 * Real.pi) * (b - a) := by
  have hl : IntervalIntegrable Real.log MeasureTheory.volume a b := by
    apply intervalIntegral.intervalIntegrable_log
    rw [Set.uIcc_of_le hab]
    intro h
    have h' := h.1
    linarith only [h', ha]
  have hc :
    IntervalIntegrable (fun _ : ℝ ↦ -RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re)
      MeasureTheory.volume a b :=
    intervalIntegrable_const
  have hi : IntervalIntegrable (fun x : ℝ ↦ x) MeasureTheory.volume a b :=
    continuous_id.intervalIntegrable a b
  rw [intervalIntegral.integral_add (hc.sub (hl.const_mul _)) hi,
    intervalIntegral.integral_sub hc (hl.const_mul _), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_log, integral_id]
  simp only [smul_eq_mul]
  ring

/-- For `1 < a ≤ b`, the integrated Chebyshev difference is the limit of
its evaluated main term and finite nontrivial-zero ledger, with the exact
trivial-zero correction retained. Combine the split formula and zero limit. -/
theorem psi1_finite_zero_limit {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    Filter.Tendsto
      (fun m : ℕ ↦
        (b ^ 2 - a ^ 2) / 2 - Real.log (2 * Real.pi) * (b - a) +
            (∑
                ρ ∈
                  (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
                        (unifiedTauRectangleUpper 2 m)).filter
                    (fun ρ ↦ ¬ρ.re < 0),
                -(riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) /
                  (ρ * (ρ + 1))).re -
          (b * riemannZetaLogTrivialZeroSeries b - a * riemannZetaLogTrivialZeroSeries a -
            ∫ t in a..b, riemannZetaLogTrivialZeroSeries t))
      Filter.atTop (nhds (Arithmetic.psiIntegralSum b - Arithmetic.psiIntegralSum a)) := by
  have hzero := (Complex.continuous_re.tendsto _).comp (boundary_limit ha hab)
  have hlim :=
    (hzero.const_add ((b ^ 2 - a ^ 2) / 2 - Real.log (2 * Real.pi) * (b - a))).sub_const
      (b * riemannZetaLogTrivialZeroSeries b - a * riemannZetaLogTrivialZeroSeries a -
        ∫ t in a..b, riemannZetaLogTrivialZeroSeries t)
  have hp := pole_eval ha hab
  have hf := psi1_diff_split ha hab
  rw [hp] at hf
  rw [hf]
  exact hlim

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
