/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# An integrable envelope for logarithmic growth with quadratic decay

The weight `(1 + log(|t| + 2)) / (1 + t²)` is nonnegative and integrable on the real line.
-/

namespace PseudoPrime.AnalyticNumberTheory.General

/-- Define the nonnegative weight `(1 + log(|t| + 2)) / (1 + t²)` for real `t`.
This integrable function provides a common majorant for logarithmic growth with quadratic decay. -/
noncomputable def logQuadraticEnvelope (t : ℝ) : ℝ :=
  (1 + Real.log (|t| + 2)) / (1 + t ^ 2)

/--
Input/assumptions: `t : ℝ`.
Conclusion: `0 ≤ logQuadraticEnvelope t`.
Content: both `1 + log(|t| + 2)` (since `|t| + 2 ≥ 1`) and `1 + t²` are nonnegative.
Role: feeds both the integrability majorant argument and the envelope mass's nonnegativity.
-/
theorem logQuadraticEnvelope_nonneg (t : ℝ) : 0 ≤ logQuadraticEnvelope t := by
  unfold logQuadraticEnvelope
  apply div_nonneg _ (by positivity)
  have := Real.log_nonneg (show (1 : ℝ) ≤ |t| + 2 by linarith [abs_nonneg t])
  linarith

/--
Input/assumptions: none.
Conclusion: `logQuadraticEnvelope` is integrable over `ℝ`.
Content: `|t| + 2 ≤ 3(1 + t²)` (`3t² - |t| + 1 > 0` always, discriminant `1 - 12 < 0`), so
`log(|t| + 2) ≤ log 3 + log(1 + t²)` (`Real.log_mul`, monotonicity); `log(1 + t²) ≤ 4(1 + t²)^{1/4}`
via `Real.log_le_rpow_div` at `ε := 1/4`. Dividing by `1 + t²` gives the pointwise majorant
`logQuadraticEnvelope t ≤ (1 + log 3)/(1 + t²) + 4(1 + t²)^{-3/4}`, whose two pieces are
integrable via mathlib's `integrable_inv_one_add_sq` and `integrable_rpow_neg_one_add_norm_sq`
(`r := 3/2 > finrank ℝ ℝ = 1`) respectively — no tail/compact case split needed.
Role: supplies integrability for functions dominated by a constant multiple of this envelope.
-/
theorem integrable_logQuadraticEnvelope : MeasureTheory.Integrable logQuadraticEnvelope := by
  set h : ℝ → ℝ := fun t => (1 + Real.log 3) * (1 + t ^ 2)⁻¹ + 4 * (1 + t ^ 2) ^ (-(3 : ℝ) / 4) with
    hh_def
  have hint1 : MeasureTheory.Integrable (fun t : ℝ => (1 + Real.log 3) * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have hint2 : MeasureTheory.Integrable (fun t : ℝ => 4 * (1 + t ^ 2) ^ (-(3 : ℝ) / 4)) := by
    have hbase : MeasureTheory.Integrable (fun t : ℝ => ((1 : ℝ) + ‖t‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2)) :=
      integrable_rpow_neg_one_add_norm_sq (E := ℝ) (r := 3 / 2)
        (by
          simp only [Module.finrank_self, Nat.cast_one]; norm_num only)
    have heq :
      (fun t : ℝ => ((1 : ℝ) + ‖t‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2)) = fun t : ℝ =>
        (1 + t ^ 2) ^ (-(3 : ℝ) / 4) := by
      funext t
      rw [Real.norm_eq_abs, sq_abs]
      norm_num only
    rw [heq] at hbase
    exact hbase.const_mul _
  have hint : MeasureTheory.Integrable h := hh_def ▸ hint1.add hint2
  have hmeas : MeasureTheory.AEStronglyMeasurable logQuadraticEnvelope MeasureTheory.volume := by
    apply Measurable.aestronglyMeasurable
    unfold logQuadraticEnvelope
    fun_prop
  refine hint.mono' hmeas (Filter.Eventually.of_forall fun t => ?_)
  have htsq_pos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hlt : |t| + 2 ≤ 3 * (1 + t ^ 2) := by nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
  have hlog1 : Real.log (|t| + 2) ≤ Real.log (3 * (1 + t ^ 2)) :=
    Real.log_le_log (by linarith [abs_nonneg t]) hlt
  have hlog2 : Real.log (3 * (1 + t ^ 2)) = Real.log 3 + Real.log (1 + t ^ 2) :=
    Real.log_mul (by norm_num only) (by positivity)
  have hlog3 : Real.log (1 + t ^ 2) ≤ (1 + t ^ 2) ^ (1 / 4 : ℝ) / (1 / 4) :=
    Real.log_le_rpow_div (by positivity) (by norm_num only)
  have hlog4 : (1 + t ^ 2) ^ (1 / 4 : ℝ) / (1 / 4) = 4 * (1 + t ^ 2) ^ (1 / 4 : ℝ) := by ring
  rw [Real.norm_eq_abs, abs_of_nonneg (logQuadraticEnvelope_nonneg t)]
  unfold logQuadraticEnvelope
  rw [div_le_iff₀ htsq_pos]
  simp only [hh_def]
  rw [add_mul]
  have hterm1 : (1 + Real.log 3) * (1 + t ^ 2)⁻¹ * (1 + t ^ 2) = 1 + Real.log 3 := by field_simp
  have hterm2 : 4 * (1 + t ^ 2) ^ (-(3 : ℝ) / 4) * (1 + t ^ 2) = 4 * (1 + t ^ 2) ^ (1 / 4 : ℝ) := by
    have h : (1 + t ^ 2) ^ (-(3 : ℝ) / 4) * (1 + t ^ 2) = (1 + t ^ 2) ^ (1 / 4 : ℝ) := by
      nth_rewrite 2 [← Real.rpow_one (1 + t ^ 2)]
      rw [← Real.rpow_add htsq_pos]
      norm_num only
    rw [mul_assoc, h]
  rw [hterm1, hterm2]
  linarith [hlog1, hlog2, hlog3, hlog4]

/-- The integral of `logQuadraticEnvelope` over the real line. Its value is a nonnegative
constant used to bound integrals of functions dominated by a multiple of this envelope. -/
noncomputable def logQuadraticEnvelopeMass : ℝ :=
  ∫ t : ℝ, logQuadraticEnvelope t

/--
Input/assumptions: none.
Conclusion: `0 ≤ logQuadraticEnvelopeMass`.
Content: `logQuadraticEnvelope` is pointwise nonnegative
(`logQuadraticEnvelope_nonneg`), so its integral is nonnegative.
Role: supplies a nonnegative constant in integral norm bounds.
-/
theorem logQuadraticEnvelopeMass_nonneg : 0 ≤ logQuadraticEnvelopeMass :=
  MeasureTheory.integral_nonneg logQuadraticEnvelope_nonneg

end PseudoPrime.AnalyticNumberTheory.General
