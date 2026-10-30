/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.MangoldtConstant
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
/-! # The variable-exponent psi error in the logarithmic zeta integral -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic
/-- The psi remainder multiplied by the derivative kernel for `1/(t^s log t)`.
The parameters are exponent `s` and real cutoff `t`; values are totalized outside
the positive domain. It is used in the logarithmic zeta Abel formula and its
limit at exponent one. -/
noncomputable def psiLogDirichletError (s t : ℝ) : ℝ :=
  (Chebyshev.psi t - t) * ((s * Real.log t + 1) / (t ^ (s + 1) * (Real.log t) ^ 2))

/-- The variable-exponent psi error specializes at exponent one to the existing
logarithmic error kernel, using the integer real-power identity. -/
theorem psiLogDirichletError_one (t : ℝ) : psiLogDirichletError 1 t = psiLogErrorKernel t := by
  dsimp only [psiLogDirichletError, psiLogErrorKernel]
  norm_num only [one_mul]
  rw [Real.rpow_two]

/-- For every fixed real exponent, the variable-exponent psi error is measurable.
Use measurability of psi, logarithm and real powers with total division. -/
theorem measurable_psiLogDirichletError (s : ℝ) : Measurable (psiLogDirichletError s) := by
  exact (Chebyshev.psi_mono.measurable.sub measurable_id).mul
    (((measurable_const.mul Real.measurable_log).add measurable_const).div
      ((measurable_id.pow_const (s + 1)).mul (Real.measurable_log.pow_const 2)))

/-- For exponents in `[1,2]` and arguments above two, the absolute variable-exponent
psi error is at most twice the original error kernel norm.
Monotonicity of positive real powers controls the denominator uniformly. -/
theorem psiLogDirichletError_abs_le {s t : ℝ} (hs : 1 ≤ s) (hsu : s ≤ 2) (ht : 2 < t) :
    |psiLogDirichletError s t| ≤ 2 * |psiLogErrorKernel t| := by
  have ht0 : 0 < t := (by norm_num only : (0 : ℝ) < 2).trans ht
  have ht1 : 1 ≤ t := (by norm_num only : (1 : ℝ) ≤ 2).trans ht.le
  have hl : 0 < Real.log t := Real.log_pos ((by norm_num only : (1 : ℝ) < 2).trans ht)
  have hp : t ^ 2 ≤ t ^ (s + 1) := by
    rw [← Real.rpow_natCast t 2]
    apply Real.rpow_le_rpow_of_exponent_le ht1
    norm_num only
    linarith only [hs]
  have hn : s * Real.log t + 1 ≤ 2 * (Real.log t + 1) := by
    have h := mul_le_mul_of_nonneg_right hsu hl.le
    linarith only [h]
  have hnum : 0 ≤ s * Real.log t + 1 := by
    have hs0 : 0 ≤ s := (by norm_num only : (0 : ℝ) ≤ 1).trans hs
    positivity
  have hd : (s * Real.log t + 1) / (t ^ (s + 1) * (Real.log t) ^ 2) ≤
      2 * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) := by
    calc
      _ ≤ (s * Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2) :=
        div_le_div_of_nonneg_left hnum (by positivity)
          (mul_le_mul_of_nonneg_right hp (sq_nonneg _))
      _ ≤ (2 * (Real.log t + 1)) / (t ^ 2 * (Real.log t) ^ 2) :=
        div_le_div_of_nonneg_right hn (by positivity)
      _ = _ := by ring
  have hds : 0 ≤ (s * Real.log t + 1) / (t ^ (s + 1) * (Real.log t) ^ 2) :=
    div_nonneg hnum (by positivity)
  have hd1 : 0 ≤ (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2) := by positivity
  dsimp only [psiLogDirichletError, psiLogErrorKernel]
  rw [abs_mul, abs_mul, abs_of_nonneg hds, abs_of_nonneg hd1]
  nlinarith only [mul_le_mul_of_nonneg_left hd (abs_nonneg (Chebyshev.psi t - t))]

/-- At every argument above two, the variable-exponent error is continuous in the
exponent at one. All logarithmic and real-power denominators are nonzero. -/
theorem psiLogDirichletError_continuousAt {t : ℝ} (ht : 2 < t) :
    ContinuousAt (fun s : ℝ ↦ psiLogDirichletError s t) 1 := by
  have ht0 : 0 < t := (by norm_num only : (0 : ℝ) < 2).trans ht
  have hl0 : 0 < Real.log t := Real.log_pos ((by norm_num only : (1 : ℝ) < 2).trans ht)
  have hp : ContinuousAt (fun s : ℝ ↦ t ^ (s + 1)) 1 :=
    (Real.continuous_const_rpow ht0.ne').continuousAt.comp
      (continuousAt_id.add continuousAt_const)
  have hd : (t ^ ((1 : ℝ) + 1) * (Real.log t) ^ 2) ≠ 0 := by positivity
  exact continuousAt_const.mul
    (((continuousAt_id.mul continuousAt_const).add continuousAt_const).div
      (hp.mul continuousAt_const) hd)

/-- Under the second-order psi bound, the error integrals converge as the exponent
approaches one from above. Dominate by twice the integrable original kernel norm;
pointwise continuity justifies passing the limit through the improper integral. -/
theorem tendsto_psiLogDirichletError (hψ : PsiSecondOrderBound) :
    Filter.Tendsto
      (fun s : ℝ ↦ ∫ t in Set.Ioi 2, psiLogDirichletError s t)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (∫ t in Set.Ioi 2, psiLogErrorKernel t)) := by
  have hbound : MeasureTheory.IntegrableOn
      (fun t ↦ 2 * |psiLogErrorKernel t|) (Set.Ioi 2) := by
    change MeasureTheory.Integrable (fun t ↦ 2 * |psiLogErrorKernel t|)
      (MeasureTheory.volume.restrict (Set.Ioi 2))
    simpa only [Real.norm_eq_abs] using (integrable_psiLogErrorKernel hψ).norm.const_mul 2
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun t ↦ 2 * |psiLogErrorKernel t|) ?_ ?_ hbound ?_
  · exact Filter.Eventually.of_forall
      (fun s ↦ (measurable_psiLogDirichletError s).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_le_nhds (by norm_num only : (1 : ℝ) < 2)).filter_mono
        nhdsWithin_le_nhds] with s hs hs2
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs]
    exact psiLogDirichletError_abs_le (show 1 < s from hs).le hs2 ht
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have h : Filter.Tendsto (fun s : ℝ ↦ psiLogDirichletError s t)
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (psiLogDirichletError 1 t)) :=
      (psiLogDirichletError_continuousAt ht).tendsto.mono_left nhdsWithin_le_nhds
    simpa only [psiLogDirichletError_one] using h


/-- Under the second-order psi bound and exponent in `[1,2]`, the variable-exponent
error is integrable on the full half-line above two, by the uniform majorant. -/
theorem integrable_psiLogDirichletError (hψ : PsiSecondOrderBound) {s : ℝ}
    (hs : 1 ≤ s) (hsu : s ≤ 2) :
    MeasureTheory.IntegrableOn (psiLogDirichletError s) (Set.Ioi 2) := by
  have hbound : MeasureTheory.Integrable
      (fun t ↦ 2 * |psiLogErrorKernel t|)
      (MeasureTheory.volume.restrict (Set.Ioi 2)) := by
    simpa only [Real.norm_eq_abs] using (integrable_psiLogErrorKernel hψ).norm.const_mul 2
  apply hbound.mono' (measurable_psiLogDirichletError s).aestronglyMeasurable
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs]
  exact psiLogDirichletError_abs_le hs hsu ht

/-- Under a second-order psi estimate, the pole-normalized logarithmic zeta
remainder after removing the lower endpoint and psi error integral tends to
`-psiMertensConstant-log(log 2)`. Combine the existing zeta pole limit with the
proved dominated-convergence theorem. A separate Abel identity and exponential
integral limit are still needed to identify the constant with Euler's constant. -/
theorem tendsto_logZeta_error_residual (hψ : PsiSecondOrderBound) :
    Filter.Tendsto
      (fun s : ℝ ↦ Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1) -
        (2 ^ (1 - s) / Real.log 2) -
        ∫ t in Set.Ioi 2, psiLogDirichletError s t)
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (-psiMertensConstant - Real.log (Real.log 2))) := by
  have hz : Filter.Tendsto
      (fun s : ℝ ↦ Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) :=
    (Asymptotics.isLittleO_one_iff ℝ).mp log_riemannZeta_add_log_sub_isLittleO_ofReal
  have hp : Filter.Tendsto (fun s : ℝ ↦ (2 : ℝ) ^ (1 - s) / Real.log 2)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 / Real.log 2)) := by
    have hc : ContinuousAt (fun s : ℝ ↦ (2 : ℝ) ^ (1 - s) / Real.log 2) 1 :=
      (((Real.continuous_const_rpow (by norm_num only : (2 : ℝ) ≠ 0)).continuousAt.comp
        (continuousAt_const.sub continuousAt_id)).div_const (Real.log 2))
    have ht : Filter.Tendsto (fun s : ℝ ↦ (2 : ℝ) ^ (1 - s) / Real.log 2)
        (nhdsWithin 1 (Set.Ioi 1)) (nhds ((2 : ℝ) ^ ((1 : ℝ) - 1) / Real.log 2)) :=
      hc.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [sub_self, Real.rpow_zero] using ht
  have he : (0 - 1 / Real.log 2) -
      (∫ t in Set.Ioi 2, psiLogErrorKernel t) =
      -psiMertensConstant - Real.log (Real.log 2) := by
    dsimp only [psiMertensConstant]
    ring
  have h := (hz.sub hp).sub (tendsto_psiLogDirichletError hψ)
  rw [he] at h
  exact h

end PseudoPrime.AnalyticNumberTheory.Arithmetic
