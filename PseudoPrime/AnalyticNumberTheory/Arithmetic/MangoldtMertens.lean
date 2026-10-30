/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.MangoldtLogZeta
public import PseudoPrime.Analysis.LogarithmicMellinIntegral
/-! # Identification of the Mangoldt Mertens constant with Euler's constant -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic
/-- Above one, differentiate `t^(1-s)/log t` to separate the reciprocal-logarithmic
main kernel from the linear part of the psi Dirichlet kernel. -/
theorem rpow_div_log_hasDerivAt {s t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t : ℝ ↦ t ^ (1 - s) / Real.log t)
      (t ^ (-s) / Real.log t - t *
        ((s * Real.log t + 1) / (t ^ (s + 1) * (Real.log t) ^ 2))) t := by
  have ht0 := zero_lt_one.trans ht
  have hl0 := Real.log_pos ht
  have h := (Real.hasDerivAt_rpow_const (p := 1 - s) (Or.inl ht0.ne')).div
    (Real.hasDerivAt_log ht0.ne') hl0.ne'
  convert h using 1
  rw [show 1 - s - 1 = -s by ring, Real.rpow_add ht0, Real.rpow_one]
  have hg : t ^ (1 - s) = t / t ^ s := by rw [Real.rpow_sub ht0, Real.rpow_one]
  rw [hg, Real.rpow_neg ht0.le]
  field_simp (disch := first | exact ht0.ne' | exact hl0.ne' |
    exact (Real.rpow_pos_of_pos ht0 s).ne')
  ring

/-- For exponent greater than one, `t^(1-s)/log t` tends to zero at infinity.
Squeeze it by twice the decaying power on the tail above two. -/
theorem tendsto_rpow_div_log_atTop {s : ℝ} (hs : 1 < s) :
    Filter.Tendsto (fun t : ℝ ↦ t ^ (1 - s) / Real.log t) Filter.atTop (nhds 0) := by
  have hp := (tendsto_rpow_neg_atTop (sub_pos.mpr hs)).mul_const 2
  simp only [zero_mul] at hp
  rw [show -(s - 1) = 1 - s by ring] at hp
  apply squeeze_zero' ?_ ?_ hp
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with t ht
    have ht0 : 0 < t := (by norm_num only : (0 : ℝ) < 2).trans_le ht
    exact div_nonneg (Real.rpow_nonneg ht0.le _) (Real.log_nonneg
      ((by norm_num only : (1 : ℝ) ≤ 2).trans ht))
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with t ht
    have ht0 : 0 < t := (by norm_num only : (0 : ℝ) < 2).trans_le ht
    have hl0 : 0 < Real.log t := Real.log_pos
      ((by norm_num only : (1 : ℝ) < 2).trans_le ht)
    have hlhalf : (1 / 2 : ℝ) ≤ Real.log t := by
      have h := Real.log_le_log (by norm_num only : (0 : ℝ) < 2) ht
      linarith only [h, Real.log_two_gt_d9]
    have hi : 1 / Real.log t ≤ (2 : ℝ) := (div_le_iff₀ hl0).mpr
      (by linarith only [hlhalf])
    simpa only [mul_one_div] using
      mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg ht0.le (1 - s))

/-- Under a second-order psi estimate and exponent in `(1,2]`, logarithmic zeta
splits into the exact lower endpoint, reciprocal-logarithmic Mellin main integral
and variable-exponent psi error integral. Integrability justifies the split. -/
theorem logZeta_eq_main_add_psi_error (hψ : PsiSecondOrderBound) {s : ℝ}
    (hs : 1 < s) (hsu : s ≤ 2) :
    Real.log (riemannZeta (s : ℂ)).re =
      (2 : ℝ) ^ (1 - s) / Real.log 2 +
      (∫ t : ℝ in Set.Ioi 2, t ^ (-s) / Real.log t) +
      ∫ t : ℝ in Set.Ioi 2, psiLogDirichletError s t := by
  let D : ℝ → ℝ := fun t ↦
    (s * Real.log t + 1) / (t ^ (s + 1) * (Real.log t) ^ 2)
  have hP := integrable_psiLogDirichletKernel hs
  have hE := integrable_psiLogDirichletError hψ hs.le hsu
  have hB : MeasureTheory.IntegrableOn (fun t : ℝ ↦ t * D t) (Set.Ioi 2) := by
    apply (hP.sub hE).congr_fun ?_ measurableSet_Ioi
    intro t _
    dsimp only [Pi.sub_apply, Pi.add_apply, D, psiLogDirichletError]
    ring
  have hJ := Analysis.integrable_logMellin_Ioi hs
  have hG := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t ht ↦ rpow_div_log_hasDerivAt ((by norm_num only : (1 : ℝ) < 2).trans_le ht))
    (hJ.sub hB) (tendsto_rpow_div_log_atTop hs)
  rw [MeasureTheory.integral_sub hJ hB] at hG
  have hBase : (∫ t : ℝ in Set.Ioi 2, t * D t) =
      (∫ t : ℝ in Set.Ioi 2, t ^ (-s) / Real.log t) +
        (2 : ℝ) ^ (1 - s) / Real.log 2 := by
    linarith only [hG]
  have hSplit : (∫ t : ℝ in Set.Ioi 2, Chebyshev.psi t * D t) =
      (∫ t : ℝ in Set.Ioi 2, t * D t) +
        ∫ t : ℝ in Set.Ioi 2, psiLogDirichletError s t := by
    rw [← MeasureTheory.integral_add hB hE]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only [Pi.sub_apply, Pi.add_apply, D, psiLogDirichletError]
    ring
  rw [logZeta_eq_psiLogDirichlet_integral hs, hSplit, hBase]
  ring


/-- A second-order psi estimate identifies the partial-summation constant with Euler's
constant. Compare the normalized zeta residual limit with the independent logarithmic
Mellin integral limit through the exact Abel decomposition; uniqueness gives the value. -/
theorem psiMertensConstant_eq_euler (hψ : PsiSecondOrderBound) :
    psiMertensConstant = Real.eulerMascheroniConstant := by
  have hC := tendsto_logZeta_error_residual hψ
  have he :
      (fun s : ℝ ↦ Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1) -
        (2 ^ (1 - s) / Real.log 2) -
        ∫ t in Set.Ioi 2, psiLogDirichletError s t) =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
      (fun s : ℝ ↦ (∫ t : ℝ in Set.Ioi 2, t ^ (-s) / Real.log t) + Real.log (s - 1)) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_le_nhds (by norm_num only : (1 : ℝ) < 2)).filter_mono
        nhdsWithin_le_nhds] with s hs hs2
    rw [logZeta_eq_main_add_psi_error hψ hs hs2]
    ring
  have h := tendsto_nhds_unique (Filter.Tendsto.congr' he hC)
    Analysis.tendsto_logMellin_normalized
  linarith only [h]

/-- A second-order psi bound alone implies the second-order logarithmic Mangoldt bound.
The constant is identified with Euler's constant by the proved Abel-Mellin comparison. -/
theorem mangoldtSecondOrder_of_psi (hψ : PsiSecondOrderBound) : MangoldtLogSumSecondOrderBound := by
  exact mangoldtSecondOrder_of_constant hψ (psiMertensConstant_eq_euler hψ)

end PseudoPrime.AnalyticNumberTheory.Arithmetic
