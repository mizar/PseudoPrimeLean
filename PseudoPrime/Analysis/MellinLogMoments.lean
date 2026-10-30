/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.MellinLogPowers

/-! # Exact shifted logarithmic moments on the unit interval -/

@[expose] public section
namespace PseudoPrime.Analysis
/-- For Re(s)>0, the n-th logarithmic moment on (0,1] is n!/s^(n+1).
Remove the indicator from the established Mellin transform, retaining absolute
integrability. Real moments below use this complex identity. -/
theorem cpow_log_moment (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ (s - 1) * ((-Real.log u : ℝ) : ℂ) ^ n)
      (Set.Ioc 0 1) ∧
    (∫ u : ℝ in Set.Ioc 0 1, (u : ℂ) ^ (s - 1) * ((-Real.log u : ℝ) : ℂ) ^ n) =
      (n.factorial : ℂ) / s ^ (n + 1) := by
  have h := hasMellin_logPowerWeight n hs
  simp only [HasMellin, MellinConvergent, mellin, logPowerWeight_eq_smul,
    mellinWeightZero, Complex.real_smul, Complex.ofReal_pow, smul_eq_mul] at h
  have he : (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) *
      (((-Real.log t : ℝ) : ℂ) ^ n * (Set.Ioc 0 1).indicator (fun _ : ℝ ↦ (1 : ℂ)) t)) =
      (Set.Ioc 0 1).indicator (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) *
        ((-Real.log t : ℝ) : ℂ) ^ n) := by
    funext t
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
    · simp only [Set.indicator_of_mem ht, mul_one]
    · simp only [Set.indicator_of_notMem ht, mul_zero]
  rw [he] at h
  simp only [MeasureTheory.IntegrableOn, MeasureTheory.integrable_indicator_iff measurableSet_Ioc,
    MeasureTheory.integral_indicator measurableSet_Ioc,
    MeasureTheory.Measure.restrict_restrict_of_subset Set.Ioc_subset_Ioi_self] at h
  exact h
/-- For positive real s, the n-th real logarithmic moment is n!/s^(n+1).
Take real parts of the complex moment on its positive domain. Integrability and the
exact value are returned together for polynomial expansion of cutoff profiles. -/
theorem real_log_moment (n : ℕ) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ u ^ (s - 1) * (-Real.log u) ^ n)
      (Set.Ioc 0 1) ∧
    (∫ u : ℝ in Set.Ioc 0 1, u ^ (s - 1) * (-Real.log u) ^ n) =
      (n.factorial : ℝ) / s ^ (n + 1) := by
  have h := cpow_log_moment n (s := (s : ℂ)) hs
  have he (u : ℝ) (hu : u ∈ Set.Ioc (0 : ℝ) 1) :
      (u : ℂ) ^ ((s : ℂ) - 1) * ((-Real.log u : ℝ) : ℂ) ^ n =
        ((u ^ (s - 1) * (-Real.log u) ^ n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_cpow hu.1.le]
    rw [Complex.ofReal_mul, Complex.ofReal_pow]
  have hi : MeasureTheory.IntegrableOn (fun u : ℝ ↦ u ^ (s - 1) * (-Real.log u) ^ n)
      (Set.Ioc 0 1) := h.1.re.congr_fun (fun u hu ↦ by
    change (RCLike.re ((u : ℂ) ^ ((s : ℂ) - 1) * ((-Real.log u : ℝ) : ℂ) ^ n)) = _
    rw [RCLike.re_eq_complex_re, he u hu, Complex.ofReal_re]) measurableSet_Ioc
  refine ⟨hi, ?_⟩
  have hr := integral_re h.1
  rw [h.2] at hr
  simp only [RCLike.re_eq_complex_re] at hr
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_div,
    Complex.ofReal_re] at hr
  exact (MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun u hu ↦ by
    rw [he u hu, Complex.ofReal_re])).symm.trans hr
/-- For s>0, integrate u^(s-1)(b-log u)^n on (0,1], with arbitrary real shift b.
Expand the finite binomial sum and apply the real logarithmic moments termwise.
The integrability certificate justifies the finite sum in rational-pole cutoffs. -/
theorem shifted_log_moment (n : ℕ) (b : ℝ) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ u ^ (s - 1) * (b - Real.log u) ^ n)
      (Set.Ioc 0 1) ∧
    (∫ u : ℝ in Set.Ioc 0 1, u ^ (s - 1) * (b - Real.log u) ^ n) =
      ∑ j ∈ Finset.range (n + 1),
        ((n.choose j : ℝ) * b ^ (n - j)) * ((j.factorial : ℝ) / s ^ (j + 1)) := by
  have he (u : ℝ) : u ^ (s - 1) * (b - Real.log u) ^ n =
      ∑ j ∈ Finset.range (n + 1),
        ((n.choose j : ℝ) * b ^ (n - j)) * (u ^ (s - 1) * (-Real.log u) ^ j) := by
    rw [show b - Real.log u = -Real.log u + b by ring, add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi (j : ℕ) : MeasureTheory.IntegrableOn
      (fun u : ℝ ↦ ((n.choose j : ℝ) * b ^ (n - j)) *
        (u ^ (s - 1) * (-Real.log u) ^ j)) (Set.Ioc 0 1) :=
    (real_log_moment j hs).1.const_mul _
  simp_rw [he]
  refine ⟨MeasureTheory.integrable_finsetSum _ (fun j _ ↦ hi j), ?_⟩
  rw [MeasureTheory.integral_finsetSum _ (fun j _ ↦ hi j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [MeasureTheory.integral_const_mul, (real_log_moment j hs).2]
end PseudoPrime.Analysis
