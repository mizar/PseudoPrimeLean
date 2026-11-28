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
  simp only [HasMellin, MellinConvergent, mellin, logPowerWeight_eq_smul, mellinWeightZero,
    Complex.real_smul, Complex.ofReal_pow, smul_eq_mul] at h
  have he :
    (fun t : ℝ ↦
        (t : ℂ) ^ (s - 1) *
          (((-Real.log t : ℝ) : ℂ) ^ n * (Set.Ioc 0 1).indicator (fun _ : ℝ ↦ (1 : ℂ)) t)) =
      (Set.Ioc 0 1).indicator (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) * ((-Real.log t : ℝ) : ℂ) ^ n) := by
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
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ u ^ (s - 1) * (-Real.log u) ^ n) (Set.Ioc 0 1) ∧
      (∫ u : ℝ in Set.Ioc 0 1, u ^ (s - 1) * (-Real.log u) ^ n) =
        (n.factorial : ℝ) / s ^ (n + 1) := by
  have h := cpow_log_moment n (s := (s : ℂ)) hs
  have he (u : ℝ) (hu : u ∈ Set.Ioc (0 : ℝ) 1) :
    (u : ℂ) ^ ((s : ℂ) - 1) * ((-Real.log u : ℝ) : ℂ) ^ n =
      ((u ^ (s - 1) * (-Real.log u) ^ n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_cpow hu.1.le]
    rw [Complex.ofReal_mul, Complex.ofReal_pow]
  have hi :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ u ^ (s - 1) * (-Real.log u) ^ n) (Set.Ioc 0 1) :=
    h.1.re.congr_fun
      (fun u hu ↦ by
        change (RCLike.re ((u : ℂ) ^ ((s : ℂ) - 1) * ((-Real.log u : ℝ) : ℂ) ^ n)) = _
        rw [RCLike.re_eq_complex_re, he u hu, Complex.ofReal_re])
      measurableSet_Ioc
  refine ⟨hi, ?_⟩
  have hr := integral_re h.1
  rw [h.2] at hr
  simp only [RCLike.re_eq_complex_re] at hr
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re] at hr
  exact
    (MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
          (fun u hu ↦ by rw [he u hu, Complex.ofReal_re])).symm.trans
      hr

/-- For s>0, integrate u^(s-1)(b-log u)^n on (0,1], with arbitrary real shift b.
Expand the finite binomial sum and apply the real logarithmic moments termwise.
The integrability certificate justifies the finite sum in rational-pole cutoffs. -/
theorem shifted_log_moment (n : ℕ) (b : ℝ) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ u ^ (s - 1) * (b - Real.log u) ^ n) (Set.Ioc 0 1) ∧
      (∫ u : ℝ in Set.Ioc 0 1, u ^ (s - 1) * (b - Real.log u) ^ n) =
        ∑ j ∈ Finset.range (n + 1),
          ((n.choose j : ℝ) * b ^ (n - j)) * ((j.factorial : ℝ) / s ^ (j + 1)) := by
  have he (u : ℝ) :
    u ^ (s - 1) * (b - Real.log u) ^ n =
      ∑ j ∈ Finset.range (n + 1),
        ((n.choose j : ℝ) * b ^ (n - j)) * (u ^ (s - 1) * (-Real.log u) ^ j) := by
    rw [show b - Real.log u = -Real.log u + b by ring, add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi (j : ℕ) :
    MeasureTheory.IntegrableOn
      (fun u : ℝ ↦ ((n.choose j : ℝ) * b ^ (n - j)) * (u ^ (s - 1) * (-Real.log u) ^ j))
      (Set.Ioc 0 1) :=
    (real_log_moment j hs).1.const_mul _
  simp_rw [he]
  refine ⟨MeasureTheory.integrable_finsetSum _ (fun j _ ↦ hi j), ?_⟩
  rw [MeasureTheory.integral_finsetSum _ (fun j _ ↦ hi j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [MeasureTheory.integral_const_mul, (real_log_moment j hs).2]

/-- For a complex exponent with positive real part, expand the shifted
logarithmic power and integrate each term on the unit interval. -/
theorem complex_shifted_log_moment (n : ℕ) (b : ℝ) {s : ℂ} (hs : 0 < s.re) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ (s - 1) * ((b - Real.log u : ℝ) : ℂ) ^ n)
        (Set.Ioc 0 1) ∧
      (∫ u : ℝ in Set.Ioc 0 1, (u : ℂ) ^ (s - 1) * ((b - Real.log u : ℝ) : ℂ) ^ n) =
        ∑ j ∈ Finset.range (n + 1),
          ((n.choose j : ℂ) * (b : ℂ) ^ (n - j)) * ((j.factorial : ℂ) / s ^ (j + 1)) := by
  have he (u : ℝ) :
    (u : ℂ) ^ (s - 1) * ((b - Real.log u : ℝ) : ℂ) ^ n =
      ∑ j ∈ Finset.range (n + 1),
        ((n.choose j : ℂ) * (b : ℂ) ^ (n - j)) *
          ((u : ℂ) ^ (s - 1) * ((-Real.log u : ℝ) : ℂ) ^ j) := by
    rw [show b - Real.log u = -Real.log u + b by ring, Complex.ofReal_add, add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi (j : ℕ) :
    MeasureTheory.IntegrableOn
      (fun u : ℝ ↦
        ((n.choose j : ℂ) * (b : ℂ) ^ (n - j)) * ((u : ℂ) ^ (s - 1) * ((-Real.log u : ℝ) : ℂ) ^ j))
      (Set.Ioc 0 1) :=
    (cpow_log_moment j hs).1.const_mul _
  simp_rw [he]
  refine ⟨MeasureTheory.integrable_finsetSum _ (fun j _ ↦ hi j), ?_⟩
  rw [MeasureTheory.integral_finsetSum _ (fun j _ ↦ hi j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [MeasureTheory.integral_const_mul, (cpow_log_moment j hs).2]

/-- The shifted complex log moment up to a positive cutoff is a unit
moment with a shifted logarithm, multiplied by the cutoff power. -/
theorem complex_log_moment_cutoff (n : ℕ) (b : ℝ) {s : ℂ} (hs : 0 < s.re) {y : ℝ} (hy : 0 < y) :
    (∫ u in (0 : ℝ)..y, (u : ℂ) ^ (s - 1) * ((b - Real.log u : ℝ) : ℂ) ^ n) =
      (y : ℂ) ^ s *
        ∑ j ∈ Finset.range (n + 1),
          ((n.choose j : ℂ) * ((b - Real.log y : ℝ) : ℂ) ^ (n - j)) *
            ((j.factorial : ℂ) / s ^ (j + 1)) := by
  let f := fun u : ℝ ↦ (u : ℂ) ^ (s - 1) * ((b - Real.log u : ℝ) : ℂ) ^ n
  let g := fun u : ℝ ↦ (u : ℂ) ^ (s - 1) * (((b - Real.log y) - Real.log u : ℝ) : ℂ) ^ n
  have h := intervalIntegral.smul_integral_comp_mul_right f (a := 0) (b := 1) y
  rw [zero_mul, one_mul] at h
  have he : (∫ u in (0 : ℝ)..1, f (u * y)) = ∫ u in (0 : ℝ)..1, (y : ℂ) ^ (s - 1) * g u := by
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    dsimp only [f, g]
    rw [Complex.ofReal_mul, Complex.ofReal_mul_cpow hu.1.le y, Real.log_mul hu.1.ne' hy.ne',
      show b - (Real.log u + Real.log y) = b - Real.log y - Real.log u by ring]
    ring
  rw [he, intervalIntegral.integral_const_mul, Complex.real_smul] at h
  have hp : (y : ℂ) * (y : ℂ) ^ (s - 1) = (y : ℂ) ^ s := by
    conv_lhs =>
      lhs; rw [← Complex.cpow_one (y : ℂ)]
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy.ne')]
    congr 1
    ring
  rw [← mul_assoc, hp] at h
  rw [← h, intervalIntegral.integral_of_le zero_le_one]
  exact congrArg ((y : ℂ) ^ s * ·) (complex_shifted_log_moment n (b - Real.log y) hs).2

/-- The complex logarithmic moment is integrable up to any positive cutoff.
Use the unit moment near zero and continuity on the remaining compact interval. -/
theorem complex_log_moment_integrable (n : ℕ) (b : ℝ) {s : ℂ} (hs : 0 < s.re) {y : ℝ} (hy : 0 < y) :
    IntervalIntegrable (fun u : ℝ ↦ (u : ℂ) ^ (s - 1) * ((b - Real.log u : ℝ) : ℂ) ^ n)
      MeasureTheory.volume 0 y := by
  have h₁ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
      (complex_shifted_log_moment n b hs).1
  rcases le_or_gt y 1 with h | h
  · apply h₁.mono_set
    rw [Set.uIcc_of_le hy.le, Set.uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc_right h
  · apply h₁.trans
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h.le]
    intro u hu
    have hu0 := zero_lt_one.trans_le hu.1
    have hp := Complex.continuousAt_ofReal_cpow_const u (s - 1) (Or.inr hu0.ne')
    have hl := (continuousAt_const (y := b)).sub (Real.continuousAt_log hu0.ne')
    exact (hp.mul ((Complex.continuous_ofReal.continuousAt.comp hl).pow n)).continuousWithinAt

end PseudoPrime.Analysis
