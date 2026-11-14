/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalLineMellin

/-! # Explicit Gaussian truncation bounds for the theta kernel -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- The positive Gaussian tail starting at the integer `N + 1` is bounded
by a geometric series. The denominator is positive for every `x > 0`. -/
theorem gaussian_nat_tail_bound (N : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖∑' k : ℕ, Real.exp (-Real.pi * ((k : ℝ) + ((N : ℝ) + 1)) ^ 2 * x)‖ ≤
      Real.exp (-Real.pi * ((N : ℝ) + 1) ^ 2 * x) / (1 - Real.exp (-Real.pi * x)) := by
  have ha : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
  simpa only [HurwitzKernelBounds.F_nat, HurwitzKernelBounds.f_nat, pow_zero, one_mul] using
    HurwitzKernelBounds.F_nat_zero_le ha hx

/-- The even theta kernel equals its constant term plus twice the positive
Gaussian series. Integer reflection pairs the nonzero terms. -/
theorem theta_kernel_eq_positive_series {x : ℝ} (hx : 0 < x) :
    HurwitzZeta.evenKernel 0 x - 1 = 2 * HurwitzKernelBounds.F_nat 0 1 x := by
  have hi : HurwitzKernelBounds.F_int 0 0 x = HurwitzZeta.evenKernel 0 x := by
    have hi' :
      HurwitzKernelBounds.F_int 0 ((0 : ℝ) : UnitAddCircle) x =
        HurwitzZeta.evenKernel ((0 : ℝ) : UnitAddCircle) x := by
      rw [HurwitzKernelBounds.F_int, Function.Periodic.lift_coe]
      have hs := (HurwitzZeta.hasSum_int_evenKernel 0 hx).tsum_eq
      simpa only [HurwitzKernelBounds.f_int, add_zero, pow_zero, one_mul] using hs
    simpa only [AddCircle.coe_zero] using hi'
  have hn :=
    HurwitzKernelBounds.F_int_eq_of_mem_Icc 0
      (show (0 : ℝ) ∈ Set.Icc 0 1 from ⟨le_refl 0, zero_le_one⟩) hx
  norm_num only [AddCircle.coe_zero, sub_zero] at hn
  have hz : HurwitzKernelBounds.F_nat 0 0 x = 1 + HurwitzKernelBounds.F_nat 0 1 x := by
    rw [HurwitzKernelBounds.F_nat, (HurwitzKernelBounds.summable_f_nat 0 0 hx).tsum_eq_zero_add]
    simp only [HurwitzKernelBounds.f_nat, Nat.cast_zero, add_zero, pow_zero, one_mul,
      HurwitzKernelBounds.F_nat, Nat.cast_add, Nat.cast_one]
    norm_num only
    simp only [mul_zero, zero_mul, Real.exp_zero]
  linarith only [hi, hn, hz]

/-- Removing the first `N` positive Gaussian terms leaves twice the shifted
natural-number tail. This identity connects a finite kernel sum to the
geometric tail bound. -/
theorem theta_kernel_sub_finite {x : ℝ} (hx : 0 < x) (N : ℕ) :
    HurwitzZeta.evenKernel 0 x - 1 -
        2 * ∑ k ∈ Finset.range N, Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * x) =
      2 * ∑' k : ℕ, Real.exp (-Real.pi * ((k : ℝ) + ((N : ℝ) + 1)) ^ 2 * x) := by
  rw [theta_kernel_eq_positive_series hx, HurwitzKernelBounds.F_nat]
  have hs := (HurwitzKernelBounds.summable_f_nat 0 1 hx).sum_add_tsum_nat_add N
  simp only [HurwitzKernelBounds.f_nat, pow_zero, one_mul, Nat.cast_add, add_assoc] at hs ⊢
  linarith only [hs]

/-- The error after `N` positive Gaussian terms in the even theta kernel is
at most an explicit geometric tail. This estimate is valid for any `x > 0`
and can be used to certify the finite Mellin-integral approximation. -/
theorem theta_kernel_finite_error {x : ℝ} (hx : 0 < x) (N : ℕ) :
    ‖HurwitzZeta.evenKernel 0 x - 1 -
          2 * ∑ k ∈ Finset.range N, Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * x)‖ ≤
      2 * (Real.exp (-Real.pi * ((N : ℝ) + 1) ^ 2 * x) / (1 - Real.exp (-Real.pi * x))) := by
  rw [theta_kernel_sub_finite hx N, norm_mul, Real.norm_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left (gaussian_nat_tail_bound N hx) (by norm_num only)

/-- For `x ≥ 1`, the Gaussian geometric ratio is at most `1/2`.
The elementary lower bound for the exponential and `π > 3` prove the
uniform denominator estimate without numerical tables. -/
theorem gaussian_ratio_le_half {x : ℝ} (hx : 1 ≤ x) : Real.exp (-Real.pi * x) ≤ 1 / 2 := by
  have hpi : (1 : ℝ) ≤ Real.pi * x := by nlinarith only [Real.pi_gt_three, hx]
  have he := Real.add_one_le_exp (Real.pi * x)
  have hp : 0 < Real.exp (Real.pi * x) := Real.exp_pos _
  rw [show -Real.pi * x = -(Real.pi * x) by ring, Real.exp_neg, inv_eq_one_div]
  apply (div_le_iff₀ hp).2
  linarith only [he, hpi]

/-- On `x ≥ 1`, the theta-kernel truncation error is at most four times
the first omitted Gaussian exponential. This simpler estimate removes the
geometric denominator and is suitable for integration over an upper tail. -/
theorem theta_kernel_finite_error_uniform {x : ℝ} (hx : 1 ≤ x) (N : ℕ) :
    ‖HurwitzZeta.evenKernel 0 x - 1 -
          2 * ∑ k ∈ Finset.range N, Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * x)‖ ≤
      4 * Real.exp (-Real.pi * ((N : ℝ) + 1) ^ 2 * x) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hq := gaussian_ratio_le_half hx
  have hd : 0 < 1 - Real.exp (-Real.pi * x) := by linarith only [hq]
  have he : 0 ≤ Real.exp (-Real.pi * ((N : ℝ) + 1) ^ 2 * x) := (Real.exp_pos _).le
  have hdiv :
    Real.exp (-Real.pi * ((N : ℝ) + 1) ^ 2 * x) / (1 - Real.exp (-Real.pi * x)) ≤
      2 * Real.exp (-Real.pi * ((N : ℝ) + 1) ^ 2 * x) := by
    apply (div_le_iff₀ hd).2
    nlinarith only [hq, he]
  have h := theta_kernel_finite_error hx0 N
  nlinarith only [h, hdiv]

/-- Above one, the modified Mellin kernel is approximated by `N` positive
Gaussian terms with the stated explicit uniform error. This transfers the
real theta bound to the complex-valued kernel used by the Mellin integral. -/
theorem modified_theta_finite_error {x : ℝ} (hx : 1 < x) (N : ℕ) :
    ‖(HurwitzZeta.hurwitzEvenFEPair 0).f_modif x -
          ((2 * ∑ k ∈ Finset.range N, Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * x) : ℝ) : ℂ)‖ ≤
      4 * Real.exp (-Real.pi * ((N : ℝ) + 1) ^ 2 * x) := by
  rw [modified_theta_kernel_above_one hx, ← Complex.ofReal_one, ← Complex.ofReal_sub, ←
    Complex.ofReal_sub, Complex.norm_real]
  exact theta_kernel_finite_error_uniform hx.le N

/-- For positive `x`, inversion of the modified theta kernel multiplies it
by `sqrt x`. This self-dual functional equation permits the lower half of
the Mellin integral to be transferred to the upper half. -/
theorem modified_theta_inversion {x : ℝ} (hx : 0 < x) :
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (1 / x) =
      ((Real.sqrt x : ℝ) : ℂ) * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x := by
  have hs :
    (HurwitzZeta.hurwitzEvenFEPair 0).g_modif = (HurwitzZeta.hurwitzEvenFEPair 0).f_modif := by
    change (HurwitzZeta.hurwitzEvenFEPair 0).symm.f_modif = _
    rw [HurwitzZeta.hurwitzEvenFEPair_zero_symm]
  have h := (HurwitzZeta.hurwitzEvenFEPair 0).hf_modif_FE x hx
  rw [hs] at h
  simpa only [HurwitzZeta.hurwitzEvenFEPair, one_mul, smul_eq_mul, Real.sqrt_eq_rpow] using h

/-- For `0 < x < 1`, inversion transfers the upper-side finite Gaussian
approximation and its error to the lower-side Mellin kernel. The explicit
factor `sqrt (1/x)` is retained for integration near zero. -/
theorem modified_theta_finite_error_below_one {x : ℝ} (hx : 0 < x) (hu : x < 1) (N : ℕ) :
    ‖(HurwitzZeta.hurwitzEvenFEPair 0).f_modif x -
          ((Real.sqrt (1 / x) *
                (2 * ∑ k ∈ Finset.range N, Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * (1 / x))) :
              ℝ) :
            ℂ)‖ ≤
      Real.sqrt (1 / x) * (4 * Real.exp (-Real.pi * ((N : ℝ) + 1) ^ 2 * (1 / x))) := by
  have hi : 1 < 1 / x := one_lt_one_div hx hu
  have hpos : 0 < 1 / x := one_div_pos.mpr hx
  have h := modified_theta_inversion hpos
  simp only [one_div, inv_inv] at h
  simp only [one_div] at ⊢ hi
  rw [h, Complex.ofReal_mul, ← mul_sub, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (modified_theta_finite_error hi N) (Real.sqrt_nonneg _)

/-- For `x > 1` and `Re s ≤ 2`, multiplying the finite theta approximation
error by the Mellin weight does not increase the uniform Gaussian bound.
This applies in particular to every critical-line ordinate. -/
theorem weighted_theta_finite_error {x : ℝ} (hx : 1 < x) {s : ℂ} (hs : s.re ≤ 2) (N : ℕ) :
    ‖(x : ℂ) ^ (s / 2 - 1) *
          ((HurwitzZeta.hurwitzEvenFEPair 0).f_modif x -
            ((2 * ∑ k ∈ Finset.range N, Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * x) : ℝ) : ℂ))‖ ≤
      4 * Real.exp (-Real.pi * ((N : ℝ) + 1) ^ 2 * x) := by
  have hx0 : 0 < x := by linarith only [hx]
  have he : (s / 2 - 1).re ≤ 0 := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    linarith only [hs]
  have hw : ‖(x : ℂ) ^ (s / 2 - 1)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hx.le he
  have hb := modified_theta_finite_error hx N
  calc
    _ =
        ‖(x : ℂ) ^ (s / 2 - 1)‖ *
          ‖(HurwitzZeta.hurwitzEvenFEPair 0).f_modif x -
              ((2 * ∑ k ∈ Finset.range N, Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * x) : ℝ) : ℂ)‖ :=
      norm_mul _ _
    _ ≤
        1 *
          ‖(HurwitzZeta.hurwitzEvenFEPair 0).f_modif x -
              ((2 * ∑ k ∈ Finset.range N, Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * x) : ℝ) : ℂ)‖ :=
      mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    _ ≤ _ := by linarith only [hb]

/-- The upper-tail integral of the Gaussian error majorant is explicit.
For any cutoff `A`, the exponential decay gives the displayed finite value;
this is the integrated budget used after truncating the theta series. -/
theorem gaussian_error_integral (N : ℕ) (A : ℝ) :
    (∫ x : ℝ in Set.Ioi A, 4 * Real.exp (-Real.pi * ((N : ℝ) + 1) ^ 2 * x)) =
      4 * Real.exp (-Real.pi * ((N : ℝ) + 1) ^ 2 * A) / (Real.pi * ((N : ℝ) + 1) ^ 2) := by
  have hn : 0 < (N : ℝ) + 1 := by positivity
  have ha : -Real.pi * ((N : ℝ) + 1) ^ 2 < 0 := by
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) (sq_pos_of_pos hn)
  rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi ha]
  simp only [neg_mul, neg_div_neg_eq, mul_div_assoc]

/-- On the upper Mellin half-line, the integral of the weighted theta
truncation error is bounded by an explicit exponential expression. The
result applies to `Re s ≤ 2` and every cutoff `A ≥ 1`. -/
theorem weighted_theta_integral_error {s : ℂ} (hs : s.re ≤ 2) {A : ℝ} (hA : 1 ≤ A) (N : ℕ) :
    ‖∫ x : ℝ in Set.Ioi A,
          (x : ℂ) ^ (s / 2 - 1) *
            ((HurwitzZeta.hurwitzEvenFEPair 0).f_modif x -
              ((2 * ∑ k ∈ Finset.range N, Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * x) : ℝ) : ℂ))‖ ≤
      4 * Real.exp (-Real.pi * ((N : ℝ) + 1) ^ 2 * A) / (Real.pi * ((N : ℝ) + 1) ^ 2) := by
  have hn : 0 < (N : ℝ) + 1 := by positivity
  have ha : -Real.pi * ((N : ℝ) + 1) ^ 2 < 0 := by
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) (sq_pos_of_pos hn)
  have hg := (integrableOn_exp_mul_Ioi ha A).const_mul 4
  have hb :=
    (MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Ioi).mono
      (fun x hx ↦ weighted_theta_finite_error (hA.trans_lt hx) hs N)
  have h := MeasureTheory.norm_integral_le_of_norm_le hg hb
  rw [gaussian_error_integral N A] at h
  exact h

/-- The upper tail of the modified-kernel Mellin integral is at most
`4 exp (-π A) / π` for `A ≥ 1` and `Re s ≤ 2`. Taking zero Gaussian terms
in the explicit truncation estimate supplies the cutoff budget. -/
theorem weighted_theta_integral_tail {s : ℂ} (hs : s.re ≤ 2) {A : ℝ} (hA : 1 ≤ A) :
    ‖∫ x : ℝ in Set.Ioi A, (x : ℂ) ^ (s / 2 - 1) * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x‖ ≤
      4 * Real.exp (-Real.pi * A) / Real.pi := by
  simpa only [Nat.cast_zero, zero_add, one_pow, mul_one, Finset.sum_range_zero, mul_zero,
    Complex.ofReal_zero, sub_zero] using weighted_theta_integral_error hs hA 0

end PseudoPrime.AnalyticNumberTheory.RiemannXi
