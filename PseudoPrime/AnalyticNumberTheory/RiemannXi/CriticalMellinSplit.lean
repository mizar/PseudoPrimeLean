/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.ThetaGaussianBounds
import all PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalLineMellin

/-! # Inversion and decomposition of the critical Mellin integral -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- Inversion transfers an integral on `(0,1)` to `(1,∞)` with Jacobian
`x⁻²`. The change-of-variables theorem applies to any complex-valued
integrand and does not require continuity assumptions. -/
theorem integral_lower_half_inversion (f : ℝ → ℂ) :
    (∫ y : ℝ in Set.Ioo 0 1, f y) = ∫ x : ℝ in Set.Ioi 1, (x⁻¹ ^ 2 : ℝ) • f x⁻¹ := by
  have himage : (fun x : ℝ ↦ x⁻¹) '' Set.Ioi 1 = Set.Ioo 0 1 := by
    rw [Set.image_inv_eq_inv, Set.inv_Ioi₀ (by norm_num only : (0 : ℝ) < 1)]
    norm_num only [inv_one]
  have hd :
    ∀ x ∈ Set.Ioi (1 : ℝ), HasDerivWithinAt (fun y : ℝ ↦ y⁻¹) (-(x⁻¹ ^ 2)) (Set.Ioi 1) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans (by norm_num only : (0 : ℝ) < 1) hx)
    simpa only [inv_pow] using (hasDerivAt_inv hx0).hasDerivWithinAt
  have hinj : Set.InjOn (fun x : ℝ ↦ x⁻¹) (Set.Ioi 1) := by
    intro x hx y hy h
    exact inv_injective h
  have h :=
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul (f := fun x : ℝ ↦ x⁻¹) (f' :=
      fun x : ℝ ↦ -(x⁻¹ ^ 2)) measurableSet_Ioi hd hinj f
  rw [himage] at h
  simpa only [abs_neg, abs_pow, sq_abs] using h

/-- An integrable positive-half-line function splits at one into its lower
open interval and upper half-line integrals. The singleton endpoint has
zero measure. -/
theorem integral_positive_split (f : ℝ → ℂ) (hf : MeasureTheory.IntegrableOn f (Set.Ioi 0)) :
    (∫ x : ℝ in Set.Ioi 0, f x) = (∫ x : ℝ in Set.Ioo 0 1, f x) + ∫ x : ℝ in Set.Ioi 1, f x := by
  have hsub : Set.Ioi (1 : ℝ) ⊆ Set.Ioi 0 := by
    intro x hx
    exact lt_trans (by norm_num only : (0 : ℝ) < 1) hx
  have h := intervalIntegral.integral_interval_add_Ioi hf (hf.mono_set hsub)
  rw [intervalIntegral.integral_of_le (by norm_num only : (0 : ℝ) ≤ 1),
    MeasureTheory.integral_Ioc_eq_integral_Ioo] at h
  exact h.symm

/-- The inversion Jacobian, Mellin weight and theta functional equation
combine into the reflected Mellin weight at `1 - s`. The identity is valid
pointwise for positive integration variables. -/
theorem theta_mellin_inversion_integrand {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x⁻¹ ^ 2 : ℝ) • ((x⁻¹ : ℂ) ^ (s / 2 - 1) * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x⁻¹) =
      (x : ℂ) ^ ((1 - s) / 2 - 1) * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x := by
  have hn : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hi := modified_theta_inversion hx
  simp only [one_div] at hi
  have hroot : (Real.sqrt x : ℂ) = (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx.le]
  have hinv : ((x⁻¹ ^ 2 : ℝ) : ℂ) = (x : ℂ) ^ (-(2 : ℂ)) := by
    simp only [Complex.ofReal_pow, Complex.ofReal_inv, Complex.cpow_neg,
      show (2 : ℂ) = ((2 : ℕ) : ℂ) from rfl, Complex.cpow_natCast, inv_pow]
  rw [hi, Complex.real_smul, hinv, hroot, Complex.inv_cpow_ofReal_nonneg hx.le, ← Complex.cpow_neg]
  have he : (-(2 : ℂ)) + (-(s / 2 - 1)) + ((1 / 2 : ℝ) : ℂ) = (1 - s) / 2 - 1 := by
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  simp only [← mul_assoc]
  rw [← Complex.cpow_add _ _ hn, ← Complex.cpow_add _ _ hn, he]

/-- The lower part of the regularized completed-zeta Mellin integral equals
the upper part with reflected parameter `1 - s`. This combines the general
inversion substitution with the modified theta functional equation. -/
theorem theta_mellin_lower_eq_reflected (s : ℂ) :
    (∫ y : ℝ in Set.Ioo 0 1, (y : ℂ) ^ (s / 2 - 1) * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif y) =
      ∫ x : ℝ in Set.Ioi 1,
        (x : ℂ) ^ ((1 - s) / 2 - 1) * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x := by
  rw [integral_lower_half_inversion]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simpa only [Complex.ofReal_inv] using
    theta_mellin_inversion_integrand (lt_trans (by norm_num only : (0 : ℝ) < 1) hx) s

/-- At every complex argument the regularized completed zeta equals one half
of the sum of two upper-half-line theta Mellin integrals, at `s` and `1-s`.
The positive-half-line integral converges absolutely, and the lower half is
transferred by inversion. This representation is the basis for finite
critical-line sign certificates. -/
theorem completed_zeta_zero_upper_mellin (s : ℂ) :
    completedRiemannZeta₀ s =
      ((∫ x : ℝ in Set.Ioi 1, (x : ℂ) ^ (s / 2 - 1) * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x) +
          (∫ x : ℝ in Set.Ioi 1,
            (x : ℂ) ^ ((1 - s) / 2 - 1) * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x)) /
        2 := by
  let f : ℝ → ℂ := fun x ↦ (x : ℂ) ^ (s / 2 - 1) * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x
  have hf : MeasureTheory.IntegrableOn f (Set.Ioi 0) := by
    simpa only [f, MellinConvergent, smul_eq_mul] using completed_zeta_mellin_convergent s
  have hsplit := integral_positive_split f hf
  have hlow := theta_mellin_lower_eq_reflected s
  rw [completed_zeta_zero_eq_mellin, mellin]
  change (∫ x : ℝ in Set.Ioi 0, f x) / 2 = _
  rw [hsplit]
  dsimp only [f]
  rw [hlow, add_comm]

/-- The first `N` positive Gaussian terms of the modified theta kernel,
weighted by the Mellin factor at `s`. Its integral is the finite-sum part
of the critical-line endpoint approximation. -/
noncomputable def thetaMellinFinite (s : ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (s / 2 - 1) *
    ((2 * ∑ k ∈ Finset.range N, Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * x) : ℝ) : ℂ)

/-- The finite Gaussian Mellin approximation is continuous on the positive
half-line. Each Gaussian term is continuous and the complex power is
continuous away from the nonpositive real axis. -/
theorem theta_mellin_finite_continuous (s : ℂ) (N : ℕ) :
    ContinuousOn (thetaMellinFinite s N) (Set.Ioi 0) := by
  have hw : ContinuousOn (fun x : ℝ ↦ (x : ℂ) ^ (s / 2 - 1)) (Set.Ioi 0) :=
    Complex.continuous_ofReal.continuousOn.cpow_const
      (fun x hx ↦ Complex.ofReal_mem_slitPlane.mpr hx)
  have hg :
    Continuous
      (fun x : ℝ ↦ 2 * ∑ k ∈ Finset.range N, Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * x)) := by
    apply continuous_const.mul
    apply continuous_finsetSum
    intro k hk
    exact Real.continuous_exp.comp (continuous_const.mul continuous_id)
  exact hw.mul (Complex.continuous_ofReal.comp_continuousOn hg.continuousOn)

/-- On `x > 1` and `Re s ≤ 2`, the finite Gaussian Mellin approximation is
bounded by `2N exp (-πx)`. Each finite summand is dominated by the first
Gaussian, and the Mellin weight has norm at most one. -/
theorem theta_mellin_finite_bound {s : ℂ} (hs : s.re ≤ 2) (N : ℕ) {x : ℝ} (hx : 1 < x) :
    ‖thetaMellinFinite s N x‖ ≤ 2 * N * Real.exp (-Real.pi * x) := by
  have hx0 : 0 < x := lt_trans (by norm_num only : (0 : ℝ) < 1) hx
  have he : (s / 2 - 1).re ≤ 0 := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    linarith only [hs]
  have hw : ‖(x : ℂ) ^ (s / 2 - 1)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hx.le he
  have hterm :
    ∀ k ∈ Finset.range N,
      Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * x) ≤ Real.exp (-Real.pi * x) := by
    intro k hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hk1 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith only [hk0, sq_nonneg (k : ℝ)]
    have hm := mul_le_mul_of_nonneg_left hk1 (mul_nonneg Real.pi_pos.le hx0.le)
    apply Real.exp_le_exp.mpr
    nlinarith only [hm]
  have hsum :
    (∑ k ∈ Finset.range N, Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * x)) ≤
      N * Real.exp (-Real.pi * x) := by
    calc
      _ ≤ ∑ k ∈ Finset.range N, Real.exp (-Real.pi * x) := Finset.sum_le_sum hterm
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hnon : 0 ≤ (2 : ℝ) * ∑ k ∈ Finset.range N, Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * x) := by
    apply mul_nonneg (by norm_num only)
    exact Finset.sum_nonneg (fun k hk ↦ (Real.exp_pos _).le)
  rw [thetaMellinFinite, norm_mul, Complex.norm_real, Real.norm_of_nonneg hnon]
  have hh := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 2 by norm_num only)
  have hmul := mul_le_mul_of_nonneg_right hw hnon
  nlinarith only [hh, hmul]

/-- The finite Gaussian Mellin approximation is integrable on every upper
half-line starting at `A ≥ 1` when `Re s ≤ 2`. The bound by an integrable
exponential supplies absolute convergence. -/
theorem theta_mellin_finite_integrable {s : ℂ} (hs : s.re ≤ 2) {A : ℝ} (hA : 1 ≤ A) (N : ℕ) :
    MeasureTheory.IntegrableOn (thetaMellinFinite s N) (Set.Ioi A) := by
  have hsub : Set.Ioi A ⊆ Set.Ioi 0 := by
    intro x hx
    exact lt_trans (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) hA) hx
  have hc := (theta_mellin_finite_continuous s N).mono hsub
  have hg := (integrableOn_exp_mul_Ioi (neg_neg_of_pos Real.pi_pos) A).const_mul (2 * N : ℝ)
  apply hg.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Ioi] with
    x hx
  exact theta_mellin_finite_bound hs N (hA.trans_lt hx)

/-- The tail of the finite Gaussian Mellin approximation beyond `A ≥ 1`
is at most `2N exp (-πA) / π`. The explicit exponential majorant is
integrable and holds uniformly when `Re s ≤ 2`. -/
theorem theta_mellin_finite_tail {s : ℂ} (hs : s.re ≤ 2) {A : ℝ} (hA : 1 ≤ A) (N : ℕ) :
    ‖∫ x : ℝ in Set.Ioi A, thetaMellinFinite s N x‖ ≤
      2 * N * Real.exp (-Real.pi * A) / Real.pi := by
  have hp : -Real.pi < 0 := neg_neg_of_pos Real.pi_pos
  have hg := (integrableOn_exp_mul_Ioi hp A).const_mul (2 * N : ℝ)
  have hb :=
    (MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Ioi).mono
      (fun x hx ↦ theta_mellin_finite_bound hs N (hA.trans_lt hx))
  have h := MeasureTheory.norm_integral_le_of_norm_le hg hb
  rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi hp] at h
  simpa only [neg_div_neg_eq, ← mul_div_assoc] using h

/-- Truncating the finite Gaussian Mellin integral to `[1,A]` incurs at most
`2N exp (-πA) / π`. Absolute convergence justifies subtracting the finite
interval integral from the upper-half-line integral. -/
theorem theta_mellin_finite_interval_error {s : ℂ} (hs : s.re ≤ 2) {A : ℝ} (hA : 1 ≤ A) (N : ℕ) :
    ‖(∫ x : ℝ in Set.Ioi 1, thetaMellinFinite s N x) -
          ∫ x : ℝ in (1 : ℝ)..A, thetaMellinFinite s N x‖ ≤
      2 * N * Real.exp (-Real.pi * A) / Real.pi := by
  have h1 := theta_mellin_finite_integrable hs (by norm_num only : (1 : ℝ) ≤ 1) N
  have hA' := theta_mellin_finite_integrable hs hA N
  have he := intervalIntegral.integral_interval_add_Ioi h1 hA'
  have heq :
    (∫ x : ℝ in Set.Ioi 1, thetaMellinFinite s N x) -
        (∫ x : ℝ in (1 : ℝ)..A, thetaMellinFinite s N x) =
      ∫ x : ℝ in Set.Ioi A, thetaMellinFinite s N x := by
    rw [← he]
    abel
  rw [heq]
  exact theta_mellin_finite_tail hs hA N

/-- Replacing the upper modified-theta Mellin integral by its finite
Gaussian approximation incurs the explicit integrated tail error. Both
integrals converge absolutely on the stated half-line. -/
theorem upper_mellin_finite_error {s : ℂ} (hs : s.re ≤ 2) {A : ℝ} (hA : 1 ≤ A) (N : ℕ) :
    ‖(∫ x : ℝ in Set.Ioi A, (x : ℂ) ^ (s / 2 - 1) * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x) -
          (∫ x : ℝ in Set.Ioi A, thetaMellinFinite s N x)‖ ≤
      4 * Real.exp (-Real.pi * ((N : ℝ) + 1) ^ 2 * A) / (Real.pi * ((N : ℝ) + 1) ^ 2) := by
  have hsub : Set.Ioi A ⊆ Set.Ioi 0 := by
    intro x hx
    exact lt_trans (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) hA) hx
  have hf :
    MeasureTheory.IntegrableOn
      (fun x : ℝ ↦ (x : ℂ) ^ (s / 2 - 1) * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x)
      (Set.Ioi A) := by
    apply MeasureTheory.IntegrableOn.mono_set _ hsub
    simpa only [MellinConvergent, smul_eq_mul] using completed_zeta_mellin_convergent s
  have hg := theta_mellin_finite_integrable hs hA N
  rw [← MeasureTheory.integral_sub hf hg]
  simpa only [thetaMellinFinite, mul_sub] using weighted_theta_integral_error hs hA N

/-- In the strip `-1 ≤ Re s ≤ 2`, the regularized completed zeta is
approximated by the two reflected finite Gaussian Mellin integrals with an
explicit exponential error. The same bound applies on the critical line. -/
theorem completed_zeta_finite_mellin_error {s : ℂ} (hl : -1 ≤ s.re) (hu : s.re ≤ 2) (N : ℕ) :
    ‖completedRiemannZeta₀ s -
          ((∫ x : ℝ in Set.Ioi 1, thetaMellinFinite s N x) +
              (∫ x : ℝ in Set.Ioi 1, thetaMellinFinite (1 - s) N x)) /
            2‖ ≤
      4 * Real.exp (-Real.pi * ((N : ℝ) + 1) ^ 2) / (Real.pi * ((N : ℝ) + 1) ^ 2) := by
  have hs : (1 - s).re ≤ 2 := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith only [hl]
  have h1 := upper_mellin_finite_error hu (by norm_num only : (1 : ℝ) ≤ 1) N
  have h2 := upper_mellin_finite_error hs (by norm_num only : (1 : ℝ) ≤ 1) N
  have ht :=
    norm_add_le
      ((∫ x : ℝ in Set.Ioi 1, (x : ℂ) ^ (s / 2 - 1) * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x) -
        (∫ x : ℝ in Set.Ioi 1, thetaMellinFinite s N x))
      ((∫ x : ℝ in Set.Ioi 1,
          (x : ℂ) ^ ((1 - s) / 2 - 1) * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x) -
        (∫ x : ℝ in Set.Ioi 1, thetaMellinFinite (1 - s) N x))
  rw [completed_zeta_zero_upper_mellin]
  have he :
    ((∫ x : ℝ in Set.Ioi 1, (x : ℂ) ^ (s / 2 - 1) * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x) +
            (∫ x : ℝ in Set.Ioi 1,
              (x : ℂ) ^ ((1 - s) / 2 - 1) * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x)) /
          2 -
        ((∫ x : ℝ in Set.Ioi 1, thetaMellinFinite s N x) +
            (∫ x : ℝ in Set.Ioi 1, thetaMellinFinite (1 - s) N x)) /
          2 =
      (((∫ x : ℝ in Set.Ioi 1,
              (x : ℂ) ^ (s / 2 - 1) * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x) -
            (∫ x : ℝ in Set.Ioi 1, thetaMellinFinite s N x)) +
          ((∫ x : ℝ in Set.Ioi 1,
              (x : ℂ) ^ ((1 - s) / 2 - 1) * (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x) -
            (∫ x : ℝ in Set.Ioi 1, thetaMellinFinite (1 - s) N x))) /
        2 := by
    ring
  rw [he, norm_div]
  simp only [mul_one] at h1 h2
  rw [Complex.norm_ofNat]
  nlinarith only [h1, h2, ht]

/-- In the strip `-1 ≤ Re s ≤ 2`, two finite Gaussian Mellin integrals over
`[1,A]` approximate regularized completed zeta with separate explicit
series and upper-tail errors. The formula reduces a critical-line sign check
to finitely many integrals on a compact interval. -/
theorem completed_zeta_finite_interval_error {s : ℂ} (hl : -1 ≤ s.re) (hu : s.re ≤ 2) {A : ℝ}
    (hA : 1 ≤ A) (N : ℕ) :
    ‖completedRiemannZeta₀ s -
          ((∫ x : ℝ in (1 : ℝ)..A, thetaMellinFinite s N x) +
              (∫ x : ℝ in (1 : ℝ)..A, thetaMellinFinite (1 - s) N x)) /
            2‖ ≤
      4 * Real.exp (-Real.pi * ((N : ℝ) + 1) ^ 2) / (Real.pi * ((N : ℝ) + 1) ^ 2) +
        2 * N * Real.exp (-Real.pi * A) / Real.pi := by
  let f1 : ℂ := ∫ x : ℝ in Set.Ioi 1, thetaMellinFinite s N x
  let f2 : ℂ := ∫ x : ℝ in Set.Ioi 1, thetaMellinFinite (1 - s) N x
  let g1 : ℂ := ∫ x : ℝ in (1 : ℝ)..A, thetaMellinFinite s N x
  let g2 : ℂ := ∫ x : ℝ in (1 : ℝ)..A, thetaMellinFinite (1 - s) N x
  have hs : (1 - s).re ≤ 2 := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith only [hl]
  have h0 := completed_zeta_finite_mellin_error hl hu N
  change ‖completedRiemannZeta₀ s - (f1 + f2) / 2‖ ≤ _ at h0
  have h1 := theta_mellin_finite_interval_error hu hA N
  have h2 := theta_mellin_finite_interval_error hs hA N
  change ‖f1 - g1‖ ≤ _ at h1
  change ‖f2 - g2‖ ≤ _ at h2
  have hm := norm_add_le (f1 - g1) (f2 - g2)
  have he : (f1 + f2) / 2 - (g1 + g2) / 2 = ((f1 - g1) + (f2 - g2)) / 2 := by ring
  have hmid : ‖(f1 + f2) / 2 - (g1 + g2) / 2‖ ≤ 2 * N * Real.exp (-Real.pi * A) / Real.pi := by
    rw [he, norm_div, Complex.norm_ofNat]
    nlinarith only [hm, h1, h2]
  have ht := norm_add_le (completedRiemannZeta₀ s - (f1 + f2) / 2) ((f1 + f2) / 2 - (g1 + g2) / 2)
  have he' :
    completedRiemannZeta₀ s - (f1 + f2) / 2 + ((f1 + f2) / 2 - (g1 + g2) / 2) =
      completedRiemannZeta₀ s - (g1 + g2) / 2 := by
    ring
  rw [he'] at ht
  change ‖completedRiemannZeta₀ s - (g1 + g2) / 2‖ ≤ _
  linarith only [ht, h0, hmid]

/-- The real part of the finite reflected Gaussian Mellin approximation at
critical-line height `t`, with `N` terms and integration cutoff `A`. -/
noncomputable def criticalCompletedFinite (t : ℝ) (N : ℕ) (A : ℝ) : ℝ :=
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  (((∫ x : ℝ in (1 : ℝ)..A, thetaMellinFinite s N x) +
        (∫ x : ℝ in (1 : ℝ)..A, thetaMellinFinite (1 - s) N x)) /
      2).re

/-- The explicit sum of the Gaussian-series and upper-integral tail bounds
for the finite Mellin approximation with parameters `N` and `A`. -/
noncomputable def criticalMellinError (N : ℕ) (A : ℝ) : ℝ :=
  4 * Real.exp (-Real.pi * ((N : ℝ) + 1) ^ 2) / (Real.pi * ((N : ℝ) + 1) ^ 2) +
    2 * N * Real.exp (-Real.pi * A) / Real.pi

/-- The finite reflected Gaussian integrals approximate the real part of
regularized completed zeta at every critical-line height within the explicit
error budget. Taking real parts cannot increase the complex norm. -/
theorem critical_completed_finite_error (t : ℝ) {A : ℝ} (hA : 1 ≤ A) (N : ℕ) :
    |criticalCompletedZeta t - criticalCompletedFinite t N A| ≤ criticalMellinError N A := by
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  have hre : s.re = 1 / 2 := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hl : -1 ≤ s.re := by linarith only [hre]
  have hu : s.re ≤ 2 := by linarith only [hre]
  have h := completed_zeta_finite_interval_error hl hu hA N
  have hr :=
    Complex.abs_re_le_norm
      (completedRiemannZeta₀ s -
        ((∫ x : ℝ in (1 : ℝ)..A, thetaMellinFinite s N x) +
            (∫ x : ℝ in (1 : ℝ)..A, thetaMellinFinite (1 - s) N x)) /
          2)
  change |criticalCompletedZeta t - criticalCompletedFinite t N A| ≤ criticalMellinError N A
  dsimp only [criticalCompletedZeta, criticalCompletedFinite, criticalMellinError]
  simpa only [s, Complex.sub_re] using hr.trans h

/-- A strict upper bound from the finite Mellin approximation proves that
xi is positive at the critical-line height `t`. The hypotheses involve only
the compact finite integrals and their explicit error budget. -/
theorem critical_xi_positive_of_finite {t A : ℝ} (hA : 1 ≤ A) (N : ℕ)
    (h : (t ^ 2 + 1 / 4) * (criticalCompletedFinite t N A + criticalMellinError N A) < 1) :
    0 < (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by
  apply (xi_critical_pos_iff t).2
  have he := (abs_le.mp (critical_completed_finite_error t hA N)).2
  have hp : 0 ≤ t ^ 2 + 1 / 4 := by nlinarith only [sq_nonneg t]
  have hm :=
    mul_le_mul_of_nonneg_left
      (show criticalCompletedZeta t ≤ criticalCompletedFinite t N A + criticalMellinError N A by
        linarith only [he])
      hp
  exact hm.trans_lt h

/-- A strict lower bound from the finite Mellin approximation proves that
xi is negative at the critical-line height `t`. The bound retains the full
two-sided analytic error from the finite Gaussian approximation. -/
theorem critical_xi_negative_of_finite {t A : ℝ} (hA : 1 ≤ A) (N : ℕ)
    (h : 1 < (t ^ 2 + 1 / 4) * (criticalCompletedFinite t N A - criticalMellinError N A)) :
    (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re < 0 := by
  apply (xi_critical_neg_iff t).2
  have he := (abs_le.mp (critical_completed_finite_error t hA N)).1
  have hp : 0 ≤ t ^ 2 + 1 / 4 := by nlinarith only [sq_nonneg t]
  have hm :=
    mul_le_mul_of_nonneg_left
      (show criticalCompletedFinite t N A - criticalMellinError N A ≤ criticalCompletedZeta t by
        linarith only [he])
      hp
  exact h.trans_le hm

end PseudoPrime.AnalyticNumberTheory.RiemannXi
