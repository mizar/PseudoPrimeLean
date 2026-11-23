/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalMellinSplit
public import PseudoPrime.Analysis.TaylorQuadrature
public import PseudoPrime.Analysis.ComplexCpowDerivatives
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalMellinNumerics
import all PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalMellinSplit

/-! # High-order quadrature for finite theta Mellin integrals -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- For a complex analytic function on an open set, iterated real
derivatives along the real axis equal its complex iterated derivatives.
This transfers complex Cauchy derivative estimates to real quadrature. -/
theorem real_iteratedDeriv_eq_complex {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : AnalyticOnNhd ℂ F U) {x : ℝ} (hx : (x : ℂ) ∈ U) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ ↦ F (y : ℂ)) x = iteratedDeriv n F (x : ℂ) := by
  induction n generalizing x with
  | zero => rfl
  | succ n
    ih =>
    have hneigh : Filter.Eventually (fun y : ℝ ↦ (y : ℂ) ∈ U) (nhds x) :=
      (hU.preimage Complex.continuous_ofReal).mem_nhds hx
    have heq :
      Filter.EventuallyEq (nhds x) (iteratedDeriv n (fun y : ℝ ↦ F (y : ℂ)))
        (fun y : ℝ ↦ iteratedDeriv n F (y : ℂ)) :=
      hneigh.mono (fun y hy ↦ ih hy)
    have han := (hF (x : ℂ) hx).iterated_deriv n
    have hd := han.differentiableAt.hasDerivAt.comp_ofReal
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    rw [heq.deriv_eq]
    simpa only [iteratedDeriv_eq_iterate] using hd.deriv

/-- A complex Cauchy estimate bounds the real within-derivative on a
nondegenerate interval. The closed complex disc lies in an analytic domain,
and the supplied sphere bound controls the derivative needed by quadrature. -/
theorem real_within_deriv_le_cauchy {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : AnalyticOnNhd ℂ F U) {a b y R M : ℝ} (hab : a < b) (hy : y ∈ Set.Icc a b) (hR : 0 < R)
    (hball : Metric.closedBall (y : ℂ) R ⊆ U) (hM : ∀ z ∈ Metric.sphere (y : ℂ) R, ‖F z‖ ≤ M)
    (n : ℕ) :
    ‖iteratedDerivWithin n (fun x : ℝ ↦ F (x : ℂ)) (Set.Icc a b) y‖ ≤ n.factorial * M / R ^ n := by
  have hyU : (y : ℂ) ∈ U := hball (Metric.mem_closedBall_self hR.le)
  have hr : AnalyticAt ℝ (fun x : ℝ ↦ F (x : ℂ)) y :=
    (hF (y : ℂ) hyU).restrictScalars.comp (Complex.ofRealCLM.analyticAt y)
  have hd : DifferentiableOn ℂ F (Metric.closedBall (y : ℂ) R) := fun z hz ↦
    (hF z (hball hz)).differentiableAt.differentiableWithinAt
  have hc : ContinuousOn F (Metric.closedBall (y : ℂ) R) := fun z hz ↦
    (hF z (hball hz)).continuousAt.continuousWithinAt
  have hderiv :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR
      (DiffContOnCl.mk_ball (hd.mono Metric.ball_subset_closedBall) hc) hM
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) hr.contDiffAt hy,
    real_iteratedDeriv_eq_complex hU hF hyU]
  exact hderiv

/-- The holomorphic extension of the finite theta Mellin integrand to the
right half-plane. It replaces each real Gaussian by its complex exponential
and is used for uniform Cauchy bounds on quadrature derivatives. -/
noncomputable def thetaMellinComplex (s : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  z ^ (s / 2 - 1) *
    (2 * ∑ k ∈ Finset.range N, Complex.exp (((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) * z))

/-- On the real axis the complex extension agrees with the finite real
theta Mellin integrand. The identity uses only preservation of finite sums
and the exponential by the real-to-complex embedding. -/
theorem theta_mellin_complex_of_real (s : ℂ) (N : ℕ) (x : ℝ) :
    thetaMellinComplex s N (x : ℂ) = thetaMellinFinite s N x := by
  simp only [thetaMellinComplex, thetaMellinFinite, Complex.ofReal_mul, Complex.ofReal_sum,
    Complex.ofReal_ofNat, Complex.ofReal_exp]

/-- The finite complex theta Mellin extension is holomorphic on the open
right half-plane. The power factor is analytic there, and the Gaussian
exponential sum is entire. -/
theorem theta_mellin_complex_analytic (s : ℂ) (N : ℕ) :
    AnalyticOnNhd ℂ (thetaMellinComplex s N) {z : ℂ | 0 < z.re} := by
  intro z hz
  have hw : AnalyticAt ℂ (fun w : ℂ ↦ w ^ (s / 2 - 1)) z :=
    analyticAt_id.cpow analyticAt_const (Complex.mem_slitPlane_iff.mpr (Or.inl hz))
  have hg :
    AnalyticAt ℂ
      (fun w : ℂ ↦
        2 * ∑ k ∈ Finset.range N, Complex.exp (((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) * w))
      z := by
    apply analyticAt_const.mul
    have hh :
      AnalyticAt ℂ
        (∑ k ∈ Finset.range N, fun w : ℂ ↦
          Complex.exp (((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) * w))
        z := by
      apply Finset.analyticAt_sum
      intro k hk
      exact (analyticAt_const.mul analyticAt_id).cexp'
    convert hh using 1
    ext w
    simp only [Finset.sum_apply]
  exact hw.mul hg

/-- An explicit finite sum for every derivative of the holomorphic finite
theta Mellin integrand on the right half-plane. This expands the coefficients
used by the composite Taylor quadrature without referring to a table. -/
theorem theta_mellin_complex_deriv (s : ℂ) (N n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    iteratedDeriv n (thetaMellinComplex s N) z =
      2 *
        ∑ k ∈ Finset.range N,
          ∑ j ∈ Finset.range (n + 1),
            (n.choose j : ℂ) *
              (PseudoPrime.Analysis.complexFalling (s / 2 - 1) j * z ^ (s / 2 - 1 - j)) *
              ((((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) ^ (n - j)) *
                Complex.exp (((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) * z)) := by
  have hslit : z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hz)
  have hterm :
    ∀ k ∈ Finset.range N,
      ContDiffAt ℂ n
        (fun u : ℂ ↦ u ^ (s / 2 - 1) * Complex.exp (((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) * u))
        z := by
    intro k hk
    exact
      ((analyticAt_id.cpow analyticAt_const hslit).mul
          (analyticAt_const.mul analyticAt_id).cexp').contDiffAt
  have heq :
    thetaMellinComplex s N = fun u : ℂ ↦
      2 *
        ∑ k ∈ Finset.range N,
          u ^ (s / 2 - 1) * Complex.exp (((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) * u) := by
    funext u
    simp only [thetaMellinComplex, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i hi ↦ mul_left_comm _ _ _)
  rw [heq, iteratedDeriv_const_mul_field, iteratedDeriv_fun_sum hterm]
  apply congrArg (fun a : ℂ ↦ 2 * a)
  apply Finset.sum_congr rfl
  intro k hk
  exact PseudoPrime.Analysis.iteratedDeriv_cpow_exp _ _ n hslit

/-- The real-axis derivatives used by Taylor quadrature equal the explicit
finite complex sum for the holomorphic extension. Positivity of the node
places it in the right half-plane, where the two derivatives agree. -/
theorem theta_mellin_real_deriv (s : ℂ) (N n : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n (thetaMellinFinite s N) x =
      2 *
        ∑ k ∈ Finset.range N,
          ∑ j ∈ Finset.range (n + 1),
            (n.choose j : ℂ) *
              (PseudoPrime.Analysis.complexFalling (s / 2 - 1) j * (x : ℂ) ^ (s / 2 - 1 - j)) *
              ((((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) ^ (n - j)) *
                Complex.exp (((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) * x)) := by
  have heq : (fun y : ℝ ↦ thetaMellinComplex s N (y : ℂ)) = thetaMellinFinite s N := by
    funext y
    exact theta_mellin_complex_of_real s N y
  rw [← heq,
    real_iteratedDeriv_eq_complex (isOpen_lt continuous_const Complex.continuous_re)
      (theta_mellin_complex_analytic s N)
      (by simpa only [Set.mem_ofPred_eq, Complex.ofReal_re] using hx)]
  exact theta_mellin_complex_deriv s N n (by simpa only [Complex.ofReal_re] using hx)

/-- On the closed right half-plane, the norm of the finite holomorphic
Mellin extension is at most `2N` times the norm of its power factor. Every
Gaussian exponential has norm at most one there. -/
theorem theta_mellin_complex_norm_le (s : ℂ) (N : ℕ) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖thetaMellinComplex s N z‖ ≤ 2 * N * ‖z ^ (s / 2 - 1)‖ := by
  have hterm :
    ∀ k ∈ Finset.range N, ‖Complex.exp (((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) * z)‖ ≤ 1 := by
    intro k hk
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) (sq_nonneg _)) hz
  have hsum :
    ‖∑ k ∈ Finset.range N, Complex.exp (((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) * z)‖ ≤ N := by
    calc
      _ ≤ ∑ k ∈ Finset.range N, ‖Complex.exp (((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) * z)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range N, (1 : ℝ) := Finset.sum_le_sum hterm
      _ = N := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [thetaMellinComplex, norm_mul, norm_mul, Complex.norm_ofNat]
  have hm := mul_le_mul_of_nonneg_left hsum (by norm_num only : (0 : ℝ) ≤ 2)
  have hn := mul_le_mul_of_nonneg_left hm (norm_nonneg (z ^ (s / 2 - 1)))
  nlinarith only [hn]

/-- If `‖z‖ ≥ 1/2` and `Re w = -3/4`, the norm of `z^w` is bounded by
`2 exp (π B)` whenever `|Im w| ≤ B`. The principal argument is at most π
in absolute value; the radial factor is bounded separately on either side
of unit modulus. -/
theorem critical_power_norm_le {z w : ℂ} {B : ℝ} (hz : (1 / 2 : ℝ) ≤ ‖z‖) (hw : w.re = -(3 / 4 : ℝ))
    (hB : |w.im| ≤ B) : ‖z ^ w‖ ≤ 2 * Real.exp (Real.pi * B) := by
  have hz0 : 0 < ‖z‖ := by linarith only [hz]
  have hr : ‖z‖ ^ w.re ≤ (2 : ℝ) := by
    rw [hw]
    by_cases h : (1 : ℝ) ≤ ‖z‖
    · have h1 := Real.rpow_le_one_of_one_le_of_nonpos h (by norm_num only : -(3 / 4 : ℝ) ≤ 0)
      linarith only [h1]
    · have h1 : ‖z‖ ≤ 1 := le_of_not_ge h
      have h2 :=
        Real.rpow_le_rpow_of_exponent_ge hz0 h1 (show (-1 : ℝ) ≤ -(3 / 4 : ℝ) by norm_num only)
      rw [Real.rpow_neg_one] at h2
      have h3 : ‖z‖⁻¹ ≤ 2 := by
        rw [inv_eq_one_div]
        apply (div_le_iff₀ hz0).2
        linarith only [hz]
      exact h2.trans h3
  have ha : |Complex.arg z * w.im| ≤ Real.pi * B := by
    rw [abs_mul]
    exact mul_le_mul (Complex.abs_arg_le_pi z) hB (abs_nonneg _) Real.pi_pos.le
  have he : Real.exp (-(Complex.arg z * w.im)) ≤ Real.exp (Real.pi * B) := by
    apply Real.exp_le_exp.mpr
    linarith only [(abs_le.mp ha).1]
  have hnorm := Complex.norm_cpow_le z w
  rw [div_eq_mul_inv, ← Real.exp_neg] at hnorm
  have hm := mul_le_mul hr he (Real.exp_pos _).le (by norm_num only : (0 : ℝ) ≤ 2)
  exact hnorm.trans hm

/-- A circle of radius `1/2` around a real center at least one stays in the
right half-plane and outside the open disc of radius `1/2` about zero. These
two bounds make the Gaussian and complex-power estimates applicable. -/
theorem positive_circle_geometry {y : ℝ} (hy : 1 ≤ y) {z : ℂ}
    (hz : z ∈ Metric.sphere (y : ℂ) (1 / 2)) : (1 / 2 : ℝ) ≤ z.re ∧ (1 / 2 : ℝ) ≤ ‖z‖ := by
  have hd : ‖z - (y : ℂ)‖ = 1 / 2 := by simpa only [Metric.mem_sphere, dist_eq_norm] using hz
  have hr := (Complex.abs_re_le_norm (z - (y : ℂ))).trans_eq hd
  simp only [Complex.sub_re, Complex.ofReal_re] at hr
  have hl := (abs_le.mp hr).1
  have hre : (1 / 2 : ℝ) ≤ z.re := by linarith only [hl, hy]
  exact ⟨hre, hre.trans ((le_abs_self z.re).trans (Complex.abs_re_le_norm z))⟩

/-- For `Re s = 1/2`, `|Im s| ≤ 100`, and eight Gaussian terms, the norm
of the complex Mellin extension on any radius-`1/2` circle centered at a
real point at least one is at most `32 exp (50π)`. -/
theorem theta_mellin_critical_sphere_bound {s z : ℂ} {y : ℝ} (hs : s.re = 1 / 2) (ht : |s.im| ≤ 100)
    (hy : 1 ≤ y) (hz : z ∈ Metric.sphere (y : ℂ) (1 / 2)) :
    ‖thetaMellinComplex s 8 z‖ ≤ 32 * Real.exp (50 * Real.pi) := by
  have hg := positive_circle_geometry hy hz
  have hwr : (s / 2 - 1).re = -(3 / 4 : ℝ) := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    linarith only [hs]
  have hwi : |(s / 2 - 1).im| ≤ 50 := by
    simp only [Complex.sub_im, Complex.div_ofNat_im, Complex.one_im, sub_zero, abs_div,
      abs_of_pos (by norm_num only : (0 : ℝ) < 2)]
    linarith only [ht]
  have hp := critical_power_norm_le hg.2 hwr hwi
  have hn := theta_mellin_complex_norm_le s 8 (show 0 ≤ z.re by linarith only [hg.1])
  simp only [mul_comm Real.pi 50] at hp
  norm_num only [Nat.cast_ofNat] at hn
  nlinarith only [hn, hp]

/-- A rational upper bound for the uniform critical-line sphere majorant.
The estimate follows from `π < 4`, `exp 1 < 3`, and exact integer powers. -/
theorem critical_sphere_majorant_rational : 32 * Real.exp (50 * Real.pi) ≤ (10 : ℝ) ^ 100 := by
  have h1 : Real.exp (50 * Real.pi) ≤ Real.exp 200 := by
    apply Real.exp_le_exp.mpr
    linarith only [Real.pi_lt_four]
  have h2 : Real.exp (200 : ℝ) = Real.exp 1 ^ 200 := by
    rw [← Real.exp_natCast_mul]
    congr 1
    norm_num only
  have h3 : Real.exp 1 ^ 200 ≤ (3 : ℝ) ^ 200 :=
    pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le 200
  have h4 : (32 : ℝ) * 3 ^ 200 ≤ 10 ^ 100 := by norm_num only
  have hm := mul_le_mul_of_nonneg_left ((h1.trans_eq h2).trans h3) (by norm_num only : (0 : ℝ) ≤ 32)
  exact hm.trans h4

/-- A sphere bound for the holomorphic finite Mellin extension gives the
real within-derivative bound needed on a positive quadrature cell. If
`R < a`, every closed disc centered on the cell stays in the right half-plane. -/
theorem theta_mellin_deriv_le_cauchy (s : ℂ) (N n : ℕ) {a b y R M : ℝ} (ha : 0 < R) (hRa : R < a)
    (hab : a < b) (hy : y ∈ Set.Icc a b)
    (hM : ∀ z ∈ Metric.sphere (y : ℂ) R, ‖thetaMellinComplex s N z‖ ≤ M) :
    ‖iteratedDerivWithin n (thetaMellinFinite s N) (Set.Icc a b) y‖ ≤ n.factorial * M / R ^ n := by
  have hball : Metric.closedBall (y : ℂ) R ⊆ {z : ℂ | 0 < z.re} := by
    intro z hz
    have hd : ‖z - (y : ℂ)‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hr := (Complex.abs_re_le_norm (z - (y : ℂ))).trans hd
    simp only [Complex.sub_re, Complex.ofReal_re] at hr
    have hl := (abs_le.mp hr).1
    have hyR : R < y := hRa.trans_le hy.1
    change 0 < z.re
    linarith only [hl, hyR]
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h := real_within_deriv_le_cauchy hU (theta_mellin_complex_analytic s N) hab hy ha hball hM n
  have he : (fun x : ℝ ↦ thetaMellinComplex s N (x : ℂ)) = thetaMellinFinite s N := by
    funext x
    exact theta_mellin_complex_of_real s N x
  rw [he] at h
  exact h

/-- For eight Gaussian terms and critical-line heights at most 100, the
`n`-th within-derivative on a positive cell is bounded by the rational Cauchy
budget `n! 10^100 / (1/2)^n`. The bound is uniform on cells starting at one. -/
theorem theta_mellin_critical_deriv_bound {s : ℂ} (hs : s.re = 1 / 2) (ht : |s.im| ≤ 100) (n : ℕ)
    {a b y : ℝ} (ha : 1 ≤ a) (hab : a < b) (hy : y ∈ Set.Icc a b) :
    ‖iteratedDerivWithin n (thetaMellinFinite s 8) (Set.Icc a b) y‖ ≤
      n.factorial * (10 : ℝ) ^ 100 / (1 / 2 : ℝ) ^ n := by
  apply
    theta_mellin_deriv_le_cauchy s 8 n (by norm_num only : (0 : ℝ) < 1 / 2)
      (show (1 / 2 : ℝ) < a by linarith only [ha]) hab hy
  intro z hz
  have hy1 : 1 ≤ y := ha.trans hy.1
  exact (theta_mellin_critical_sphere_bound hs ht hy1 hz).trans critical_sphere_majorant_rational

/-- Every finite theta Mellin integrand is real-analytic at positive real
arguments. The complex power is analytic on the slit plane, while each
Gaussian term is an analytic real exponential. -/
theorem theta_mellin_finite_analytic (s : ℂ) (N : ℕ) {x : ℝ} (hx : 0 < x) :
    AnalyticAt ℝ (thetaMellinFinite s N) x := by
  have hc : AnalyticAt ℂ (fun z : ℂ ↦ z ^ (s / 2 - 1)) (x : ℂ) :=
    analyticAt_id.cpow analyticAt_const (Complex.ofReal_mem_slitPlane.mpr hx)
  have hw : AnalyticAt ℝ (fun y : ℝ ↦ (y : ℂ) ^ (s / 2 - 1)) x :=
    hc.restrictScalars.comp (Complex.ofRealCLM.analyticAt x)
  have hg :
    AnalyticAt ℝ (fun y : ℝ ↦ 2 * ∑ k ∈ Finset.range N, Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * y))
      x := by
    apply analyticAt_const.mul
    have hh :
      AnalyticAt ℝ (∑ k ∈ Finset.range N, fun y : ℝ ↦ Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * y))
        x := by
      apply Finset.analyticAt_sum
      intro k hk
      exact (analyticAt_const.mul analyticAt_id).rexp'
    convert hh using 1
    ext y
    simp only [Finset.sum_apply]
  have hh := hw.mul ((Complex.ofRealCLM.analyticAt _).comp hg)
  convert hh using 1
  ext y
  simp only [thetaMellinFinite, Pi.mul_apply, Function.comp_apply, Complex.ofRealCLM_apply]

/-- On any compact interval contained in the positive half-line, the finite
Mellin integrand is continuously differentiable to every requested order. -/
theorem theta_mellin_finite_smooth (s : ℂ) (N n : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContDiffOn ℝ n (thetaMellinFinite s N) (Set.Icc a b) := by
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
  exact (theta_mellin_finite_analytic s N hx0).contDiffAt.contDiffWithinAt

/-- On a nondegenerate positive cell, the finite Taylor quadrature sum for
the Mellin integrand can be evaluated using ordinary derivatives at the
left endpoint. Real analyticity removes the within-set derivative input. -/
theorem theta_mellin_cell_sum (s : ℂ) (N n : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Analysis.taylorCellSum (thetaMellinFinite s N) n a b =
      ∑ k ∈ Finset.range (n + 1),
        (((k.factorial : ℝ)⁻¹ * ((b - a) ^ (k + 1) / (k + 1))) : ℝ) •
          iteratedDeriv k (thetaMellinFinite s N) a := by
  apply Analysis.taylor_cell_sum_eq_derivatives hab
  intro k hk
  exact (theta_mellin_finite_analytic s N ha).contDiffAt

/-- The explicit coefficient of order `n` at the positive node `x` for the
finite theta Mellin integrand. The nested finite sums use the product rule,
the falling product, and the elementary exponential derivative. -/
noncomputable def thetaMellinCoefficient (s : ℂ) (N n : ℕ) (x : ℝ) : ℂ :=
  2 *
    ∑ k ∈ Finset.range N,
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℂ) *
          (PseudoPrime.Analysis.complexFalling (s / 2 - 1) j * (x : ℂ) ^ (s / 2 - 1 - j)) *
          ((((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) ^ (n - j)) *
            Complex.exp (((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) * x))

/-- On a positive node, all terms in a Taylor coefficient share a single
complex power. The remaining finite sum uses only integer powers of the
node, the Gaussian exponentials and polynomial arithmetic. -/
theorem theta_mellin_coefficient_factor (s : ℂ) (N n : ℕ) {x : ℝ} (hx : 0 < x) :
    thetaMellinCoefficient s N n x =
      (x : ℂ) ^ (s / 2 - 1) *
        (2 *
          ∑ k ∈ Finset.range N,
            ∑ j ∈ Finset.range (n + 1),
              (n.choose j : ℂ) * (PseudoPrime.Analysis.complexFalling (s / 2 - 1) j / (x : ℂ) ^ j) *
                ((((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) ^ (n - j)) *
                  Complex.exp (((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) * x))) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  simp only [thetaMellinCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro j hj
  rw [Complex.cpow_sub _ _ hx0, Complex.cpow_natCast]
  ring

/-- The finite coefficient remaining after factoring out the node's complex
power. Its dependence on the derivative order uses only finite sums, integer
powers, and Gaussian exponentials. -/
noncomputable def thetaMellinPolyCoeff (s : ℂ) (N n : ℕ) (x : ℝ) : ℂ :=
  2 *
    ∑ k ∈ Finset.range N,
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℂ) * (PseudoPrime.Analysis.complexFalling (s / 2 - 1) j / (x : ℂ) ^ j) *
          ((((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) ^ (n - j)) *
            Complex.exp (((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) * x))

/-- The power factor is independent of the derivative order, permitting one
phase evaluation per quadrature node instead of one for every coefficient. -/
theorem theta_mellin_coefficient_poly (s : ℂ) (N n : ℕ) {x : ℝ} (hx : 0 < x) :
    thetaMellinCoefficient s N n x = (x : ℂ) ^ (s / 2 - 1) * thetaMellinPolyCoeff s N n x := by
  exact theta_mellin_coefficient_factor s N n hx

/-- For a positive node, a complex power with real and imaginary exponents
is an exponential amplitude times a sine-cosine phase. The identity allows
independent rational interval bounds for the amplitude and phase. -/
theorem positive_cpow_exp_phase {x : ℝ} (hx : 0 < x) (u v : ℝ) :
    (x : ℂ) ^ ((u : ℂ) + (v : ℂ) * Complex.I) =
      (Real.exp (Real.log x * u) : ℂ) *
        ((Real.cos (Real.log x * v) : ℂ) + (Real.sin (Real.log x * v) : ℂ) * Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hx)), ←
    Complex.ofReal_log hx.le]
  have harg :
    (Real.log x : ℂ) * ((u : ℂ) + (v : ℂ) * Complex.I) =
      ((Real.log x * u : ℝ) : ℂ) + ((Real.log x * v : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_add_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- At a critical-line height, the common power factor has amplitude
`exp (-3 log x / 4)` and phase `t log x / 2`. This concrete identity is
used to evaluate all derivative orders at a fixed quadrature node. -/
theorem critical_cpow_exp_phase {x : ℝ} (hx : 0 < x) (t : ℝ) :
    (x : ℂ) ^ ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2 - 1) =
      (Real.exp (Real.log x * (-(3 / 4 : ℝ))) : ℂ) *
        ((Real.cos (Real.log x * (t / 2)) : ℂ) +
          (Real.sin (Real.log x * (t / 2)) : ℂ) * Complex.I) := by
  have hexp :
    ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2 - 1) =
      ((-(3 / 4 : ℝ) : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hexp, positive_cpow_exp_phase hx]

/-- A positive nondegenerate cell's Taylor sum uses only the explicit
finite coefficients, with no iterated derivatives left to evaluate. -/
theorem theta_mellin_cell_explicit (s : ℂ) (N n : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Analysis.taylorCellSum (thetaMellinFinite s N) n a b =
      ∑ k ∈ Finset.range (n + 1),
        (((k.factorial : ℝ)⁻¹ * ((b - a) ^ (k + 1) / (k + 1))) : ℝ) •
          thetaMellinCoefficient s N k a := by
  rw [theta_mellin_cell_sum s N n ha hab]
  apply Finset.sum_congr rfl
  intro k hk
  rw [theta_mellin_real_deriv s N k ha]
  rfl

/-- On an ordered positive partition, high-order Taylor quadrature bounds
the error in the finite theta Mellin integral by the sum of its cell errors.
Only the explicit derivative bounds remain to be certified. -/
theorem theta_mellin_taylor_composite (s : ℂ) (N n m : ℕ) (p C : ℕ → ℝ) (hp : ∀ j < m, 0 < p j)
    (hab : ∀ j < m, p j ≤ p (j + 1))
    (hC :
      ∀ j < m,
        ∀ y ∈ Set.Icc (p j) (p (j + 1)),
          ‖iteratedDerivWithin (n + 1) (thetaMellinFinite s N) (Set.Icc (p j) (p (j + 1))) y‖ ≤
            C j) :
    ‖(∫ x in p 0..p m, thetaMellinFinite s N x) -
          ∑ j ∈ Finset.range m,
            Analysis.taylorCellSum (thetaMellinFinite s N) n (p j) (p (j + 1))‖ ≤
      ∑ j ∈ Finset.range m, C j * (p (j + 1) - p j) ^ (n + 2) / n.factorial := by
  apply Analysis.taylor_composite_sum_error hab
  · intro j hj
    exact theta_mellin_finite_smooth s N (n + 1) (hp j hj)
  · exact hC

/-- The real part of the reflected composite Taylor quadrature for the
finite critical-line theta Mellin integrals. The partition and Taylor order
are supplied explicitly for a finite endpoint certificate. -/
noncomputable def criticalThetaQuadrature (t : ℝ) (N n m : ℕ) (p : ℕ → ℝ) : ℝ :=
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  (((∑ j ∈ Finset.range m, Analysis.taylorCellSum (thetaMellinFinite s N) n (p j) (p (j + 1))) +
        (∑ j ∈ Finset.range m,
          Analysis.taylorCellSum (thetaMellinFinite (1 - s) N) n (p j) (p (j + 1)))) /
      2).re

/-- The Taylor cell sum written as a finite sum of explicit coefficients.
It is intended for direct evaluation at rational partition nodes. -/
noncomputable def thetaMellinExplicitCell (s : ℂ) (N n : ℕ) (a b : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    (((k.factorial : ℝ)⁻¹ * ((b - a) ^ (k + 1) / (k + 1))) : ℝ) • thetaMellinCoefficient s N k a

/-- A Taylor cell factored into one complex power at its left endpoint and
a finite sum of polynomial coefficients. This form avoids repeatedly
evaluating the same logarithmic phase for different derivative orders. -/
theorem theta_mellin_explicit_cell_factor (s : ℂ) (N n : ℕ) {a b : ℝ} (ha : 0 < a) :
    thetaMellinExplicitCell s N n a b =
      (a : ℂ) ^ (s / 2 - 1) *
        ∑ k ∈ Finset.range (n + 1),
          (((k.factorial : ℝ)⁻¹ * ((b - a) ^ (k + 1) / (k + 1))) : ℝ) •
            thetaMellinPolyCoeff s N k a := by
  simp only [thetaMellinExplicitCell, Finset.mul_sum, Complex.real_smul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [theta_mellin_coefficient_poly s N k ha]
  ring

/-- The critical-line cell uses one real exponential amplitude and one
sine-cosine phase, multiplied by the finite coefficient sum. This is the
cell form used for interval evaluation at rational grid points. -/
theorem critical_explicit_cell_phase (t : ℝ) (N n : ℕ) {a b : ℝ} (ha : 0 < a) :
    thetaMellinExplicitCell (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) N n a b =
      ((Real.exp (Real.log a * (-(3 / 4 : ℝ))) : ℂ) *
          ((Real.cos (Real.log a * (t / 2)) : ℂ) +
            (Real.sin (Real.log a * (t / 2)) : ℂ) * Complex.I)) *
        ∑ k ∈ Finset.range (n + 1),
          (((k.factorial : ℝ)⁻¹ * ((b - a) ^ (k + 1) / (k + 1))) : ℝ) •
            thetaMellinPolyCoeff (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) N k a := by
  rw [theta_mellin_explicit_cell_factor _ _ _ ha, critical_cpow_exp_phase ha]

/-- The composite critical-line quadrature in terms of explicit finite
coefficients. Both reflected integrands use the same partition template. -/
noncomputable def criticalExplicitQuadrature (t : ℝ) (N n m : ℕ) (p : ℕ → ℝ) : ℝ :=
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  (((∑ j ∈ Finset.range m, thetaMellinExplicitCell s N n (p j) (p (j + 1))) +
        (∑ j ∈ Finset.range m, thetaMellinExplicitCell (1 - s) N n (p j) (p (j + 1)))) /
      2).re

/-- On a positive strictly increasing partition, the derivative-based
quadrature equals its explicit finite-sum form on every cell. -/
theorem critical_quadrature_explicit (t : ℝ) (N n m : ℕ) (p : ℕ → ℝ) (hp : ∀ j < m, 0 < p j)
    (hab : ∀ j < m, p j < p (j + 1)) :
    criticalThetaQuadrature t N n m p = criticalExplicitQuadrature t N n m p := by
  simp only [criticalThetaQuadrature, criticalExplicitQuadrature, thetaMellinExplicitCell]
  congr 3 <;> apply Finset.sum_congr rfl <;> intro j hj
  all_goals
    exact
      theta_mellin_cell_explicit _ _ _ (hp j (Finset.mem_range.mp hj))
        (hab j (Finset.mem_range.mp hj))

/-- A composite Taylor certificate bounds the real regularized completed
zeta value at height `t`. The total error is the analytic Mellin truncation
budget plus half the sum of the two reflected quadrature budgets. -/
theorem critical_completed_taylor_error (t A : ℝ) (N n m : ℕ) (p C D : ℕ → ℝ) (hstart : p 0 = 1)
    (hend : p m = A) (hA : 1 ≤ A) (hp : ∀ j < m, 0 < p j) (hab : ∀ j < m, p j ≤ p (j + 1))
    (hC :
      ∀ j < m,
        ∀ y ∈ Set.Icc (p j) (p (j + 1)),
          ‖iteratedDerivWithin (n + 1)
                (thetaMellinFinite (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) N)
                (Set.Icc (p j) (p (j + 1))) y‖ ≤
            C j)
    (hD :
      ∀ j < m,
        ∀ y ∈ Set.Icc (p j) (p (j + 1)),
          ‖iteratedDerivWithin (n + 1)
                (thetaMellinFinite (1 - (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) N)
                (Set.Icc (p j) (p (j + 1))) y‖ ≤
            D j) :
    |criticalCompletedZeta t - criticalThetaQuadrature t N n m p| ≤
      criticalMellinError N A +
        ((∑ j ∈ Finset.range m, C j * (p (j + 1) - p j) ^ (n + 2) / n.factorial) +
            (∑ j ∈ Finset.range m, D j * (p (j + 1) - p j) ^ (n + 2) / n.factorial)) /
          2 := by
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  let q1 : ℂ :=
    ∑ j ∈ Finset.range m, Analysis.taylorCellSum (thetaMellinFinite s N) n (p j) (p (j + 1))
  let q2 : ℂ :=
    ∑ j ∈ Finset.range m, Analysis.taylorCellSum (thetaMellinFinite (1 - s) N) n (p j) (p (j + 1))
  let f1 : ℂ := ∫ x : ℝ in (1 : ℝ)..A, thetaMellinFinite s N x
  let f2 : ℂ := ∫ x : ℝ in (1 : ℝ)..A, thetaMellinFinite (1 - s) N x
  have h1 := theta_mellin_taylor_composite s N n m p C hp hab hC
  have h2 := theta_mellin_taylor_composite (1 - s) N n m p D hp hab hD
  rw [hstart, hend] at h1 h2
  change ‖f1 - q1‖ ≤ _ at h1
  change ‖f2 - q2‖ ≤ _ at h2
  have hsum := norm_add_le (f1 - q1) (f2 - q2)
  have he : (f1 + f2) / 2 - (q1 + q2) / 2 = ((f1 - q1) + (f2 - q2)) / 2 := by ring
  have hnorm :
    ‖(f1 + f2) / 2 - (q1 + q2) / 2‖ ≤
      ((∑ j ∈ Finset.range m, C j * (p (j + 1) - p j) ^ (n + 2) / n.factorial) +
          (∑ j ∈ Finset.range m, D j * (p (j + 1) - p j) ^ (n + 2) / n.factorial)) /
        2 := by
    rw [he, norm_div, Complex.norm_ofNat]
    linarith only [hsum, h1, h2]
  have hr := Complex.abs_re_le_norm ((f1 + f2) / 2 - (q1 + q2) / 2)
  have hreal :
    |((f1 + f2) / 2).re - ((q1 + q2) / 2).re| ≤
      ((∑ j ∈ Finset.range m, C j * (p (j + 1) - p j) ^ (n + 2) / n.factorial) +
          (∑ j ∈ Finset.range m, D j * (p (j + 1) - p j) ^ (n + 2) / n.factorial)) /
        2 := by
    simpa only [Complex.sub_re] using hr.trans hnorm
  have hbase := critical_completed_finite_error t hA N
  change |criticalCompletedZeta t - ((f1 + f2) / 2).re| ≤ criticalMellinError N A at hbase
  change |criticalCompletedZeta t - ((q1 + q2) / 2).re| ≤ _
  have htri :=
    abs_add_le (criticalCompletedZeta t - ((f1 + f2) / 2).re)
      (((f1 + f2) / 2).re - ((q1 + q2) / 2).re)
  have he' :
    criticalCompletedZeta t - ((f1 + f2) / 2).re + (((f1 + f2) / 2).re - ((q1 + q2) / 2).re) =
      criticalCompletedZeta t - ((q1 + q2) / 2).re := by
    ring
  rw [he'] at htri
  linarith only [htri, hbase, hreal]

/-- The explicit uniform Cauchy bound for the `(n+1)`-st derivative of an
eight-term critical theta Mellin integrand at heights at most 100. -/
noncomputable def criticalTaylorDerivativeBound (n : ℕ) : ℝ :=
  (n + 1).factorial * (10 : ℝ) ^ 100 / (1 / 2 : ℝ) ^ (n + 1)

/-- For critical-line heights at most 100, strictly ordered cells beginning
at or above one admit a completely explicit composite Taylor error bound.
The prior derivative-bound assumptions follow from the uniform Cauchy bound. -/
theorem critical_completed_uniform_taylor_error {t A : ℝ} (ht : |t| ≤ 100) (n m : ℕ) (p : ℕ → ℝ)
    (hstart : p 0 = 1) (hend : p m = A) (hA : 1 ≤ A) (hp : ∀ j < m, 1 ≤ p j)
    (hab : ∀ j < m, p j < p (j + 1)) :
    |criticalCompletedZeta t - criticalThetaQuadrature t 8 n m p| ≤
      criticalMellinError 8 A +
        ∑ j ∈ Finset.range m,
          criticalTaylorDerivativeBound n * (p (j + 1) - p j) ^ (n + 2) / n.factorial := by
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  have hsr : s.re = 1 / 2 := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hsi : |s.im| ≤ 100 := by
    simpa only [s, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero] using ht
  have hsr' : (1 - s).re = 1 / 2 := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith only [hsr]
  have hsi' : |(1 - s).im| ≤ 100 := by
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using hsi
  have hpos : ∀ j < m, 0 < p j := by
    intro j hj
    exact lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) (hp j hj)
  have hle : ∀ j < m, p j ≤ p (j + 1) := fun j hj ↦ (hab j hj).le
  have hC :
    ∀ j < m,
      ∀ y ∈ Set.Icc (p j) (p (j + 1)),
        ‖iteratedDerivWithin (n + 1) (thetaMellinFinite s 8) (Set.Icc (p j) (p (j + 1))) y‖ ≤
          criticalTaylorDerivativeBound n := by
    intro j hj y hy
    exact theta_mellin_critical_deriv_bound hsr hsi (n + 1) (hp j hj) (hab j hj) hy
  have hD :
    ∀ j < m,
      ∀ y ∈ Set.Icc (p j) (p (j + 1)),
        ‖iteratedDerivWithin (n + 1) (thetaMellinFinite (1 - s) 8) (Set.Icc (p j) (p (j + 1))) y‖ ≤
          criticalTaylorDerivativeBound n := by
    intro j hj y hy
    exact theta_mellin_critical_deriv_bound hsr' hsi' (n + 1) (hp j hj) (hab j hj) hy
  have h :=
    critical_completed_taylor_error t A 8 n m p (fun _ ↦ criticalTaylorDerivativeBound n)
      (fun _ ↦ criticalTaylorDerivativeBound n) hstart hend hA hpos hle hC hD
  linarith only [h]

/-- The uniform grid of mesh `1/16` starting at one. Its first 944 cells
cover exactly `[1,60]` for the compact critical-line computation. -/
noncomputable def criticalQuadratureGrid (j : ℕ) : ℝ :=
  1 + j / 16

/-- The explicit 200th-order Taylor budget on one `1/16` cell is at most
`1 / (944 * 10^60)`. Exact arithmetic verifies the Cauchy majorant and
factorial cancellation without a numerical table. -/
theorem critical_grid_cell_error :
    criticalTaylorDerivativeBound 200 * (1 / 16 : ℝ) ^ 202 / (Nat.factorial 200 : ℝ) ≤
      1 / (944 * (10 : ℝ) ^ 60) := by
  have hf : (Nat.factorial 200 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero 200)
  have he :
    criticalTaylorDerivativeBound 200 * (1 / 16 : ℝ) ^ 202 / (Nat.factorial 200 : ℝ) =
      (201 * (10 : ℝ) ^ 100 / (1 / 2 : ℝ) ^ 201) * (1 / 16 : ℝ) ^ 202 := by
    unfold criticalTaylorDerivativeBound
    rw [Nat.factorial_succ, Nat.cast_mul]
    field_simp [hf]
    norm_num only
  rw [he]
  norm_num only

/-- At every critical-line height `|t| ≤ 100`, the 200th-order composite
Taylor sum on the explicit 944-cell grid approximates the regularized zeta
real part to `10⁻⁵² + 10⁻⁶⁰`. The first term is the Mellin truncation error
and the second is the certified composite quadrature error. -/
theorem critical_quadrature_error {t : ℝ} (ht : |t| ≤ 100) :
    |criticalCompletedZeta t - criticalThetaQuadrature t 8 200 944 criticalQuadratureGrid| ≤
      1 / (10 : ℝ) ^ 52 + 1 / (10 : ℝ) ^ 60 := by
  have hs : criticalQuadratureGrid 0 = 1 := by
    norm_num only [criticalQuadratureGrid, Nat.cast_zero, zero_div, add_zero]
  have he : criticalQuadratureGrid 944 = 60 := by
    norm_num only [criticalQuadratureGrid, Nat.cast_ofNat]
  have hp : ∀ j < 944, 1 ≤ criticalQuadratureGrid j := by
    intro j hj
    dsimp only [criticalQuadratureGrid]
    have hn : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith only [hn]
  have hab : ∀ j < 944, criticalQuadratureGrid j < criticalQuadratureGrid (j + 1) := by
    intro j hj
    dsimp only [criticalQuadratureGrid]
    simp only [Nat.cast_add, Nat.cast_one]
    linarith only
  have hw : ∀ j, criticalQuadratureGrid (j + 1) - criticalQuadratureGrid j = 1 / 16 := by
    intro j
    dsimp only [criticalQuadratureGrid]
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  have hsum :
    (∑ j ∈ Finset.range 944,
        criticalTaylorDerivativeBound 200 *
            (criticalQuadratureGrid (j + 1) - criticalQuadratureGrid j) ^ (200 + 2) /
          (Nat.factorial 200 : ℝ)) ≤
      1 / (10 : ℝ) ^ 60 := by
    simp only [hw, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h := mul_le_mul_of_nonneg_left critical_grid_cell_error (by norm_num only : (0 : ℝ) ≤ 944)
    nlinarith only [h]
  have h :=
    critical_completed_uniform_taylor_error ht 200 944 criticalQuadratureGrid hs he
      (by norm_num only : (1 : ℝ) ≤ 60) hp hab
  linarith only [h, hsum, critical_mellin_error_eight_sixty]

/-- On the fixed rational grid, derivative-based quadrature equals the
finite coefficient expression at every height. -/
theorem critical_fixed_quadrature_explicit (t : ℝ) :
    criticalThetaQuadrature t 8 200 944 criticalQuadratureGrid =
      criticalExplicitQuadrature t 8 200 944 criticalQuadratureGrid := by
  have hp : ∀ j < 944, 0 < criticalQuadratureGrid j := by
    intro j hj
    dsimp only [criticalQuadratureGrid]
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    exact add_pos_of_pos_of_nonneg (by norm_num only) (div_nonneg hj0 (by norm_num only))
  have hab : ∀ j < 944, criticalQuadratureGrid j < criticalQuadratureGrid (j + 1) := by
    intro j hj
    dsimp only [criticalQuadratureGrid]
    push_cast
    linarith only
  exact critical_quadrature_explicit t 8 200 944 criticalQuadratureGrid hp hab

/-- The fixed 944-cell quadrature retains its certified error after replacing
all derivatives by the explicit finite coefficient sums. -/
theorem critical_explicit_quadrature_error {t : ℝ} (ht : |t| ≤ 100) :
    |criticalCompletedZeta t - criticalExplicitQuadrature t 8 200 944 criticalQuadratureGrid| ≤
      1 / 10 ^ 52 + 1 / 10 ^ 60 := by
  rw [← critical_fixed_quadrature_explicit t]
  exact critical_quadrature_error ht

/-- Any certified approximation to the critical completed-zeta real part
proves a positive xi sign when its upper interval lies below the xi
threshold. In particular, the composite Taylor error may supply `hE`. -/
theorem critical_xi_pos_of_approx {t q E : ℝ} (hE : |criticalCompletedZeta t - q| ≤ E)
    (hq : (t ^ 2 + 1 / 4) * (q + E) < 1) :
    0 < (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by
  apply (xi_critical_pos_iff t).2
  have hb := (abs_le.mp hE).2
  have hp : 0 ≤ t ^ 2 + 1 / 4 := by nlinarith only [sq_nonneg t]
  have hm :=
    mul_le_mul_of_nonneg_left (show criticalCompletedZeta t ≤ q + E by linarith only [hb]) hp
  exact hm.trans_lt hq

/-- Any certified approximation to the critical completed-zeta real part
proves a negative xi sign when its lower interval lies above the xi
threshold. It complements the positive-sign quadrature criterion. -/
theorem critical_xi_neg_of_approx {t q E : ℝ} (hE : |criticalCompletedZeta t - q| ≤ E)
    (hq : 1 < (t ^ 2 + 1 / 4) * (q - E)) :
    (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re < 0 := by
  apply (xi_critical_neg_iff t).2
  have hb := (abs_le.mp hE).1
  have hp : 0 ≤ t ^ 2 + 1 / 4 := by nlinarith only [sq_nonneg t]
  have hm :=
    mul_le_mul_of_nonneg_left (show q - E ≤ criticalCompletedZeta t by linarith only [hb]) hp
  exact hq.trans_le hm

end PseudoPrime.AnalyticNumberTheory.RiemannXi
