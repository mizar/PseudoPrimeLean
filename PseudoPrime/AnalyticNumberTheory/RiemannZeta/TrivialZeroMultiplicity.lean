/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCounting
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroContribution
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroClassification
import Mathlib.NumberTheory.ZetaValues

/-!
# Simplicity of zeta's trivial zeros

Near `-2(n+1)`, the functional equation writes zeta as
`2*(2π)^(-(1-w))*Γ(1-w)*ζ(1-w)*sin(πw/2)`.
The first factor is analytic and nonzero there, while the sine has a simple zero.
Thus every trivial zero has multiplicity one. This identifies trivial-zero
residue contributions with the logarithmic and reciprocal series.
-/

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- `ζ` factors as `A(w) · sin(πw/2)` on the ball of radius `1` around any trivial zero
`-2(n+1)`, where `A(w) := 2·(2π)^{-(1-w)}·Γ(1-w)·ζ(1-w)`. -/
theorem riemannZeta_eq_mul_sin_eventually (n : ℕ) :
    (fun w : ℂ => riemannZeta w) =ᶠ[nhds (-2 * ((n : ℂ) + 1))]
      (fun w : ℂ =>
        (2 * (2 * (Real.pi : ℂ)) ^ (-(1 - w)) * Complex.Gamma (1 - w) * riemannZeta (1 - w)) *
          Complex.sin ((Real.pi : ℂ) * w / 2)) := by
  have hball : Metric.ball (-2 * ((n : ℂ) + 1)) 1 ⊆ {w : ℂ | w ≠ 0 ∧ ∀ m : ℕ, w ≠ 1 + m} := by
    intro w hw
    have hdist : ‖w - (-2 * ((n : ℂ) + 1))‖ < 1 := by
      simpa only [neg_mul, sub_neg_eq_add, Metric.mem_ball, Complex.dist_eq] using hw
    have hre_le : |w.re - (-2 * ((n : ℂ) + 1)).re| ≤ ‖w - (-2 * ((n : ℂ) + 1))‖ := by
      have h := Complex.abs_re_le_norm (w - (-2 * ((n : ℂ) + 1)))
      rwa [Complex.sub_re] at h
    have hre_lt : |w.re - (-2 * ((n : ℂ) + 1)).re| < 1 := lt_of_le_of_lt hre_le hdist
    have hw0re : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by
      simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.add_re,
        Complex.natCast_re, Complex.one_re, Complex.im_ofNat, Complex.add_im, Complex.natCast_im,
        Complex.one_im, add_zero, mul_zero, sub_zero]
    rw [hw0re] at hre_lt
    have hwre_neg : w.re < 0 := by
      have := (abs_lt.mp hre_lt).2
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    refine
      ⟨fun h0 => by
        rw [h0] at hwre_neg
        simp only [Complex.zero_re, lt_self_iff_false] at hwre_neg, fun m hm => ?_⟩
    have : w.re = 1 + m := by
      rw [hm]
      simp only [Complex.add_re, Complex.one_re, Complex.natCast_re]
    rw [this] at hwre_neg
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  filter_upwards [Metric.ball_mem_nhds (-2 * ((n : ℂ) + 1)) one_pos] with w hw
  obtain ⟨hw0, hwm⟩ := hball hw
  have hs :=
    riemannZeta_one_sub (s := 1 - w) (fun m hm => hwm m (by linear_combination -hm))
      (fun h1 => hw0 (by linear_combination -h1))
  rw [show (1 - (1 - w)) = w from by ring] at hs
  have hcos_eq :
    Complex.cos ((Real.pi : ℂ) * (1 - w) / 2) = Complex.sin ((Real.pi : ℂ) * w / 2) := by
    rw [show (Real.pi : ℂ) * (1 - w) / 2 = Real.pi / 2 - (Real.pi : ℂ) * w / 2 from by ring,
      Complex.cos_pi_div_two_sub]
  rw [hcos_eq] at hs
  rw [hs]; ring

/-- Every trivial zero `-2(n+1)` of `ζ` is a *simple* zero. -/
theorem riemannZetaZeroMultiplicity_neg_two_mul_nat_add_one (n : ℕ) :
    riemannZetaZeroMultiplicity (-2 * ((n : ℂ) + 1)) =
      1 := by
  set w₀ : ℂ := -2 * ((n : ℂ) + 1) with hw₀_def
  set A : ℂ → ℂ := fun w =>
    2 * (2 * (Real.pi : ℂ)) ^ (-(1 - w)) * Complex.Gamma (1 - w) * riemannZeta (1 - w) with hA_def
  set B : ℂ → ℂ := fun w => Complex.sin ((Real.pi : ℂ) * w / 2) with hB_def
  have hw₀re : w₀.re = -2 * ((n : ℝ) + 1) := by
    rw [hw₀_def]
    simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.add_re,
      Complex.natCast_re, Complex.one_re, Complex.im_ofNat, Complex.add_im, Complex.natCast_im,
      Complex.one_im, add_zero, mul_zero, sub_zero]
  have hball : Metric.ball w₀ 1 ⊆ {w : ℂ | w.re < 0} := by
    intro w hw
    have hdist : ‖w - w₀‖ < 1 := by simpa only [Metric.mem_ball, Complex.dist_eq] using hw
    have hre_le : |w.re - w₀.re| ≤ ‖w - w₀‖ := by
      have h := Complex.abs_re_le_norm (w - w₀); rwa [Complex.sub_re] at h
    have hre_lt : |w.re - w₀.re| < 1 := lt_of_le_of_lt hre_le hdist
    rw [hw₀re] at hre_lt
    have hlt := (abs_lt.mp hre_lt).2
    change w.re < 0
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hAdiff : ∀ w ∈ Metric.ball w₀ 1, DifferentiableAt ℂ A w := by
    intro w hw
    have hwre : w.re < 0 := hball hw
    have h1mwne : ∀ m : ℕ, (1 - w) ≠ -m := by
      intro m hm
      have hre : (1 - w).re = -(m : ℝ) := by
        rw [hm]
        simp only [Complex.neg_re, Complex.natCast_re]
      simp only [Complex.sub_re, Complex.one_re] at hre
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have h1mne1 : (1 - w) ≠ 1 := by
      intro h
      have hre : (1 - w).re = 1 := by
        rw [h]
        simp only [Complex.one_re]
      simp only [Complex.sub_re, Complex.one_re] at hre
      linarith
    have hc_ne : (2 * (Real.pi : ℂ)) ≠ 0 := by
      rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) from by
          push_cast; ring]
      exact Complex.ofReal_ne_zero.mpr (by positivity)
    have hexp_diff : DifferentiableAt ℂ (fun w : ℂ => -(1 - w)) w := by fun_prop
    have h1 : DifferentiableAt ℂ (fun w : ℂ => (2 * (Real.pi : ℂ)) ^ (-(1 - w))) w :=
      hexp_diff.const_cpow (Or.inl hc_ne)
    have h2 : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (1 - w)) w :=
      (Complex.differentiableAt_Gamma _ h1mwne).comp w (by fun_prop)
    have h3 : DifferentiableAt ℂ (fun w : ℂ => riemannZeta (1 - w)) w :=
      ((analyticOn_riemannZeta (1 - w) h1mne1).differentiableAt).comp w (by fun_prop)
    have hfun_eq :
      (fun _ : ℂ => (2 : ℂ)) * (fun w : ℂ => (2 * (Real.pi : ℂ)) ^ (-(1 - w))) *
          (fun w : ℂ => Complex.Gamma (1 - w)) *
          (fun w : ℂ => riemannZeta (1 - w)) =
        A := by
      funext w
      simp only [neg_sub, Pi.mul_apply, hA_def]
    rw [← hfun_eq]
    exact ((differentiableAt_const (2 : ℂ)).mul h1).mul h2 |>.mul h3
  have hAanalytic : AnalyticAt ℂ A w₀ :=
    Complex.analyticAt_iff_eventually_differentiableAt.mpr
      (Filter.eventually_of_mem (Metric.ball_mem_nhds w₀ one_pos) hAdiff)
  have hBanalytic : AnalyticAt ℂ B w₀ :=
    Complex.analyticAt_iff_eventually_differentiableAt.mpr
      (Filter.Eventually.of_forall
        (fun w => by
          rw [hB_def]; fun_prop))
  have h1msub : (1 - w₀) = ((2 * (n : ℝ) + 3 : ℝ) : ℂ) := by
    rw [hw₀_def]
    push_cast
    ring
  have h1msub_re : (1 - w₀).re = 2 * (n : ℝ) + 3 := by
    rw [h1msub]
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast,
      Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.natCast_re, Complex.im_ofNat,
      Complex.natCast_im, mul_zero, sub_zero]
  have hζ_ne : riemannZeta (1 - w₀) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re
      (by
        rw [h1msub_re]; linarith [Nat.cast_nonneg (α := ℝ) n])
  have hΓ_ne : Complex.Gamma (1 - w₀) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos
      (by
        rw [h1msub_re]; linarith [Nat.cast_nonneg (α := ℝ) n])
  have hc_ne : (2 * (Real.pi : ℂ)) ≠ 0 := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) from by
        push_cast; ring]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hpow_ne : (2 * (Real.pi : ℂ)) ^ (-(1 - w₀)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hc_ne)
  have hAw₀_ne : A w₀ ≠ 0 := by
    rw [hA_def]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpow_ne) hΓ_ne) hζ_ne
  have hBw₀_zero : B w₀ = 0 := by
    simp only [hB_def, hw₀_def]
    rw [show (Real.pi : ℂ) * (-2 * ((n : ℂ) + 1)) / 2 = -(Real.pi * ((n : ℂ) + 1)) from by ring,
      Complex.sin_neg, neg_eq_zero, Complex.sin_eq_zero_iff]
    exact
      ⟨(n : ℤ) + 1, by
        push_cast; ring⟩
  have hcos_ne : Complex.cos ((Real.pi : ℂ) * ((n : ℂ) + 1)) ≠ 0 := by
    intro hcos0
    rw [Complex.cos_eq_zero_iff] at hcos0
    obtain ⟨k, hk⟩ := hcos0
    have hpi_ne : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : (2 * ((n : ℤ) + 1) : ℂ) * (Real.pi : ℂ) = ((2 * k + 1 : ℤ) : ℂ) * (Real.pi : ℂ) := by
      push_cast; linear_combination 2 * hk
    have heq : (2 * ((n : ℤ) + 1) : ℂ) = ((2 * k + 1 : ℤ) : ℂ) := mul_right_cancel₀ hpi_ne h2
    have : 2 * ((n : ℤ) + 1) = 2 * k + 1 := by exact_mod_cast heq
    omega
  have hBderiv_ne : deriv B w₀ ≠ 0 := by
    have hf : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w / 2) ((Real.pi : ℂ) / 2) w₀ := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id w₀).const_mul (Real.pi : ℂ)).div_const 2
    have hderiv : HasDerivAt B (Complex.cos ((Real.pi : ℂ) * w₀ / 2) * ((Real.pi : ℂ) / 2)) w₀ := by
      rw [hB_def]; exact hf.csin
    rw [hderiv.deriv, hw₀_def,
      show (Real.pi : ℂ) * (-2 * ((n : ℂ) + 1)) / 2 = -(Real.pi * ((n : ℂ) + 1)) from by ring,
      Complex.cos_neg]
    have hpi2_ne : (Real.pi : ℂ) / 2 ≠ 0 := by
      rw [show (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) from by
          push_cast; ring]
      exact Complex.ofReal_ne_zero.mpr (by positivity)
    exact mul_ne_zero hcos_ne hpi2_ne
  have hBorder : analyticOrderAt B w₀ = 1 :=
    hBanalytic.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hBw₀_zero hBderiv_ne
  have hAorder : analyticOrderAt A w₀ = 0 := hAanalytic.analyticOrderAt_eq_zero.mpr hAw₀_ne
  have hcongr : analyticOrderAt riemannZeta w₀ = analyticOrderAt (fun w => A w * B w) w₀ :=
    analyticOrderAt_congr
      (riemannZeta_eq_mul_sin_eventually n)
  have hmul :
    analyticOrderAt (fun w => A w * B w) w₀ = analyticOrderAt A w₀ + analyticOrderAt B w₀ :=
    analyticOrderAt_mul hAanalytic hBanalytic
  rw [riemannZetaZeroMultiplicity, analyticOrderNatAt,
    hcongr, hmul, hAorder, hBorder]
  simp only [zero_add, ENat.toNat_one]

/-- `ζ`'s reciprocal-kernel contribution at the `k`-th trivial zero `-2(k+1)` is exactly the
negative of the `k`-th summand of the reciprocal trivial-zero series. -/
theorem riemannZetaReciprocalZeroContribution_neg_two_mul_nat_add_one {x : ℝ} (hx : 0 < x) (k : ℕ) :
    riemannZetaReciprocalZeroContribution x
        (-2 * ((k : ℂ) + 1)) =
      -((x⁻¹ ^ (2 * (k + 1) + 1) / ((2 * (k + 1) : ℝ) * (2 * (k + 1) + 1)) : ℝ) : ℂ) := by
  unfold riemannZetaReciprocalZeroContribution
  rw [riemannZetaZeroMultiplicity_neg_two_mul_nat_add_one]
  set ρ : ℂ := -2 * ((k : ℂ) + 1) with hρ_def
  have hρ1_eq : ρ - 1 = ((-(2 * (k + 1) + 1 : ℕ) : ℝ) : ℂ) := by
    rw [hρ_def]; push_cast; ring
  have hxcpow : (x : ℂ) ^ (ρ - 1) = ((x⁻¹ ^ (2 * (k + 1) + 1) : ℝ) : ℂ) := by
    rw [hρ1_eq,
      show ((-(2 * (k + 1) + 1 : ℕ) : ℝ) : ℂ) = -(((2 * (k + 1) + 1 : ℕ) : ℝ) : ℂ) from by
        push_cast; ring,
      Complex.cpow_neg, ← Complex.ofReal_cpow hx.le, Real.rpow_natCast, ← Complex.ofReal_inv,
      inv_pow]
  have hρprod : ρ * (ρ - 1) = (((2 * (k + 1) : ℝ) * (2 * (k + 1) + 1) : ℝ) : ℂ) := by
    rw [hρ1_eq, hρ_def]; push_cast; ring
  rw [hxcpow, hρprod, Nat.cast_one]
  push_cast
  ring

/-! The reciprocal trivial-zero summand is nonnegative for nonnegative `x`. -/

theorem reciprocalTrivialZeroTerm_nonneg {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    0 ≤ x⁻¹ ^ (2 * (k + 1) + 1) / ((2 * (k + 1) : ℝ) * (2 * (k + 1) + 1)) := by
  exact div_nonneg (pow_nonneg (inv_nonneg.mpr hx) _) (mul_nonneg (by positivity) (by positivity))

/-! A reciprocal trivial-zero summand is bounded by a geometric summand on `x ≥ 2`. -/

theorem reciprocalTrivialZeroTerm_le_geometric {x : ℝ} (hx : 2 ≤ x) (k : ℕ) :
    x⁻¹ ^ (2 * (k + 1) + 1) / ((2 * (k + 1) : ℝ) * (2 * (k + 1) + 1)) ≤
      x⁻¹ ^ 3 / 6 * (x⁻¹ ^ 2) ^ k := by
  have hinv : 0 ≤ x⁻¹ := inv_nonneg.mpr (by positivity)
  have hnumerator : 0 ≤ x⁻¹ ^ (2 * (k + 1) + 1) := pow_nonneg hinv _
  have hdenominator : (6 : ℝ) ≤ (2 * (k + 1) : ℝ) * (2 * (k + 1) + 1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  calc
    _ ≤ x⁻¹ ^ (2 * (k + 1) + 1) / 6 :=
      div_le_div_of_nonneg_left hnumerator (by norm_num only) hdenominator
    _ = x⁻¹ ^ 3 / 6 * (x⁻¹ ^ 2) ^ k := by
      have hexponent : 2 * (k + 1) + 1 = 3 + 2 * k := by omega
      rw [hexponent, pow_add, pow_mul]
      ring

/-- A reciprocal trivial-zero summand is bounded by a geometric summand for every `x > 0`. -/
theorem reciprocalTrivialZeroTerm_le_geometric_of_pos {x : ℝ} (hx : 0 < x) (k : ℕ) :
    x⁻¹ ^ (2 * (k + 1) + 1) / ((2 * (k + 1) : ℝ) * (2 * (k + 1) + 1)) ≤
      x⁻¹ ^ 3 / 6 * (x⁻¹ ^ 2) ^ k := by
  have hinv : 0 ≤ x⁻¹ := inv_nonneg.mpr hx.le
  have hnumerator : 0 ≤ x⁻¹ ^ (2 * (k + 1) + 1) := pow_nonneg hinv _
  have hdenominator : (6 : ℝ) ≤ (2 * (k + 1) : ℝ) * (2 * (k + 1) + 1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  calc
    _ ≤ x⁻¹ ^ (2 * (k + 1) + 1) / 6 :=
      div_le_div_of_nonneg_left hnumerator (by norm_num only) hdenominator
    _ = x⁻¹ ^ 3 / 6 * (x⁻¹ ^ 2) ^ k := by
      have hexponent : 2 * (k + 1) + 1 = 3 + 2 * k := by omega
      rw [hexponent, pow_add, pow_mul]
      ring

/-- The logarithmic-kernel analogue of `PseudoPrime.AnalyticNumberTheory.RiemannZeta.`
`riemannZetaReciprocalZeroContribution_neg_two_mul_nat_add_one`: `ζ`'s logarithmic-kernel
contribution at the `k`-th trivial zero `-2(k+1)` is `-x^{-2(k+1)}/(4(k+1)²)`. -/
theorem riemannZetaLogZeroContribution_neg_two_mul_nat_add_one {x : ℝ} (hx : 0 < x) (k : ℕ) :
    riemannZetaLogZeroContribution x
        (-2 * ((k : ℂ) + 1)) =
      -((x⁻¹ ^ (2 * (k + 1)) / (4 * ((k : ℝ) + 1) ^ 2) : ℝ) : ℂ) := by
  unfold riemannZetaLogZeroContribution
  rw [riemannZetaZeroMultiplicity_neg_two_mul_nat_add_one]
  set ρ : ℂ := -2 * ((k : ℂ) + 1) with hρ_def
  have hρ_eq : ρ = ((-(2 * (k + 1) : ℕ) : ℝ) : ℂ) := by
    rw [hρ_def]; push_cast; ring
  have hxcpow : (x : ℂ) ^ ρ = ((x⁻¹ ^ (2 * (k + 1)) : ℝ) : ℂ) := by
    rw [hρ_eq,
      show ((-(2 * (k + 1) : ℕ) : ℝ) : ℂ) = -(((2 * (k + 1) : ℕ) : ℝ) : ℂ) from by
        push_cast; ring,
      Complex.cpow_neg, ← Complex.ofReal_cpow hx.le, Real.rpow_natCast, ← Complex.ofReal_inv,
      inv_pow]
  have hρsq : ρ ^ 2 = (((4 : ℝ) * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by
    rw [hρ_eq]; push_cast; ring
  rw [hxcpow, hρsq, Nat.cast_one]
  push_cast
  ring

/-- The totalized logarithmic trivial-zero series. For `x > 1`, its terms
are positive and the series converges. -/
noncomputable def riemannZetaLogTrivialZeroSeries (x : ℝ) : ℝ :=
  ∑' k : ℕ, x⁻¹ ^ (2 * (k + 1)) / (4 * ((k : ℝ) + 1) ^ 2)

/-- The logarithmic trivial-zero series is nonnegative for `x ≥ 0`. -/
theorem riemannZetaLogTrivialZeroSeries_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ riemannZetaLogTrivialZeroSeries x := by
  rw [riemannZetaLogTrivialZeroSeries]
  exact tsum_nonneg fun k => div_nonneg (pow_nonneg (inv_nonneg.mpr hx) _) (by positivity)

/-- The logarithmic trivial-zero series' summand sequence is summable for every `x > 1`. -/
theorem summable_logTrivialZeroTerm {x : ℝ} (hx : 1 < x) :
    Summable fun k : ℕ => x⁻¹ ^ (2 * (k + 1)) / (4 * ((k : ℝ) + 1) ^ 2) := by
  have hxpos : 0 < x := by linarith
  have hinv : 0 ≤ x⁻¹ := inv_nonneg.mpr hxpos.le
  have hinvlt : x⁻¹ < (1 : ℝ) := inv_lt_one_of_one_lt₀ hx
  have hratio : x⁻¹ ^ 2 < 1 := by nlinarith [sq_nonneg (x⁻¹)]
  have hgeom : Summable fun k : ℕ => (x⁻¹ ^ 2) ^ k :=
    summable_geometric_of_lt_one (pow_nonneg hinv 2) hratio
  have hmajor : Summable fun k : ℕ => x⁻¹ ^ 2 / 4 * (x⁻¹ ^ 2) ^ k := hgeom.mul_left (x⁻¹ ^ 2 / 4)
  refine
    hmajor.of_nonneg_of_le (fun k => div_nonneg (pow_nonneg hinv _) (by positivity)) (fun k => ?_)
  have hk1sq : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hnum_eq : x⁻¹ ^ (2 * (k + 1)) = x⁻¹ ^ 2 * (x⁻¹ ^ 2) ^ k := by
    rw [← pow_mul, show 2 * (k + 1) = 2 + 2 * k from by ring, pow_add]
  rw [hnum_eq]
  have hnum_nonneg : (0 : ℝ) ≤ x⁻¹ ^ 2 * (x⁻¹ ^ 2) ^ k := by positivity
  calc
    x⁻¹ ^ 2 * (x⁻¹ ^ 2) ^ k / (4 * ((k : ℝ) + 1) ^ 2) ≤ x⁻¹ ^ 2 * (x⁻¹ ^ 2) ^ k / 4 := by
      apply div_le_div_of_nonneg_left hnum_nonneg (by norm_num only)
      nlinarith [hk1sq]
    _ = x⁻¹ ^ 2 / 4 * (x⁻¹ ^ 2) ^ k := by ring

/-- The logarithmic trivial-zero series is bounded by the Basel sum for `x > 1`. -/
theorem riemannZetaLogTrivialZeroSeries_le_pi_sq_div_twenty_four {x : ℝ} (hx : 1 < x) :
    riemannZetaLogTrivialZeroSeries x ≤
      Real.pi ^ 2 / 24 := by
  have hs := summable_logTrivialZeroTerm hx
  have hbase : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ 2) := by
    have hp : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := (hasSum_zeta_two).summable
    have hsuc : Summable ((fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) ∘ Nat.succ) :=
      hp.comp_injective Nat.succ_injective
    change Summable (fun k : ℕ => (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2) at hsuc
    simpa only [Nat.cast_add, Nat.cast_one] using hsuc
  have hsum : (∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + 1) ^ 2) = Real.pi ^ 2 / 6 := by
    have h := (hasSum_zeta_two.summable).tsum_eq_zero_add
    have h' := hasSum_zeta_two.tsum_eq
    calc
      _ = ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 := by
        symm
        simpa only [one_div, CharP.cast_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, div_zero, Nat.cast_add, Nat.cast_one, zero_add] using h
      _ = _ := h'
  rw [riemannZetaLogTrivialZeroSeries]
  calc
    (∑' k : ℕ, x⁻¹ ^ (2 * (k + 1)) / (4 * ((k : ℝ) + 1) ^ 2)) ≤
        ∑' k : ℕ, (1 : ℝ) / (4 * ((k : ℝ) + 1) ^ 2) :=
      by
      refine Summable.tsum_le_tsum ?_ hs ?_
      · intro k
        have hpow : x⁻¹ ^ (2 * (k + 1)) ≤ (1 : ℝ) := by
          have hx0 : 0 < x := lt_trans zero_lt_one hx
          have hi : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0.le
          have hil : x⁻¹ ≤ (1 : ℝ) := (inv_le_one₀ hx0).2 (le_of_lt hx)
          exact pow_le_one₀ hi hil
        exact div_le_div_of_nonneg_right hpow (by positivity)
      · simpa only [mul_comm, div_eq_mul_inv, mul_inv_rev, one_mul] using hbase.mul_left (1 / 4 : ℝ)
    _ = ∑' k : ℕ, (1 / 4 : ℝ) * (1 / ((k : ℝ) + 1) ^ 2) := by
      apply tsum_congr
      intro k
      have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      field_simp
    _ = (1 / 4 : ℝ) * (Real.pi ^ 2 / 6) := by rw [tsum_mul_left, hsum]
    _ = Real.pi ^ 2 / 24 := by ring

/-- **Finite trivial-zero partial sums (logarithmic kernel) are bounded by the full series.** -/
theorem sum_logTrivialZeroTerm_le {x : ℝ} (hx : 1 < x) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1)) :
    (∑ ρ ∈ S,
        x⁻¹ ^ (2 * (trivialZeroIndex ρ + 1)) /
          (4 * ((trivialZeroIndex ρ : ℝ) + 1) ^ 2)) ≤
      riemannZetaLogTrivialZeroSeries x := by
  have hinj : Set.InjOn trivialZeroIndex S := by
    intro ρ₁ h1 ρ₂ h2 heq
    have hs1 := trivialZeroIndex_spec (hS ρ₁ h1)
    have hs2 := trivialZeroIndex_spec (hS ρ₂ h2)
    rw [hs1, hs2, heq]
  have himg :
    (∑ ρ ∈ S,
        x⁻¹ ^ (2 * (trivialZeroIndex ρ + 1)) /
          (4 * ((trivialZeroIndex ρ : ℝ) + 1) ^ 2)) =
      ∑ k ∈ S.image trivialZeroIndex,
        x⁻¹ ^ (2 * (k + 1)) / (4 * ((k : ℝ) + 1) ^ 2) :=
    (Finset.sum_image (f := fun k : ℕ => x⁻¹ ^ (2 * (k + 1)) / (4 * ((k : ℝ) + 1) ^ 2)) hinj).symm
  rw [himg]
  have hsummable := summable_logTrivialZeroTerm hx
  have hxnn : (0 : ℝ) ≤ x := by linarith
  have hle :=
    hsummable.sum_le_tsum (S.image trivialZeroIndex)
      (fun k _ => div_nonneg (pow_nonneg (inv_nonneg.mpr hxnn) _) (by positivity))
  rwa [show
      (∑' k : ℕ, x⁻¹ ^ (2 * (k + 1)) / (4 * ((k : ℝ) + 1) ^ 2)) =
        riemannZetaLogTrivialZeroSeries x
      from rfl] at hle

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
