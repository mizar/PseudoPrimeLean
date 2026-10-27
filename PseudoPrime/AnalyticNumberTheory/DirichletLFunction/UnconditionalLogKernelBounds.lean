/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalLogOriginRegularization

/-! # Uniform regularized half-scale bounds in the left critical strip -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For nonnegative real exponents `b ≤ a`, a nonzero complex argument with
`a * ‖z‖ ≤ 1` has a quadratically bounded exponential difference after subtracting
its linear term. Apply the exponential Taylor bound twice and divide by `z²`.
This gives a bound uniform as the argument approaches zero. -/
theorem norm_exp_difference_linear_remainder_le_small {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) {z : ℂ}
    (hz : z ≠ 0) (hsmall : a * ‖z‖ ≤ 1) :
    ‖(Complex.exp ((a : ℂ) * z) - Complex.exp ((b : ℂ) * z) - ((a - b : ℝ) : ℂ) * z) / z ^ 2‖ ≤
      2 * a ^ 2 := by
  have ha : 0 ≤ a := hb.trans hba
  have hna : ‖(a : ℂ) * z‖ = a * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
  have hnb : ‖(b : ℂ) * z‖ = b * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb]
  have hsmallb : b * ‖z‖ ≤ 1 := (mul_le_mul_of_nonneg_right hba (norm_nonneg z)).trans hsmall
  have hfirst :=
    Complex.norm_exp_sub_one_sub_id_le
      (by
        rw [hna]; exact hsmall)
  have hsecond :=
    Complex.norm_exp_sub_one_sub_id_le
      (by
        rw [hnb]; exact hsmallb)
  rw [hna] at hfirst
  rw [hnb] at hsecond
  have he :
    Complex.exp ((a : ℂ) * z) - Complex.exp ((b : ℂ) * z) - ((a - b : ℝ) : ℂ) * z =
      (Complex.exp ((a : ℂ) * z) - 1 - (a : ℂ) * z) -
        (Complex.exp ((b : ℂ) * z) - 1 - (b : ℂ) * z) := by
    push_cast
    ring
  rw [norm_div, norm_pow]
  apply (div_le_iff₀ (pow_pos (norm_pos_iff.mpr hz) 2)).mpr
  rw [he]
  have hnorm :=
    norm_sub_le (Complex.exp ((a : ℂ) * z) - 1 - (a : ℂ) * z)
      (Complex.exp ((b : ℂ) * z) - 1 - (b : ℂ) * z)
  have hsq : b ^ 2 ≤ a ^ 2 := (sq_le_sq₀ hb ha).mpr hba
  have hprod := mul_nonneg (sub_nonneg.mpr hsq) (sq_nonneg ‖z‖)
  nlinarith only [hnorm, hfirst, hsecond, hprod]

/-- For a nonnegative real scale and any complex exponent, the half-scale
power factor equals the difference of the two scale powers. Use the complex
power quotient identity on the nonnegative real axis. This exposes the common
linear term in the origin regularization. -/
theorem half_power_difference_eq {x : ℝ} (hx : 0 ≤ x) (z : ℂ) :
    (1 - (2 : ℂ) ^ (-z)) * (x : ℂ) ^ z = (x : ℂ) ^ z - ((x / 2 : ℝ) : ℂ) ^ z := by
  have he := Complex.div_cpow_ofReal_nonneg hx (by norm_num only : (0 : ℝ) ≤ 2) z
  rw [← Complex.ofReal_div, Complex.ofReal_ofNat] at he
  rw [he, Complex.cpow_neg]
  ring

/-- For scale at least two and a nonzero argument with `log x * ‖z‖ ≤ 1`,
the half-power difference minus its linear term, divided by `z²`, is bounded
by twice `log² x`. Rewrite both powers as exponentials and apply the small
argument Taylor estimate. This controls the origin neighborhood. -/
theorem norm_half_power_linear_remainder_le_small {x : ℝ} (hx : 2 ≤ x) {z : ℂ} (hz : z ≠ 0)
    (hsmall : Real.log x * ‖z‖ ≤ 1) :
    ‖(((1 - (2 : ℂ) ^ (-z)) * (x : ℂ) ^ z - (Real.log 2 : ℂ) * z) / z ^ 2)‖ ≤
      2 * (Real.log x) ^ 2 := by
  have hxpos : 0 < x := by linarith only [hx]
  have hhalf : 0 < x / 2 := div_pos hxpos (by norm_num only)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num only)
  have hloghalf : 0 ≤ Real.log (x / 2) := Real.log_nonneg (by linarith only [hx])
  have hlog := Real.log_div hxpos.ne' (by norm_num only : (2 : ℝ) ≠ 0)
  have hba : Real.log (x / 2) ≤ Real.log x := by linarith only [hlog, hlog2]
  have hsub : Real.log x - Real.log (x / 2) = Real.log 2 := by linarith only [hlog]
  have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hxpos.ne'
  have hhne : ((x / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hhalf.ne'
  rw [half_power_difference_eq hxpos.le, Complex.cpow_def_of_ne_zero hxne,
    Complex.cpow_def_of_ne_zero hhne, ← Complex.ofReal_log hxpos.le, ← Complex.ofReal_log hhalf.le,
    ← hsub]
  exact norm_exp_difference_linear_remainder_le_small hloghalf hba hz hsmall

/-- For scale at least two and real part between zero and one half, the
half-power factor is bounded by twice the square root of the scale. Bound both
scale powers on the positive real axis. This supplies the large-argument bound. -/
theorem norm_half_power_le_two_sqrt {x : ℝ} (hx : 2 ≤ x) {z : ℂ} (hzlo : 0 ≤ z.re)
    (hzhi : z.re ≤ 1 / 2) : ‖(1 - (2 : ℂ) ^ (-z)) * (x : ℂ) ^ z‖ ≤ 2 * Real.sqrt x := by
  have hxpos : 0 < x := by linarith only [hx]
  have hhalf : 0 < x / 2 := div_pos hxpos (by norm_num only)
  have hxone : 1 ≤ x := by linarith only [hx]
  have hfirst : ‖(x : ℂ) ^ z‖ ≤ Real.sqrt x := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hxone hzhi
  have hsecond : ‖((x / 2 : ℝ) : ℂ) ^ z‖ ≤ Real.sqrt x := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hhalf]
    exact
      (Real.rpow_le_rpow hhalf.le (by linarith only [hxpos] : x / 2 ≤ x) hzlo).trans
        (by
          rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hxone hzhi)
  rw [half_power_difference_eq hxpos.le]
  exact (norm_sub_le _ _).trans (by linarith only [hfirst, hsecond])

/-- For scale at least two, real part in the left half of the critical strip,
and `1 ≤ log x * ‖z‖`, the linear-subtracted half-power quotient has a square-root
and logarithmic bound. Use the power norms and the lower bound on the argument.
This complements the Taylor estimate near zero. -/
theorem norm_half_power_linear_remainder_le_large {x : ℝ} (hx : 2 ≤ x) {z : ℂ} (hzlo : 0 ≤ z.re)
    (hzhi : z.re ≤ 1 / 2) (hz : z ≠ 0) (hlarge : 1 ≤ Real.log x * ‖z‖) :
    ‖(((1 - (2 : ℂ) ^ (-z)) * (x : ℂ) ^ z - (Real.log 2 : ℂ) * z) / z ^ 2)‖ ≤
      2 * Real.sqrt x * (Real.log x) ^ 2 + Real.log 2 * Real.log x := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have ha : 0 ≤ Real.log x := Real.log_nonneg (by linarith only [hx])
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num only)
  have hinv : 1 / ‖z‖ ≤ Real.log x := (div_le_iff₀ hn).mpr hlarge
  have hsq : (1 / ‖z‖) ^ 2 ≤ (Real.log x) ^ 2 := (sq_le_sq₀ (one_div_nonneg.mpr hn.le) ha).mpr hinv
  have hpower := norm_half_power_le_two_sqrt hx hzlo hzhi
  have hlognorm : ‖(Real.log 2 : ℂ)‖ = Real.log 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl]
  have hnum := norm_sub_le ((1 - (2 : ℂ) ^ (-z)) * (x : ℂ) ^ z) ((Real.log 2 : ℂ) * z)
  rw [norm_mul (Real.log 2 : ℂ) z, hlognorm] at hnum
  rw [norm_div, norm_pow]
  calc
    _ ≤ (2 * Real.sqrt x + Real.log 2 * ‖z‖) / ‖z‖ ^ 2 :=
      div_le_div_of_nonneg_right (hnum.trans (add_le_add hpower le_rfl)) (sq_nonneg _)
    _ = 2 * Real.sqrt x * (1 / ‖z‖) ^ 2 + Real.log 2 * (1 / ‖z‖) := by
      rw [add_div, mul_div_assoc, pow_two, mul_div_mul_right _ _ hn.ne']
      ring
    _ ≤ _ :=
      add_le_add
        (mul_le_mul_of_nonneg_left hsq (mul_nonneg (by norm_num only) (Real.sqrt_nonneg x)))
        (mul_le_mul_of_nonneg_left hinv hl)

/-- For scale at least two and a nonzero argument with real part between zero
and one half, the regularized half-power kernel has a uniform square-root and
logarithmic bound. Combine the small and large argument estimates and bound the
regular correction at two. No inverse distance from zero remains. -/
theorem norm_regularized_half_kernel_le_low_re {x : ℝ} (hx : 2 ≤ x) {z : ℂ} (hzlo : 0 ≤ z.re)
    (hzhi : z.re ≤ 1 / 2) (hz : z ≠ 0) :
    ‖(((1 - (2 : ℂ) ^ (-z)) * (x : ℂ) ^ z - (Real.log 2 : ℂ) * z) / z ^ 2) -
          (Real.log 2 : ℂ) / ((2 : ℂ) - z)‖ ≤
      2 * Real.sqrt x * (Real.log x) ^ 2 + Real.log 2 * (Real.log x + 1) := by
  have ha : 0 ≤ Real.log x := Real.log_nonneg (by linarith only [hx])
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num only)
  have hsqrt : 1 ≤ Real.sqrt x := by
    have h := Real.sqrt_le_sqrt (by linarith only [hx] : 1 ≤ x)
    simpa only [Real.sqrt_one] using h
  have hfirst :
    ‖(((1 - (2 : ℂ) ^ (-z)) * (x : ℂ) ^ z - (Real.log 2 : ℂ) * z) / z ^ 2)‖ ≤
      2 * Real.sqrt x * (Real.log x) ^ 2 + Real.log 2 * Real.log x := by
    by_cases hsmall : Real.log x * ‖z‖ ≤ 1
    · have hb := norm_half_power_linear_remainder_le_small hx hz hsmall
      have hprod :=
        mul_nonneg (by linarith only [hsqrt] : 0 ≤ Real.sqrt x - 1) (sq_nonneg (Real.log x))
      nlinarith only [hb, hprod, mul_nonneg hl ha]
    · exact
        norm_half_power_linear_remainder_le_large hx hzlo hzhi hz (le_of_lt (lt_of_not_ge hsmall))
  have hden : 1 ≤ ‖(2 : ℂ) - z‖ := by
    have hb := Complex.re_le_norm ((2 : ℂ) - z)
    rw [Complex.sub_re, Complex.re_ofNat] at hb
    linarith only [hb, hzhi]
  have hsecond : ‖(Real.log 2 : ℂ) / ((2 : ℂ) - z)‖ ≤ Real.log 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl]
    exact div_le_self hl hden
  exact (norm_sub_le _ _).trans (by linarith only [hfirst, hsecond])

/-- For a primitive nonprincipal character and its nonprincipal inverse, each
regularized completed-zero term with real part at most one half is bounded by
its divisor multiplicity times an explicit square-root and logarithmic factor.
The zero-free half-planes and quadratic cancellation remove the origin singularity.
This permits summing the left-strip terms using unconditional local counts. -/
theorem norm_regularizedLogHalfZeroTerm_le_low_re {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) {ρ : ℂ}
    (hre : ρ.re ≤ 1 / 2) :
    ‖regularizedLogHalfZeroTerm χ x ρ‖ ≤
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        (2 * Real.sqrt x * (Real.log x) ^ 2 + Real.log 2 * (Real.log x + 1)) := by
  let D := MeromorphicOn.divisor χ.completedLFunction Set.univ ρ
  by_cases hD : D = 0
  · have hDz : MeromorphicOn.divisor χ.completedLFunction Set.univ ρ = 0 := hD
    simp only [regularizedLogHalfZeroTerm, completedLogHalfZeroTerm, hDz, Int.cast_zero, zero_mul,
      zero_div, mul_zero, sub_self, norm_zero, le_refl]
  · have hz := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD
    have hρ : ρ ≠ 0 := by
      intro he
      exact dirichletCompletedLFunction_zero_ne_zero_of_primitive hp hne (he ▸ hz)
    have hlo := completedLFunction_zero_re_pos hp hinv hz
    have hAn : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
      (χ.differentiable_completedLFunction hne).analyticAt z
    have hDn : (0 : ℝ) ≤ D := by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn ρ
    rw [regularizedLogHalfZeroTerm_eq_cancelled_kernel χ x hρ, norm_mul, Complex.norm_intCast,
      abs_of_nonneg hDn]
    exact mul_le_mul_of_nonneg_left (norm_regularized_half_kernel_le_low_re hx hlo.le hre hρ) hDn

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
