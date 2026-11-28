/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangleFourier
public import PseudoPrime.Analysis.ShiftedPoleProfile
import Mathlib.Tactic.LinearCombination

/-! # Fourier recurrence for opposite reciprocal poles -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Split a reciprocal product of two opposite poles by lowering one of its
orders. Their denominators add to twice the pole parameter. -/
public theorem opposite_pole_split {a z : ℂ} (ha : a ≠ 0) (hp : a + z ≠ 0) (hm : a - z ≠ 0)
    (p q : ℕ) :
    1 / ((a + z) ^ (p + 1) * (a - z) ^ (q + 1)) =
      (1 / ((a + z) ^ p * (a - z) ^ (q + 1)) + 1 / ((a + z) ^ (p + 1) * (a - z) ^ q)) /
        (2 * a) := by
  have ha₂ : (2 : ℂ) * a ≠ 0 := mul_ne_zero (by norm_num only) ha
  apply (eq_div_iff ha₂).mpr
  have h₁ :
    1 / ((a + z) ^ p * (a - z) ^ (q + 1)) = (a + z) / ((a + z) ^ (p + 1) * (a - z) ^ (q + 1)) := by
    rw [pow_succ (a + z) p, mul_right_comm ((a + z) ^ p) (a + z)]
    simpa only [one_mul] using (mul_div_mul_right 1 _ hp).symm
  have h₂ :
    1 / ((a + z) ^ (p + 1) * (a - z) ^ q) = (a - z) / ((a + z) ^ (p + 1) * (a - z) ^ (q + 1)) := by
    rw [pow_succ (a - z) q, ← mul_assoc]
    simpa only [one_mul] using (mul_div_mul_right 1 _ hm).symm
  rw [h₁, h₂, ← add_div, div_mul_eq_mul_div, one_mul]
  ring

/-- The reciprocal quadratic power on the Fourier line is the product of
two reciprocal pole powers of equal order. -/
public theorem cauchy_power_opposite_poles (a t : ℝ) (m : ℕ) :
    (((a ^ 2 + t ^ 2 : ℝ) : ℂ) ^ m) =
      ((a : ℂ) + Complex.I * (t : ℂ)) ^ m * ((a : ℂ) - Complex.I * (t : ℂ)) ^ m := by
  rw [← mul_pow]
  congr 1
  simp only [Complex.ofReal_add, Complex.ofReal_pow]
  linear_combination ((t : ℂ) ^ 2) * Complex.I_sq

/-- Fourier inversion gives the full complex integral of the first Cauchy power.
The transform is real because the original exponential is even. -/
public theorem cauchy_fourier_one {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (∫ t : ℝ, Complex.exp ((x * t : ℝ) * Complex.I) / (((a ^ 2 + t ^ 2 : ℝ) : ℂ))) =
      ((Real.pi / a * Real.exp (-a * |x|) : ℝ) : ℂ) := by
  let f (t : ℝ) : ℂ := Real.exp (-(2 * Real.pi * a) * |t|)
  have hpa : 0 < 2 * Real.pi * a := mul_pos (mul_pos (by norm_num only) Real.pi_pos) ha
  have hf : MeasureTheory.Integrable f := by
    simpa only [f, Complex.ofReal_zero, mul_zero, zero_mul, sub_zero, Complex.ofReal_exp,
      Complex.ofReal_mul, Complex.ofReal_neg] using (triangle_exp_transform hpa 0).1
  have hg : MeasureTheory.Integrable (FourierTransform.fourier f) := by
    apply (((Analysis.integrable_cauchy_of_pos ha).const_mul (a / Real.pi)).ofReal (𝕜 := ℂ)).congr
    exact Filter.Eventually.of_forall fun t ↦ (triangle_fourier_exp ha t).symm
  let y := x / (2 * Real.pi)
  have he :=
    congrFun
      ((show Continuous f by
            unfold f; fun_prop).fourierInv_fourier_eq
        hf hg)
      y
  rw [Real.fourierInv_eq'] at he
  have hπ : (2 * Real.pi) ≠ 0 := mul_ne_zero (by norm_num only) Real.pi_ne_zero
  have hy (t : ℝ) : 2 * Real.pi * (t * y) = x * t := by
    unfold y
    rw [← mul_assoc, mul_comm (2 * Real.pi) t, mul_assoc, ← mul_div_assoc (2 * Real.pi) x,
      mul_div_cancel_left₀ _ hπ, mul_comm]
  have hpoint (t : ℝ) :
    Complex.exp (((2 * Real.pi * inner ℝ t y : ℝ) : ℂ) * Complex.I) • FourierTransform.fourier f t =
      ((a / Real.pi : ℝ) : ℂ) *
        (Complex.exp ((x * t : ℝ) * Complex.I) / (((a ^ 2 + t ^ 2 : ℝ) : ℂ))) := by
    rw [triangle_fourier_exp ha, Real.inner_apply, hy, smul_eq_mul, Complex.ofReal_div]
    simp only [div_eq_mul_inv]
    ring
  simp_rw [hpoint] at he
  rw [MeasureTheory.integral_const_mul] at he
  have hx : -(2 * Real.pi * a) * |y| = -a * |x| := by
    rw [show |y| = |x| / (2 * Real.pi) by
        unfold y
        rw [abs_div, abs_of_pos (mul_pos (by norm_num only) Real.pi_pos)]]
    apply (mul_div_assoc _ _ _).symm.trans
    apply (div_eq_iff hπ).mpr
    ring
  change ((a / Real.pi : ℝ) : ℂ) * _ = ((Real.exp (-(2 * Real.pi * a) * |y|) : ℝ) : ℂ) at he
  rw [hx] at he
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (div_ne_zero ha.ne' Real.pi_ne_zero))
  rw [he, ← Complex.ofReal_mul, ← mul_assoc, div_mul_div_comm, mul_comm Real.pi a,
    div_self (mul_ne_zero ha.ne' Real.pi_ne_zero), one_mul]

/-- The two pole factors on the imaginary axis have the same squared norm. -/
private theorem pole_line_norm_sq (a t : ℝ) :
    ‖(a : ℂ) + Complex.I * (t : ℂ)‖ ^ 2 = a ^ 2 + t ^ 2 ∧
      ‖(a : ℂ) - Complex.I * (t : ℂ)‖ ^ 2 = a ^ 2 + t ^ 2 := by
  constructor <;>
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.sub_re,
      Complex.add_im, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im] <;>
    ring

/-- Fourier-modulated products of opposite poles. -/
@[expose]
public noncomputable def oppositePoleMode (a x : ℝ) (p q : ℕ) (t : ℝ) : ℂ :=
  Complex.exp ((x * t : ℝ) * Complex.I) /
    (((a : ℂ) + Complex.I * (t : ℂ)) ^ p * ((a : ℂ) - Complex.I * (t : ℂ)) ^ q)

/-- Opposite pole products of total order at least two are absolutely integrable
for pole distance at least one, as in both high Gaussian kernels. -/
public theorem integrable_opposite_pole_mode {a : ℝ} (ha : 1 ≤ a) (x : ℝ) {p q : ℕ}
    (horder : 2 ≤ p + q) : MeasureTheory.Integrable (oppositePoleMode a x p q) := by
  have ha' : 0 < a := zero_lt_one.trans_le ha
  have hn (t : ℝ) : 1 ≤ ‖(a : ℂ) + Complex.I * (t : ℂ)‖ := by
    have h := Complex.abs_re_le_norm ((a : ℂ) + Complex.I * (t : ℂ))
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im, mul_zero, zero_mul,
      sub_zero, add_zero, Complex.ofReal_re, abs_of_pos ha'] at h
    exact ha.trans h
  have he (t : ℝ) : ‖(a : ℂ) - Complex.I * (t : ℂ)‖ = ‖(a : ℂ) + Complex.I * (t : ℂ)‖ := by
    have h := pole_line_norm_sq a t
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (h.2.trans h.1.symm)
  apply (Analysis.integrable_cauchy_of_pos ha').mono'
  · apply Continuous.aestronglyMeasurable
    unfold oppositePoleMode
    have ht := Complex.continuous_ofReal
    apply
      (Complex.continuous_exp.comp
            ((ht.comp (continuous_const.mul continuous_id)).mul continuous_const)).div
        (((continuous_const.add (continuous_const.mul ht)).pow p).mul
          ((continuous_const.sub (continuous_const.mul ht)).pow q))
    intro t
    exact
      mul_ne_zero (pow_ne_zero _ (norm_pos_iff.mp (zero_lt_one.trans_le (hn t))))
        (pow_ne_zero _ (norm_pos_iff.mp ((he t).symm ▸ zero_lt_one.trans_le (hn t))))
  · apply Filter.Eventually.of_forall
    intro t
    unfold oppositePoleMode
    simp only [norm_div, norm_mul, norm_pow, he t, ← pow_add, Complex.norm_exp, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, mul_zero, zero_mul, sub_self, Real.exp_zero]
    rw [← (pole_line_norm_sq a t).1, one_div]
    exact inv_anti₀ (pow_pos (zero_lt_one.trans_le (hn t)) _) (pow_le_pow_right₀ (hn t) horder)

/-- The mixed-pole Fourier integrals satisfy the same lowering recurrence.
The order hypothesis keeps both terms on the right absolutely integrable. -/
public theorem opposite_pole_fourier_step {a : ℝ} (ha : 1 ≤ a) (x : ℝ) (p q : ℕ) (hpq : 1 ≤ p + q) :
    (∫ t : ℝ, oppositePoleMode a x (p + 1) (q + 1) t) =
      ((∫ t : ℝ, oppositePoleMode a x p (q + 1) t) + (∫ t : ℝ, oppositePoleMode a x (p + 1) q t)) /
        (2 * (a : ℂ)) := by
  have ha' := zero_lt_one.trans_le ha
  have h₁ : 2 ≤ p + (q + 1) := by
    rw [← Nat.add_assoc]
    exact Nat.add_le_add_right hpq 1
  have h₂ : 2 ≤ (p + 1) + q := by
    rw [Nat.add_right_comm]
    exact Nat.add_le_add_right hpq 1
  rw [←
    MeasureTheory.integral_add (integrable_opposite_pole_mode ha x h₁)
      (integrable_opposite_pole_mode ha x h₂),
    ← MeasureTheory.integral_div]
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  have hplus : (a : ℂ) + Complex.I * (t : ℂ) ≠ 0 := by
    intro h
    have hc := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im, mul_zero, zero_mul,
      sub_zero, add_zero, Complex.ofReal_re, Complex.zero_re] at hc
    exact ha'.ne' hc
  have hminus : (a : ℂ) - Complex.I * (t : ℂ) ≠ 0 := by
    intro h
    have hc := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im, mul_zero, zero_mul,
      sub_zero, Complex.ofReal_re, Complex.zero_re] at hc
    exact ha'.ne' hc
  unfold oppositePoleMode
  have hs := opposite_pole_split (Complex.ofReal_ne_zero.mpr ha'.ne') hplus hminus p q
  simp only [div_eq_mul_inv, one_mul] at hs
  simp only [div_eq_mul_inv]
  rw [← mul_add, mul_assoc, ← hs]

/-- The symmetric mixed-order integral is the integral of the corresponding Cauchy power. -/
public theorem cauchy_fourier_eq_opposite (a x : ℝ) (m : ℕ) :
    (∫ t : ℝ, Complex.exp ((x * t : ℝ) * Complex.I) / (((a ^ 2 + t ^ 2 : ℝ) : ℂ) ^ m)) =
      ∫ t : ℝ, oppositePoleMode a x m m t := by
  simp only [oppositePoleMode, cauchy_power_opposite_poles]

/-- The lowering recurrence stops at the integrable symmetric pair of order one. -/
public theorem opposite_pole_fourier_base {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (∫ t : ℝ, oppositePoleMode a x 1 1 t) = ((Real.pi / a * Real.exp (-a * |x|) : ℝ) : ℂ) := by
  rw [← cauchy_fourier_eq_opposite]
  simpa only [pow_one] using cauchy_fourier_one ha x

/-- The terminal positive pole is evaluated by the existing shifted-pole Mellin inversion. -/
public theorem opposite_pole_fourier_positive {a : ℝ} (ha : 0 < a) (x : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (∫ t : ℝ, oppositePoleMode a x (n + 1) 0 t) =
      (2 * (Real.pi : ℂ)) * (Analysis.shiftedPoleProfile n a 0 (Real.exp (-x)) : ℂ) := by
  have h :=
    Analysis.inverseMellin_shiftedPole hn (σ := 0) (ρ := a)
      (by
        rw [zero_add]; exact ha)
      (Real.exp_pos (-x)) 0
  unfold Analysis.inverseMellin at h
  simp only [Complex.ofReal_zero, zero_add, zero_mul, Complex.exp_zero] at h
  have hphase (t : ℝ) :
    (↑(Real.exp (-x)) : ℂ) ^ (-(Complex.I * (t : ℂ))) = Complex.exp ((x * t : ℝ) * Complex.I) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'), ←
      Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, Complex.ofReal_neg, Complex.ofReal_mul]
    congr 1
    ring
  have he (t : ℝ) :
    1 / (Complex.I * (t : ℂ) + (a : ℂ)) ^ (n + 1) *
        (↑(Real.exp (-x)) : ℂ) ^ (-(Complex.I * (t : ℂ))) =
      oppositePoleMode a x (n + 1) 0 t := by
    rw [hphase, mul_comm, mul_one_div]
    simp only [oppositePoleMode, pow_zero, mul_one, add_comm]
  simp only [he, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat,
    Complex.ofReal_one] at h
  have hπ : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num only) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [← h, ← mul_assoc, mul_one_div, div_self hπ, one_mul]

/-- Negating the Fourier variable interchanges the two pole factors. -/
public theorem opposite_pole_fourier_reflect (a x : ℝ) (p q : ℕ) :
    (∫ t : ℝ, oppositePoleMode a x p q t) = ∫ t : ℝ, oppositePoleMode a (-x) q p t := by
  rw [← MeasureTheory.integral_neg_eq_self (fun t ↦ oppositePoleMode a (-x) q p t)]
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  simp only [oppositePoleMode, Complex.ofReal_neg, mul_neg, neg_mul, neg_neg, sub_neg_eq_add,
    ← sub_eq_add_neg]
  rw [mul_comm (((a : ℂ) - Complex.I * (t : ℂ)) ^ q)]

end PseudoPrime.PrimeTestBounds.MillerRabin
