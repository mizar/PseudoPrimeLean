/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.MellinResolventPositive
public import PseudoPrime.AnalyticNumberTheory.General.TriangularMellinInversion

/-! # Inversion of triangular regularized resolvents -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For a positive real base, exponential scaling gives the corresponding complex
exponential factor. Apply the positive-real quotient power rule. This supports translated terms. -/
theorem triangular_resolvent_cpow_exp_scale {u : ℝ} (hu : 0 < u) (b : ℝ) (s : ℂ) :
    (((u / Real.exp b : ℝ) : ℂ) ^ (-s)) = Complex.exp ((b : ℂ) * s) * (u : ℂ) ^ (-s) := by
  rw [cpow_div_eq_cpow_mul_cpow_neg hu.le (Real.exp_pos b), neg_neg,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos b).ne'), ←
    Complex.ofReal_log (Real.exp_pos b).le, Real.log_exp, mul_comm]

/-- For nonzero parameter and argument, expand the triangular kernel into three
exponential inverse-square terms. Opposite exponentials cancel. This supports resolvent
  inversion. -/
theorem triangular_resolvent_expansion {a : ℝ} (ha : a ≠ 0) {s : ℂ} (hs : s ≠ 0) :
    Analysis.triangularMellinFunction a s =
      (Complex.exp (2 * (a : ℂ) * s) + Complex.exp (-(2 * (a : ℂ) * s)) - 2) / s ^ 2 := by
  rw [Analysis.triangularMellinFunction_of_ne_zero ha hs, div_pow]
  congr 1
  have he := Complex.exp_add ((a : ℂ) * s) (-((a : ℂ) * s))
  rw [add_neg_cancel, Complex.exp_zero] at he
  have h1 : Complex.exp ((a : ℂ) * s) ^ 2 = Complex.exp (2 * (a : ℂ) * s) := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  have h2 : Complex.exp (-((a : ℂ) * s)) ^ 2 = Complex.exp (-(2 * (a : ℂ) * s)) := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  calc
    _ =
        Complex.exp ((a : ℂ) * s) ^ 2 + Complex.exp (-((a : ℂ) * s)) ^ 2 -
          2 * (Complex.exp ((a : ℂ) * s) * Complex.exp (-((a : ℂ) * s))) :=
      by ring
    _ = _ := by rw [← he, h1, h2, mul_one]

/-- For nonzero parameter and line coordinate and positive argument, the triangular
resolvent inverse integrand splits into three translated scalar resolvents. Expand the
kernel and scale the powers. This is the pointwise identity for splitting the integral. -/
theorem triangular_resolvent_inverse_integrand_eq {α : ℂ} {a c u : ℝ} (ha : a ≠ 0) (hc : c ≠ 0)
    (hu : 0 < u) (t : ℝ) :
    (u : ℂ) ^ (-((c : ℂ) + t * Complex.I)) *
        (Analysis.triangularMellinFunction a ((c : ℂ) + t * Complex.I) /
          (((c : ℂ) + t * Complex.I) - α)) =
      ((u / Real.exp (2 * a) : ℝ) : ℂ) ^ (-((c : ℂ) + t * Complex.I)) /
            (((c : ℂ) + t * Complex.I) ^ 2 * (((c : ℂ) + t * Complex.I) - α)) +
          ((u / Real.exp (-2 * a) : ℝ) : ℂ) ^ (-((c : ℂ) + t * Complex.I)) /
            (((c : ℂ) + t * Complex.I) ^ 2 * (((c : ℂ) + t * Complex.I) - α)) -
        2 *
          ((u : ℂ) ^ (-((c : ℂ) + t * Complex.I)) /
            (((c : ℂ) + t * Complex.I) ^ 2 * (((c : ℂ) + t * Complex.I) - α))) := by
  have hs : (c : ℂ) + t * Complex.I ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at hr
    exact hc hr
  rw [triangular_resolvent_expansion ha hs, triangular_resolvent_cpow_exp_scale hu (2 * a),
    triangular_resolvent_cpow_exp_scale hu (-2 * a)]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_neg]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring_nf

/-- For a pole with negative real part, positive line and positive argument,
the scalar resolvent inverse integrand is integrable. Multiply the integrable resolvent
kernel by the bounded complex power on the fixed line. This permits finite integral splitting. -/
theorem integrable_resolvent_inverse_of_pos {α : ℂ} (hα : α.re < 0) {c u : ℝ} (hc : 0 < c)
    (hu : 0 < u) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        (u : ℂ) ^ (-((c : ℂ) + t * Complex.I)) /
          (((c : ℂ) + t * Complex.I) ^ 2 * (((c : ℂ) + t * Complex.I) - α))) := by
  have hb :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ 1 / (((c : ℂ) + t * Complex.I) ^ 2 * (((c : ℂ) + t * Complex.I) - α))) := by
    simpa only [Complex.VerticalIntegrable, one_div] using verticalIntegrable_resolventKernel hα hc
  have hm :
    MeasureTheory.AEStronglyMeasurable (fun t : ℝ ↦ (u : ℂ) ^ (-((c : ℂ) + t * Complex.I)))
      MeasureTheory.volume := by
    simp only [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne')]
    exact
      (Complex.continuous_exp.comp
          (continuous_const.mul
            ((continuous_const.add
                (Complex.continuous_ofReal.mul continuous_const)).neg))).aestronglyMeasurable
  have hh :=
    hb.bdd_mul hm (c := u ^ (-c))
      (Filter.Eventually.of_forall
        (fun t ↦ by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hu]
          simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
            le_refl]))
  simpa only [div_eq_mul_inv, one_mul] using hh

/-- For a pole with negative real part, nonzero triangular parameter, positive line
and positive argument, the triangular resolvent inverse transform equals three translated
regularized weights. Split integrable terms and invert each scalar resolvent.
This evaluates individual Gamma-pole contributions before summing the digamma series. -/
theorem mellinInv_triangular_resolvent_weight_combination {α : ℂ} (hα : α.re < 0) {a c u : ℝ}
    (ha : a ≠ 0) (hc : 0 < c) (hu : 0 < u) :
    mellinInv c (fun s : ℂ ↦ Analysis.triangularMellinFunction a s / (s - α)) u =
      mellinResolventWeight α (u / Real.exp (2 * a)) +
          mellinResolventWeight α (u / Real.exp (-2 * a)) -
        2 * mellinResolventWeight α u := by
  let f := fun (v t : ℝ) ↦
    (v : ℂ) ^ (-((c : ℂ) + t * Complex.I)) /
      (((c : ℂ) + t * Complex.I) ^ 2 * (((c : ℂ) + t * Complex.I) - α))
  have hf {v : ℝ} (hv : 0 < v) : MeasureTheory.Integrable (f v) :=
    integrable_resolvent_inverse_of_pos hα hc hv
  have hp :
    (fun t : ℝ ↦
        (u : ℂ) ^ (-((c : ℂ) + t * Complex.I)) *
          (Analysis.triangularMellinFunction a ((c : ℂ) + t * Complex.I) /
            (((c : ℂ) + t * Complex.I) - α))) =
      fun t ↦ f (u / Real.exp (2 * a)) t + f (u / Real.exp (-2 * a)) t - 2 * f u t := by
    funext t
    exact triangular_resolvent_inverse_integrand_eq ha hc.ne' hu t
  have h1 := mellinInv_resolventKernel_eq_of_pos hα hc (div_pos hu (Real.exp_pos (2 * a)))
  have h2 := mellinInv_resolventKernel_eq_of_pos hα hc (div_pos hu (Real.exp_pos (-2 * a)))
  have h0 := mellinInv_resolventKernel_eq_of_pos hα hc hu
  rw [← h1, ← h2, ← h0]
  simp only [mellinInv, smul_eq_mul]
  rw [hp]
  have hadd :=
    MeasureTheory.integral_add (hf (div_pos hu (Real.exp_pos (2 * a))))
      (hf (div_pos hu (Real.exp_pos (-2 * a))))
  change
    (∫ t : ℝ, f (u / Real.exp (2 * a)) t + f (u / Real.exp (-2 * a)) t) =
      (∫ t : ℝ, f (u / Real.exp (2 * a)) t) + (∫ t : ℝ, f (u / Real.exp (-2 * a)) t) at hadd
  have hsub :=
    MeasureTheory.integral_sub
      ((hf (div_pos hu (Real.exp_pos (2 * a)))).add (hf (div_pos hu (Real.exp_pos (-2 * a)))))
      ((hf hu).const_mul 2)
  change
    (∫ t : ℝ, (f (u / Real.exp (2 * a)) t + f (u / Real.exp (-2 * a)) t) - 2 * f u t) =
      (∫ t : ℝ, f (u / Real.exp (2 * a)) t + f (u / Real.exp (-2 * a)) t) -
        (∫ t : ℝ, 2 * f u t) at hsub
  rw [hsub, hadd, MeasureTheory.integral_const_mul]
  dsimp only [f]
  simp only [div_eq_mul_inv, one_mul, smul_sub, smul_add, Complex.real_smul, Complex.ofReal_mul]
  ring

/-- For positive parameter and line and a pole with negative real part, the inverse
transform vanishes beyond exp(2a). All three translated regularized weights are outside
their support. This supplies the exterior branch of the Gamma-pole evaluation. -/
theorem mellinInv_triangular_resolvent_eq_zero_of_large_argument {α : ℂ} (hα : α.re < 0) {a c u : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hu : Real.exp (2 * a) < u) :
    mellinInv c (fun s : ℂ ↦ Analysis.triangularMellinFunction a s / (s - α)) u = 0 := by
  have hu0 : 0 < u := (Real.exp_pos _).trans hu
  have he : Real.exp (-2 * a) ≤ Real.exp (2 * a) := Real.exp_le_exp.mpr (by linarith only [ha])
  have h0 : 1 < u := (Real.one_le_exp (by linarith only [ha] : 0 ≤ 2 * a)).trans_lt hu
  rw [mellinInv_triangular_resolvent_weight_combination hα ha.ne' hc hu0,
    mellinResolventWeight_eq_zero_of_one_lt α ((one_lt_div (Real.exp_pos _)).mpr hu),
    mellinResolventWeight_eq_zero_of_one_lt α ((one_lt_div (Real.exp_pos _)).mpr (he.trans_lt hu)),
    mellinResolventWeight_eq_zero_of_one_lt α h0]
  simp only [add_zero, mul_zero, sub_zero]

end PseudoPrime.AnalyticNumberTheory.General
