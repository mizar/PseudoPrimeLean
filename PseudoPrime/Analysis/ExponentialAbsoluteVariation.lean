/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialPolynomialMoments

/-! # Affine error integrals retaining the sign change of exponential variation -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: nonnegative a,b and cutoff y. Claim: the affine-weighted absolute
variation integral is at most 2(a+3b)exp(-1)-b. Split at one and evaluate the
quadratic exponential primitives, keeping the nonnegative tail remainder.
Role: avoid replacing abs(u-1) by u+1 in principal error bounds. -/
theorem integral_affine_abs_exponential_variation_le {a b y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hy : 0 ≤ y) :
    (∫ u in (0 : ℝ)..y, (a + b * u) * |u - 1| * Real.exp (-u)) ≤
      2 * (a + 3 * b) * Real.exp (-1) - b := by
  let f := fun u : ℝ ↦ (a + b * u) * |u - 1| * Real.exp (-u)
  have hcont : Continuous f :=
    ((continuous_const.add (continuous_const.mul continuous_id)).mul
          (continuous_id.sub continuous_const).abs).mul
      (Real.continuous_exp.comp continuous_id.neg)
  have hleft : (∫ u in (0 : ℝ)..1, f u) = (a + 3 * b) * Real.exp (-1) - b := by
    have he :
      (∫ u in (0 : ℝ)..1, f u) =
        ∫ u in (0 : ℝ)..1, (a + (b - a) * u + (-b) * u ^ 2) * Real.exp (-u) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le (by norm_num only : (0 : ℝ) ≤ 1)] at hu
      dsimp only [f]
      rw [abs_of_nonpos (sub_nonpos.mpr hu.2)]
      ring
    rw [he, integral_exponential_quadratic]
    ring
  by_cases hsmall : y ≤ 1
  · have hn : 0 ≤ ∫ u in y..(1 : ℝ), f u :=
      intervalIntegral.integral_nonneg hsmall
        (fun u hu ↦
          mul_nonneg (mul_nonneg (add_nonneg ha (mul_nonneg hb (hy.trans hu.1))) (abs_nonneg _))
            (Real.exp_pos _).le)
    have hj :=
      intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
        (hcont.intervalIntegrable (0 : ℝ) y) (hcont.intervalIntegrable y 1)
    have hp := mul_nonneg (show 0 ≤ a + 3 * b by linarith only [ha, hb]) (Real.exp_pos (-1)).le
    change (∫ u in (0 : ℝ)..y, f u) ≤ _
    linarith only [hleft, hn, hj, hp]
  · have hy1 := le_of_not_ge hsmall
    have he :
      (∫ u in (1 : ℝ)..y, f u) =
        ∫ u in (1 : ℝ)..y, (-a + (a - b) * u + b * u ^ 2) * Real.exp (-u) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le hy1] at hu
      dsimp only [f]
      rw [abs_of_nonneg (sub_nonneg.mpr hu.1)]
      ring
    have hc : Continuous (fun u : ℝ ↦ (-a + (a - b) * u + b * u ^ 2) * Real.exp (-u)) :=
      ((continuous_const.add (continuous_const.mul continuous_id)).add
            (continuous_const.mul (continuous_id.pow 2))).mul
        (Real.continuous_exp.comp continuous_id.neg)
    have hj :=
      intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
        (hc.intervalIntegrable (0 : ℝ) 1) (hc.intervalIntegrable 1 y)
    rw [integral_exponential_quadratic, integral_exponential_quadratic] at hj
    have hf :=
      intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
        (hcont.intervalIntegrable (0 : ℝ) 1) (hcont.intervalIntegrable 1 y)
    have hp : 0 ≤ (a * y + b * (y ^ 2 + y + 1)) * Real.exp (-y) := by
      apply mul_nonneg _ (Real.exp_pos _).le
      nlinarith only [mul_nonneg ha hy, mul_nonneg hb (sq_nonneg y), mul_nonneg hb hy, hb]
    change (∫ u in (0 : ℝ)..y, f u) ≤ _
    rw [he] at hf
    linarith only [hleft, hj, hf, hp]

/-- Claim: exp(-1) <= 3/8. Use the first four terms of the positive exponential
series at one and invert. Role: give a short rational variation-moment bound. -/
theorem exp_neg_one_le_three_eighths : Real.exp (-1) ≤ (3 / 8 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 1) 4
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, one_pow,
    Nat.factorial] at h
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos 1)]
  linarith only [h]

/-- Input: nonnegative affine coefficients and cutoff. Claim: the variation
integral is at most 3a/4+5b/4. Insert exp(-1) <= 3/8 into the exact bound.
Role: provide constants suitable for later rational witness comparisons. -/
theorem integral_affine_abs_exponential_variation_le_rational {a b y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hy : 0 ≤ y) :
    (∫ u in (0 : ℝ)..y, (a + b * u) * |u - 1| * Real.exp (-u)) ≤ 3 / 4 * a + 5 / 4 * b := by
  have h := integral_affine_abs_exponential_variation_le ha hb hy
  have hm :=
    mul_le_mul_of_nonneg_left exp_neg_one_le_three_eighths
      (show 0 ≤ 2 * (a + 3 * b) by linarith only [ha, hb])
  linarith only [h, hm]

/-- Input: a continuous error f on [0,y], nonnegative y,a,b, and abs(f(u)) <= a+b*u.
Claim: its signed exponential variation integral has norm at most 3a/4+5b/4.
Dominate the integral norm by the proved affine variation moment.
Role: transfer pointwise arithmetic errors to principal Gamma sums. -/
theorem norm_integral_exponential_variation_le_affine {a b y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hy : 0 ≤ y) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.uIcc 0 y))
    (hbound : ∀ u ∈ Set.Icc 0 y, |f u| ≤ a + b * u) :
    |∫ u in (0 : ℝ)..y, f u * ((u - 1) * Real.exp (-u))| ≤ 3 / 4 * a + 5 / 4 * b := by
  have hQ : Continuous (fun u : ℝ ↦ (u - 1) * Real.exp (-u)) :=
    (continuous_id.sub continuous_const).mul (Real.continuous_exp.comp continuous_id.neg)
  have hg : Continuous (fun u : ℝ ↦ (a + b * u) * |u - 1| * Real.exp (-u)) :=
    ((continuous_const.add (continuous_const.mul continuous_id)).mul
          (continuous_id.sub continuous_const).abs).mul
      (Real.continuous_exp.comp continuous_id.neg)
  have hn :=
    intervalIntegral.norm_integral_le_integral_norm (f := fun u ↦ f u * ((u - 1) * Real.exp (-u)))
      (μ := MeasureTheory.volume) hy
  simp only [Real.norm_eq_abs] at hn
  have hm :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hy
      ((hf.mul hQ.continuousOn).abs.intervalIntegrable) (hg.intervalIntegrable 0 y)
      (fun u hu ↦
        show |f u * ((u - 1) * Real.exp (-u))| ≤ (a + b * u) * |u - 1| * Real.exp (-u) from by
          rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
          exact
            (mul_le_mul_of_nonneg_right (hbound u hu)
                  (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)).trans_eq
              (by ring))
  exact hn.trans (hm.trans (integral_affine_abs_exponential_variation_le_rational ha hb hy))

end PseudoPrime.Analysis
