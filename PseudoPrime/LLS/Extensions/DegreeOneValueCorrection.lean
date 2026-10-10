/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.ConductorValueExpansion

/-! Sign of the degree-one conductor-value correction. -/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- For a positive linear factor, multiplying the degree-one exponent by that factor
leaves its linear term and the positive rational quadratic term. Clear the explicitly
nonzero denominators and use a ring identity. This is used in the strict majorant bound. -/
private theorem degreeOne_exponential_identity (a K u : ℝ) (h : 0 < 1 - a * u) :
    (1 - a * u) * (u / (2 * (1 - a * u)) + K * u ^ 2 / (4 * (1 - a * u) ^ 2) + 1) =
      1 + (1 / 2 - a) * u + K * u ^ 2 / (4 * (1 - a * u)) := by
  field_simp (disch :=
    first
    | exact ne_of_gt h
    | exact pow_ne_zero _ (ne_of_gt h)
    | norm_num only)
  ring

/-- For positive `u`, `K` and `1-au`, the degree-one normalized majorant strictly
exceeds its first-order polynomial. Multiply `1+y ≤ exp y` by the positive factor;
the remaining term `K u²/(4(1-au))` is positive. This determines the sign of the
correction used by the conductor-value bounds. -/
theorem normalizedValueUpper_one_gt_linear {a K u : ℝ} (h : 0 < 1 - a * u) (hK : 0 < K)
    (hu : 0 < u) : 1 + (1 / 2 - a) * u < normalizedValueUpper 1 a K u := by
  have hp := div_pos (mul_pos hK (sq_pos_of_pos hu)) (mul_pos (by norm_num only : (0 : ℝ) < 4) h)
  have he :=
    mul_le_mul_of_nonneg_left
      (Real.add_one_le_exp (u / (2 * (1 - a * u)) + K * u ^ 2 / (4 * (1 - a * u) ^ 2))) h.le
  rw [degreeOne_exponential_identity a K u h] at he
  simpa only [normalizedValueUpper, Nat.cast_one, one_mul, pow_one] using
    lt_of_lt_of_le (lt_add_of_pos_right _ hp) he

/-- For positive `t`, multiplying the first-order polynomial at `1/t` by `t`
cancels its denominator. This converts the normalized comparison to the value correction. -/
private theorem degreeOne_linear_identity (a t : ℝ) (ht : 0 < t) :
    t * (1 + (1 / 2 - a) * (1 / t)) = t + (1 / 2 - a) := by
  field_simp (disch :=
    first
    | exact ne_of_gt ht
    | norm_num only)

/-- If `K > 0`, `t > 0` and `a < t`, the degree-one value correction is negative.
The normalized majorant exceeds its linear approximation; multiplication by positive
`t` reverses the difference defining the correction. Consequently this majorant
does not supply the error-free degree-one endpoint by absorbing a nonnegative correction. -/
theorem valueUpperCorrection_one_neg {a K t : ℝ} (hK : 0 < K) (ht : 0 < t) (ha : a < t) :
    valueUpperCorrection 1 a K t < 0 := by
  have hn : 0 < 1 - a * (1 / t) := by
    rw [mul_one_div, sub_pos, div_lt_one ht]
    exact ha
  have h :=
    mul_lt_mul_of_pos_left (normalizedValueUpper_one_gt_linear hn hK (one_div_pos.mpr ht)) ht
  rw [degreeOne_linear_identity a t ht] at h
  dsimp only [valueUpperCorrection, Nat.cast_one, one_mul]
  linarith only [h]

/-- For fixed shift and positive coefficient, the degree-one correction is negative
eventually on the conductor filter. The double logarithm tends to infinity, so the
pointwise sign theorem applies. This connects the algebraic obstruction to uniform families. -/
theorem eventually_valueUpperCorrection_one_neg (a : ℝ) {K : ℝ} (hK : 0 < K) :
    ∀ᶠ f : FixedDegreeFamily 1 in conductorFilter 1,
      valueUpperCorrection 1 a K (Real.log (Real.log f.val.analyticConductor)) < 0 := by
  have ht :
    Filter.Tendsto (fun f : FixedDegreeFamily 1 ↦ Real.log (Real.log f.val.analyticConductor))
      (conductorFilter 1) Filter.atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp Filter.tendsto_comap)
  filter_upwards [ht.eventually (Filter.eventually_gt_atTop (0 : ℝ)),
    ht.eventually (Filter.eventually_gt_atTop a)] with f hf0 hfa
  exact valueUpperCorrection_one_neg hK hf0 hfa

/-- Nonnegative second-order arithmetic constants make the coefficient
`A+B+34/7+1` positive. The correction in the existing degree-one Mangoldt majorant
is therefore eventually negative. This rules out absorbing that correction to obtain
the exact endpoint; it does not assert that the endpoint itself is false. -/
theorem eventually_degreeOne_mangoldtCorrection_neg {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∀ᶠ f : FixedDegreeFamily 1 in conductorFilter 1,
      valueUpperCorrection 1 (Real.log 2) (A + B + 34 / 7 + 1)
          (Real.log (Real.log f.val.analyticConductor)) <
        0 := by
  apply eventually_valueUpperCorrection_one_neg
  linarith only [hA, hB]

end PseudoPrime.LLS.Extensions.GeneralLFunction
