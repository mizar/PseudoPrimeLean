/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.TruncatedArithmeticBounds

/-! Common conductor cutoffs and uniform fixed-degree general L-value bounds. -/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- The general L-value cutoff `(log C)^2 / (4 d^2)` for degree `d` and conductor `C`.
Division is total; positive degree is required by the comparison lemmas.
It is the common conductor-dependent cutoff for fixed-degree value estimates. -/
noncomputable def valueCutoff (d : ℕ) (C : ℝ) : ℝ :=
  (Real.log C) ^ 2 / (4 * (d : ℝ) ^ 2)

/-- For positive degree, the value cutoff is the square of `log C / (2d)`.
Clear the nonzero degree denominator. This evaluates its square root and logarithm. -/
theorem valueCutoff_eq_sq {d : ℕ} (hd : 0 < d) (C : ℝ) :
    valueCutoff d C = (Real.log C / (2 * (d : ℝ))) ^ 2 := by
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hd)
  unfold valueCutoff
  field_simp (disch := simp only [hd0, ne_eq, not_false_eq_true])
  ring

/-- For positive degree and conductor at least one, the cutoff square root is `log C / (2d)`.
The quotient is nonnegative, so its square root has no absolute-value ambiguity.
This evaluates the conductor term and the square-loss scale. -/
theorem sqrt_valueCutoff {d : ℕ} (hd : 0 < d) {C : ℝ} (hC : 1 ≤ C) :
    Real.sqrt (valueCutoff d C) = Real.log C / (2 * (d : ℝ)) := by
  rw [valueCutoff_eq_sq hd, Real.sqrt_sq_eq_abs]
  exact
    abs_of_nonneg
      (div_nonneg (Real.log_nonneg hC)
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) (Nat.cast_nonneg d)))

/-- For positive degree and conductor above one, the cutoff logarithm is twice
`log log C - log (2d)`. Apply the square and quotient logarithm identities with positive
arguments. This identifies the first-order correction in the final value estimates. -/
theorem log_valueCutoff {d : ℕ} (hd : 0 < d) {C : ℝ} (hC : 1 < C) :
    Real.log (valueCutoff d C) = 2 * (Real.log (Real.log C) - Real.log (2 * (d : ℝ))) := by
  rw [valueCutoff_eq_sq hd, Real.log_pow,
    Real.log_div (Real.log_pos hC).ne'
      (mul_pos (by norm_num only : (0 : ℝ) < 2) (Nat.cast_pos.mpr hd)).ne']
  norm_num only [Nat.cast_ofNat]

/-- For positive degree and `log C >= 20d`, the common cutoff is at least one hundred.
The root quotient is at least ten; square this inequality. This ensures the finite
prime-power comparisons apply beyond a threshold depending only on degree. -/
theorem hundred_le_valueCutoff {d : ℕ} (hd : 0 < d) {C : ℝ} (hlog : 20 * (d : ℝ) ≤ Real.log C) :
    100 ≤ valueCutoff d C := by
  have hd0 : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hdiv : 10 ≤ Real.log C / (2 * (d : ℝ)) := by
    apply (le_div_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 2) hd0)).mpr
    linarith only [hlog]
  rw [valueCutoff_eq_sq hd]
  nlinarith only [hdiv]

/-- For positive degree and conductor above one, the leading conductor term at the
common cutoff equals `2d / log cutoff`. Substitute its square root and cancel `log C`.
This transfers the exact cutoff choice to the exponential value bounds. -/
theorem conductor_term_at_valueCutoff {d : ℕ} (hd : 0 < d) {C : ℝ} (hC : 1 < C) :
    |Real.log C| / (Real.sqrt (valueCutoff d C) * Real.log (valueCutoff d C)) =
      2 * (d : ℝ) / Real.log (valueCutoff d C) := by
  have hl : 0 < Real.log C := Real.log_pos hC
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hd)
  rw [abs_of_pos hl, sqrt_valueCutoff hd hC.le, div_mul_eq_div_mul_one_div]
  field_simp (disch := simp only [hl.ne', hd0, ne_eq, not_false_eq_true])

/-- For positive fixed degree, the value cutoff is eventually at least one hundred on
the conductor filter. The log conductor tends to infinity through the comap filter;
apply the explicit degree-only threshold. This supplies a uniform comparison domain. -/
theorem eventually_valueCutoff_ge_hundred {d : ℕ} (hd : 0 < d) :
    ∀ᶠ f in conductorFilter d, 100 ≤ valueCutoff d f.val.analyticConductor := by
  have ht :
    Filter.Tendsto (fun f : FixedDegreeFamily d ↦ Real.log f.val.analyticConductor)
      (conductorFilter d) Filter.atTop :=
    Real.tendsto_log_atTop.comp Filter.tendsto_comap
  filter_upwards [ht.eventually (Filter.eventually_ge_atTop (20 * (d : ℝ)))] with f hf
  exact hundred_le_valueCutoff hd hf

/-- For positive fixed degree, simultaneous norm and reciprocal bounds hold eventually
on the conductor filter at the common cutoff, retaining the truncated arithmetic majorant
and error. Apply admissibility and RH from the family, use the uniform cutoff threshold,
and evaluate the leading conductor term. This connects pointwise bounds to the generalL family. -/
theorem eventually_norm_L_one_and_reciprocal_le_valueCutoff {d : ℕ} (hd : 0 < d) :
    ∀ᶠ f in conductorFilter d,
      ‖f.val.L 1‖ ≤
          Real.exp
            ((d : ℝ) *
                AnalyticNumberTheory.Arithmetic.truncatedMangoldtMajorant
                  (valueCutoff d f.val.analyticConductor) +
              2 * (d : ℝ) / Real.log (valueCutoff d f.val.analyticConductor) +
              f.val.truncatedConductorErrorBound (valueCutoff d f.val.analyticConductor)) ∧
        1 / ‖f.val.L 1‖ ≤
          (6 / Real.pi ^ 2) ^ d *
            Real.exp
              ((d : ℝ) *
                  (AnalyticNumberTheory.Arithmetic.truncatedMangoldtMajorant
                      (valueCutoff d f.val.analyticConductor) +
                    3 / (2 * Real.sqrt (valueCutoff d f.val.analyticConductor))) +
                2 * (d : ℝ) / Real.log (valueCutoff d f.val.analyticConductor) +
                f.val.truncatedConductorErrorBound (valueCutoff d f.val.analyticConductor)) := by
  have ht :
    Filter.Tendsto (fun f : FixedDegreeFamily d ↦ f.val.analyticConductor) (conductorFilter d)
      Filter.atTop :=
    Filter.tendsto_comap
  filter_upwards [eventually_valueCutoff_ge_hundred hd,
    ht.eventually (Filter.eventually_gt_atTop (1 : ℝ))] with f hx hC
  have h1 :=
    (norm_L_one_and_reciprocal_le_exp_truncated_majorants f.val f.property.2.1 f.property.2.2
        (le_trans (by norm_num only : (2 : ℝ) ≤ 100) hx)).1
  have h2 := reciprocal_norm_L_one_le_square_corrected f.val f.property.2.1 f.property.2.2 hx
  rw [f.property.1, conductor_term_at_valueCutoff hd hC] at h1 h2
  exact ⟨h1, h2⟩

/-- For positive fixed degree, the common cutoff tends to infinity on the conductor
filter. The log conductor tends to infinity, as does its quotient by positive `2d` and
its square. This allows real-cutoff asymptotic estimates to be composed with the family. -/
theorem tendsto_valueCutoff_atTop {d : ℕ} (hd : 0 < d) :
    Filter.Tendsto (fun f : FixedDegreeFamily d ↦ valueCutoff d f.val.analyticConductor)
      (conductorFilter d) Filter.atTop := by
  have ht :
    Filter.Tendsto (fun f : FixedDegreeFamily d ↦ Real.log f.val.analyticConductor)
      (conductorFilter d) Filter.atTop :=
    Real.tendsto_log_atTop.comp Filter.tendsto_comap
  have hdiv := ht.atTop_div_const (mul_pos (by norm_num only : (0 : ℝ) < 2) (Nat.cast_pos.mpr hd))
  have hs := (Filter.tendsto_pow_atTop (by norm_num only : (2 : ℕ) ≠ 0)).comp hdiv
  change
    Filter.Tendsto
      (fun f : FixedDegreeFamily d ↦ (Real.log f.val.analyticConductor / (2 * (d : ℝ))) ^ 2)
      (conductorFilter d) Filter.atTop at hs
  simpa only [valueCutoff_eq_sq hd] using hs

/-- For positive fixed degree, the square-correction loss majorant at the common cutoff
tends to zero uniformly on the conductor filter. Compose the cutoff limit with the square
root and reciprocal limits, then multiply by `3/2`. This removes this error from the final
little-o obstruction. -/
theorem tendsto_squareLoss_at_valueCutoff {d : ℕ} (hd : 0 < d) :
    Filter.Tendsto
      (fun f : FixedDegreeFamily d ↦ 3 / (2 * Real.sqrt (valueCutoff d f.val.analyticConductor)))
      (conductorFilter d) (nhds 0) := by
  have hs := (Real.tendsto_sqrt_atTop.comp (tendsto_valueCutoff_atTop hd)).inv_tendsto_atTop
  simpa only [div_mul_eq_div_mul_one_div, one_div, mul_zero, Pi.inv_apply,
    Function.comp_apply] using hs.const_mul (3 / 2 : ℝ)

/-- For positive fixed degree, the logarithm of the common cutoff tends to infinity
on the conductor filter. Compose the cutoff limit with the logarithm limit.
This supplies the reciprocal logarithm scale for conductor corrections. -/
theorem tendsto_log_valueCutoff_atTop {d : ℕ} (hd : 0 < d) :
    Filter.Tendsto (fun f : FixedDegreeFamily d ↦ Real.log (valueCutoff d f.val.analyticConductor))
      (conductorFilter d) Filter.atTop := by
  exact Real.tendsto_log_atTop.comp (tendsto_valueCutoff_atTop hd)

/-- For positive fixed degree, the evaluated leading conductor term tends to zero
uniformly on the conductor filter. The cutoff logarithm tends to infinity, so its inverse
and constant multiple tend to zero. This removes the leading correction at zeroth order. -/
theorem tendsto_conductor_term_at_valueCutoff {d : ℕ} (hd : 0 < d) :
    Filter.Tendsto
      (fun f : FixedDegreeFamily d ↦ 2 * (d : ℝ) / Real.log (valueCutoff d f.val.analyticConductor))
      (conductorFilter d) (nhds 0) := by
  have hi := (tendsto_log_valueCutoff_atTop hd).inv_tendsto_atTop
  simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply] using hi.const_mul (2 * (d : ℝ))

end PseudoPrime.LLS.Extensions.GeneralLFunction
