/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.ConductorCutoffAsymptotics

/-! Second-order conductor-cutoff errors and quantitative general L-value bounds. -/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- For positive fixed degree, the uniform truncation error times the square cutoff logarithm
converges to `34d/7` on the conductor filter. Expand the scaled error and take the logarithmic
power limits; only the normalized zero-mass majorant survives.
This supplies a second-order error bound while preserving the leading conductor correction. -/
theorem tendsto_truncatedConductorErrorBound_mul_log_sq {d : ℕ} (hd : 0 < d) :
    Filter.Tendsto
      (fun f : FixedDegreeFamily d ↦
        f.val.truncatedConductorErrorBound (valueCutoff d f.val.analyticConductor) *
          (Real.log (valueCutoff d f.val.analyticConductor)) ^ 2)
      (conductorFilter d) (nhds ((34 / 7 : ℝ) * (d : ℝ))) := by
  have hi := (tendsto_valueCutoff_atTop hd).inv_tendsto_atTop
  have hr := (Real.tendsto_sqrt_atTop.comp (tendsto_valueCutoff_atTop hd)).inv_tendsto_atTop
  have hls := (Analysis.tendsto_log_pow_div_sqrt 1).comp (tendsto_valueCutoff_atTop hd)
  have hlx := (Analysis.tendsto_log_pow_div_self 1).comp (tendsto_valueCutoff_atTop hd)
  have hl2x := (Analysis.tendsto_log_pow_div_self 2).comp (tendsto_valueCutoff_atTop hd)
  have hp :=
    AnalyticNumberTheory.Arithmetic.tendsto_reciprocalMangoldtSum_mul_log_div_sqrt.comp
      (tendsto_valueCutoff_atTop hd)
  have hu := (hr.const_mul ((d : ℝ) * zeroMassDegreeBound)).const_add ((34 / 7 : ℝ) * (d : ℝ))
  let z :=
    (d : ℝ) *
        (2 * AnalyticNumberTheory.Gamma.digammaLogErrorBound + 3 * |zeroMassDegreeBound| +
          2 * (1 + AnalyticNumberTheory.Gamma.reciprocalGammaTailBound) +
          2 * (Real.log 4 + 4)) +
      (116 / 7 : ℝ) * (d : ℝ)
  have hsum :=
    (hu.mul (hls.const_mul (1 / 2 : ℝ))).add hu |>.add (hi.const_mul (2 * (d : ℝ))) |>.add
                  (hls.const_mul (d : ℝ)) |>.add
                (hlx.const_mul
                  ((d : ℝ) * AnalyticNumberTheory.Gamma.digammaLogErrorBound / 2)) |>.add
              (hu.mul hls) |>.add
            (hl2x.const_mul (d : ℝ)) |>.add
          (hlx.const_mul ((d : ℝ) * AnalyticNumberTheory.Gamma.reciprocalGammaTailBound)) |>.add
        (hp.const_mul (2 * (d : ℝ))) |>.add
      (hls.const_mul z)
  simp only [mul_zero, add_zero, zero_add] at hsum
  apply hsum.congr'
  have hC :
    Filter.Tendsto (fun f : FixedDegreeFamily d ↦ f.val.analyticConductor) (conductorFilter d)
      Filter.atTop :=
    Filter.tendsto_comap
  filter_upwards [hC.eventually (Filter.eventually_gt_atTop (1 : ℝ)),
    (tendsto_valueCutoff_atTop hd).eventually (Filter.eventually_gt_atTop (1 : ℝ))] with f hCf hxf
  rw [truncatedConductorErrorBound_eq_scaled f.val hd f.property.1 hCf hxf]
  dsimp only [z]
  simp only [Pi.inv_apply, Function.comp_apply, pow_one]
  have hl : Real.log (valueCutoff d f.val.analyticConductor) ≠ 0 := (Real.log_pos hxf).ne'
  field_simp (disch := simp only [hl, ne_eq, not_false_eq_true])

/-- For positive fixed degree, adding the square-loss contribution preserves the scaled limit
`34d/7`. Its product with the square cutoff logarithm tends to zero.
This gives a common second-order error for the L-value and reciprocal estimates. -/
theorem tendsto_valueError_mul_log_sq {d : ℕ} (hd : 0 < d) :
    Filter.Tendsto
      (fun f : FixedDegreeFamily d ↦
        (f.val.truncatedConductorErrorBound (valueCutoff d f.val.analyticConductor) +
            (d : ℝ) * (3 / (2 * Real.sqrt (valueCutoff d f.val.analyticConductor)))) *
          (Real.log (valueCutoff d f.val.analyticConductor)) ^ 2)
      (conductorFilter d) (nhds ((34 / 7 : ℝ) * (d : ℝ))) := by
  have hs :=
    ((Analysis.tendsto_log_pow_div_sqrt 2).comp (tendsto_valueCutoff_atTop hd)).const_mul
      ((d : ℝ) * (3 / 2))
  have ht := (tendsto_truncatedConductorErrorBound_mul_log_sq hd).add hs
  simp only [mul_zero, add_zero] at ht
  convert ht using 1
  funext f
  simp only [Function.comp_apply]
  ring

/-- For positive fixed degree and sufficiently large conductor, bound both L-values using
exponent `d Q(x) + 2d/log x + (34d/7 + 1)/log^2 x` at the common cutoff.
The reciprocal retains the factor `(6/pi^2)^d`. Apply the scaled error limit and absorb
square loss into the common error. This preserves the first-order term for the final expansion. -/
theorem eventually_norm_L_one_and_reciprocal_le_secondOrder_error {d : ℕ} (hd : 0 < d) :
    ∀ᶠ f : FixedDegreeFamily d in conductorFilter d,
      let x := valueCutoff d f.val.analyticConductor
      let b := ((34 / 7 : ℝ) * (d : ℝ) + 1) / (Real.log x) ^ 2
      ‖f.val.L 1‖ ≤
          Real.exp
            ((d : ℝ) * AnalyticNumberTheory.Arithmetic.truncatedMangoldtMajorant x +
              2 * (d : ℝ) / Real.log x +
              b) ∧
        1 / ‖f.val.L 1‖ ≤
          (6 / Real.pi ^ 2) ^ d *
            Real.exp
              ((d : ℝ) * AnalyticNumberTheory.Arithmetic.truncatedMangoldtMajorant x +
                2 * (d : ℝ) / Real.log x +
                b) := by
  have hlim :=
    (tendsto_valueError_mul_log_sq hd).eventually
      (gt_mem_nhds (show (34 / 7 : ℝ) * (d : ℝ) < (34 / 7 : ℝ) * (d : ℝ) + 1 by linarith only))
  filter_upwards [eventually_norm_L_one_and_reciprocal_le_valueCutoff hd, hlim,
    (tendsto_valueCutoff_atTop hd).eventually (Filter.eventually_gt_atTop (1 : ℝ))] with f hb he hx
  dsimp only at hb ⊢
  have hs : 0 ≤ (d : ℝ) * (3 / (2 * Real.sqrt (valueCutoff d f.val.analyticConductor))) :=
    mul_nonneg (Nat.cast_nonneg d)
      (div_nonneg (by norm_num only : (0 : ℝ) ≤ 3)
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg _)))
  have he' := (le_div_iff₀ (sq_pos_of_pos (Real.log_pos hx))).mpr he.le
  refine
    ⟨hb.1.trans (Real.exp_le_exp.mpr ?_),
      hb.2.trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
          (pow_nonneg (div_nonneg (by norm_num only : (0 : ℝ) ≤ 6) (sq_nonneg Real.pi)) d))⟩
  · linarith only [he', hs]
  · linarith only [he']

/-- For positive fixed degree, eventual second-order Mangoldt and psi bounds imply simultaneous
L-value bounds with exponent `d(log log x + gamma + 1/log x) + K/log^2 x`, where
`K = d(A+B) + 34d/7 + 1`. The reciprocal retains the zeta-at-two factor.
Compose the arithmetic inputs with the conductor cutoff and insert the uniform error bound.
The prime-sum estimates are explicit hypotheses; this does not prove the public general-L claim. -/
theorem eventually_norm_L_one_and_reciprocal_le_of_secondOrder_mangoldt_errors {d : ℕ} (hd : 0 < d)
    {A B : ℝ} (hB : 0 ≤ B)
    (hH :
      ∀ᶠ x : ℝ in Filter.atTop,
        |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n)) -
              (Real.log (Real.log x) + Real.eulerMascheroniConstant)| ≤
          A / (Real.log x) ^ 2)
    (hψ : ∀ᶠ x : ℝ in Filter.atTop, |Chebyshev.psi x - x| ≤ B * x / (Real.log x) ^ 2) :
    ∀ᶠ f : FixedDegreeFamily d in conductorFilter d,
      let x := valueCutoff d f.val.analyticConductor
      let m :=
        (d : ℝ) * (Real.log (Real.log x) + Real.eulerMascheroniConstant + 1 / Real.log x) +
          ((d : ℝ) * (A + B) + (34 / 7 : ℝ) * (d : ℝ) + 1) / (Real.log x) ^ 2
      ‖f.val.L 1‖ ≤ Real.exp m ∧ 1 / ‖f.val.L 1‖ ≤ (6 / Real.pi ^ 2) ^ d * Real.exp m := by
  filter_upwards [eventually_norm_L_one_and_reciprocal_le_secondOrder_error hd,
    (tendsto_valueCutoff_atTop hd).eventually hH, (tendsto_valueCutoff_atTop hd).eventually hψ,
    (tendsto_valueCutoff_atTop hd).eventually (Filter.eventually_gt_atTop (1 : ℝ)),
    (tendsto_log_valueCutoff_atTop hd).eventually (Filter.eventually_ge_atTop (1 : ℝ))] with f hb
    hHf hψf hx hl
  dsimp only at hb ⊢
  have hQ :=
    mul_le_mul_of_nonneg_left
      (AnalyticNumberTheory.Arithmetic.truncatedMangoldtMajorant_le_of_secondOrder_mangoldt_errors
        hx hl hB hHf hψf)
      (Nat.cast_nonneg d)
  have hex :
    (d : ℝ) *
          AnalyticNumberTheory.Arithmetic.truncatedMangoldtMajorant
            (valueCutoff d f.val.analyticConductor) +
        2 * (d : ℝ) / Real.log (valueCutoff d f.val.analyticConductor) +
        ((34 / 7 : ℝ) * (d : ℝ) + 1) / (Real.log (valueCutoff d f.val.analyticConductor)) ^ 2 ≤
      (d : ℝ) *
          (Real.log (Real.log (valueCutoff d f.val.analyticConductor)) +
            Real.eulerMascheroniConstant +
            1 / Real.log (valueCutoff d f.val.analyticConductor)) +
        ((d : ℝ) * (A + B) + (34 / 7 : ℝ) * (d : ℝ) + 1) /
          (Real.log (valueCutoff d f.val.analyticConductor)) ^ 2 := by
    simp only [add_div, mul_add, mul_sub, mul_one_div, mul_div_assoc] at hQ ⊢
    linarith only [hQ]
  exact
    ⟨hb.1.trans (Real.exp_le_exp.mpr hex),
      hb.2.trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hex)
          (pow_nonneg (div_nonneg (by norm_num only : (0 : ℝ) ≤ 6) (sq_nonneg Real.pi)) d))⟩

end PseudoPrime.LLS.Extensions.GeneralLFunction
