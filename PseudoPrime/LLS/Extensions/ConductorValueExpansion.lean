/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.ConductorCutoffErrorRate

/-! Polynomial conductor-value bounds and their vanishing first-order corrections. -/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- The normalized exponential value majorant after setting `u = 1/log log C`.
For degree `d`, shift `a` and second-order coefficient `K`, it is
`(1-au)^d exp(d u/(2(1-au)) + K u^2/(4(1-au)^2))`.
It separates the conductor growth from the first-order correction; divisions are total. -/
noncomputable def normalizedValueUpper (d : ℕ) (a K u : ℝ) : ℝ :=
  (1 - a * u) ^ d * Real.exp ((d : ℝ) * u / (2 * (1 - a * u)) + K * u ^ 2 / (4 * (1 - a * u) ^ 2))

/-- The normalized value majorant has derivative `d(1/2-a)` at zero.
Differentiate the polynomial, rational terms and exponential; all denominators are nonzero
at zero. This identifies the coefficient of the final first-order value correction. -/
theorem hasDerivAt_normalizedValueUpper (d : ℕ) (a K : ℝ) :
    HasDerivAt (normalizedValueUpper d a K) ((d : ℝ) * (1 / 2 - a)) 0 := by
  have hu := hasDerivAt_id (0 : ℝ)
  have hn := (hu.const_mul a).const_sub 1
  have hl :=
    (hu.const_mul (d : ℝ)).div (hn.const_mul 2)
      (by norm_num only [id_eq, mul_zero, sub_zero, mul_one, ne_eq, OfNat.ofNat_ne_zero])
  have hr :=
    ((hu.pow 2).const_mul K).div ((hn.pow 2).const_mul 4)
      (by
        norm_num only [Pi.pow_apply, id_eq, mul_zero, sub_zero, one_pow, mul_one, ne_eq,
          OfNat.ofNat_ne_zero])
  have h := (hn.pow d).mul (hl.add hr).exp
  change HasDerivAt (normalizedValueUpper d a K) _ 0 at h
  simp only [Pi.pow_apply, Pi.div_apply, Pi.add_apply, id_eq, mul_zero, sub_zero, one_pow, mul_one,
    zero_mul, zero_div] at h
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_pow, OfNat.ofNat_ne_zero] at h
  simp only [mul_zero, zero_div, zero_add, Real.exp_zero, mul_one, one_mul] at h
  convert h using 1
  ring

/-- The error in the first-order polynomial expansion of the normalized value majorant.
For `t = log log C`, subtract `d(a-1/2)` from `t(1-F(1/t))`.
The same real error is used in both norm and reciprocal bounds and tends to zero. -/
noncomputable def valueUpperCorrection (d : ℕ) (a K t : ℝ) : ℝ :=
  t * (1 - normalizedValueUpper d a K (1 / t)) - (d : ℝ) * (a - 1 / 2)

/-- The normalized value majorant equals one at zero for every degree, shift and coefficient.
Evaluate the polynomial and exponential. This is the constant term of its Taylor expansion. -/
theorem normalizedValueUpper_zero (d : ℕ) (a K : ℝ) : normalizedValueUpper d a K 0 = 1 := by
  simp only [normalizedValueUpper, mul_zero, sub_zero, one_pow,
    zero_pow (by norm_num only : (2 : ℕ) ≠ 0), zero_div, add_zero, Real.exp_zero, mul_one]

/-- For fixed degree, shift and coefficient, the value correction tends to zero as `t` grows.
Compose the derivative remainder at zero with `1/t`, then rearrange the quotient.
This supplies the little-o error in the final polynomial value bounds. -/
theorem tendsto_valueUpperCorrection (d : ℕ) (a K : ℝ) :
    Filter.Tendsto (valueUpperCorrection d a K) Filter.atTop (nhds 0) := by
  have h := (hasDerivAt_normalizedValueUpper d a K).isLittleO.tendsto_div_nhds_zero
  simp only [normalizedValueUpper_zero, sub_zero, smul_eq_mul] at h
  have ht := h.comp tendsto_inv_atTop_zero
  have hn := ht.neg
  simp only [neg_zero] at hn
  apply hn.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht0
  simp only [Function.comp_apply, valueUpperCorrection]
  rw [one_div]
  field_simp (disch := simp only [ht0.ne', ne_eq, not_false_eq_true])
  ring

/-- For positive degree, express `t^d F(1/t)` exactly as
`t^d - (d(a-1/2) + error(t)) t^(d-1)`, including at zero.
Unfold the correction and split the degree power. This converts the exponential majorant
to the polynomial form of the general L-value claim. -/
theorem normalizedValueUpper_eq_polynomial (d : ℕ) (hd : 0 < d) (a K : ℝ) {t : ℝ} :
    t ^ d * normalizedValueUpper d a K (1 / t) =
      t ^ d - ((d : ℝ) * (a - 1 / 2) + valueUpperCorrection d a K t) * t ^ (d - 1) := by
  rw [valueUpperCorrection]
  have hp : t ^ d = t * t ^ (d - 1) := by rw [← pow_succ', Nat.sub_add_cancel hd]
  rw [hp]
  ring

/-- For positive `t` above the shift `a`, factor the second-order exponential main term
as `(2 exp gamma)^d t^d F(1/t)`. Evaluate the logarithmic exponential and clear the
positive denominators. This preserves the exact first-order coefficient when exponentiating. -/
theorem exp_valueMain_eq_normalized (d : ℕ) (a K γ : ℝ) {t : ℝ} (ht : 0 < t) (hta : a < t) :
    Real.exp ((d : ℝ) * (Real.log (2 * (t - a)) + γ + 1 / (2 * (t - a))) + K / (4 * (t - a) ^ 2)) =
      (2 * Real.exp γ) ^ d * t ^ d * normalizedValueUpper d a K (1 / t) := by
  have hs : 1 - a * (1 / t) = (t - a) / t := by
    field_simp (disch := simp only [ht.ne', ne_eq, not_false_eq_true])
  have he :
    (d : ℝ) * (Real.log (2 * (t - a)) + γ + 1 / (2 * (t - a))) + K / (4 * (t - a) ^ 2) =
      (d : ℝ) * Real.log (2 * (t - a)) + (d : ℝ) * γ +
        ((d : ℝ) * (1 / t) / (2 * (1 - a * (1 / t))) +
          K * (1 / t) ^ 2 / (4 * (1 - a * (1 / t)) ^ 2)) := by
    rw [hs]
    field_simp (disch := simp only [ht.ne', (sub_pos.mpr hta).ne', ne_eq, not_false_eq_true])
    ring
  rw [he, Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_log (mul_pos (by norm_num only : (0 : ℝ) < 2) (sub_pos.mpr hta))]
  unfold normalizedValueUpper
  rw [hs]
  have hp : t ^ d * ((t - a) / t) ^ d = (t - a) ^ d := by rw [← mul_pow, mul_div_cancel₀ _ ht.ne']
  rw [← mul_assoc, mul_assoc ((2 * Real.exp γ) ^ d), hp, mul_pow, mul_pow]
  ring

/-- For positive fixed degree, eventual second-order Mangoldt and psi bounds imply the
polynomial norm and reciprocal bounds with correction `d log d + d(log 2-1/2) + e`.
Use the conductor-cutoff logarithm, factor the exponential and insert the normalized
polynomial identity. The reciprocal prefactor is `(12 exp gamma/pi^2)^d`.
The arithmetic estimates remain explicit inputs; no new public theorem assumption is added. -/
theorem eventually_value_bounds_with_correction_of_mangoldt_errors {d : ℕ} (hd : 0 < d) {A B : ℝ}
    (hB : 0 ≤ B)
    (hH :
      ∀ᶠ x : ℝ in Filter.atTop,
        |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n)) -
              (Real.log (Real.log x) + Real.eulerMascheroniConstant)| ≤
          A / (Real.log x) ^ 2)
    (hψ : ∀ᶠ x : ℝ in Filter.atTop, |Chebyshev.psi x - x| ≤ B * x / (Real.log x) ^ 2) :
    ∀ᶠ f : FixedDegreeFamily d in conductorFilter d,
      let t := Real.log (Real.log f.val.analyticConductor)
      let e :=
        valueUpperCorrection d (Real.log (2 * (d : ℝ)))
          ((d : ℝ) * (A + B) + (34 / 7 : ℝ) * (d : ℝ) + 1) t
      ‖f.val.L 1‖ ≤
          (2 * Real.exp Real.eulerMascheroniConstant) ^ d *
            (t ^ d - ((d : ℝ) * Real.log d + (d : ℝ) * (Real.log 2 - 1 / 2) + e) * t ^ (d - 1)) ∧
        1 / ‖f.val.L 1‖ ≤
          (12 * Real.exp Real.eulerMascheroniConstant / Real.pi ^ 2) ^ d *
            (t ^ d -
              ((d : ℝ) * Real.log d + (d : ℝ) * (Real.log 2 - 1 / 2) + e) * t ^ (d - 1)) := by
  have ht :
    Filter.Tendsto (fun f : FixedDegreeFamily d ↦ Real.log (Real.log f.val.analyticConductor))
      (conductorFilter d) Filter.atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp Filter.tendsto_comap)
  have hC :
    Filter.Tendsto (fun f : FixedDegreeFamily d ↦ f.val.analyticConductor) (conductorFilter d)
      Filter.atTop :=
    Filter.tendsto_comap
  filter_upwards [eventually_norm_L_one_and_reciprocal_le_of_secondOrder_mangoldt_errors hd hB hH
      hψ,
    ht.eventually (Filter.eventually_gt_atTop (0 : ℝ)),
    ht.eventually (Filter.eventually_gt_atTop (Real.log (2 * (d : ℝ)))),
    hC.eventually (Filter.eventually_gt_atTop (1 : ℝ))] with f hb ht0 hta hCf
  dsimp only at hb ⊢
  rw [log_valueCutoff hd hCf] at hb
  have hv :=
    exp_valueMain_eq_normalized d (Real.log (2 * (d : ℝ)))
      ((d : ℝ) * (A + B) + (34 / 7 : ℝ) * (d : ℝ) + 1) Real.eulerMascheroniConstant ht0 hta
  rw [mul_assoc ((2 * Real.exp Real.eulerMascheroniConstant) ^ d),
    normalizedValueUpper_eq_polynomial d hd] at hv
  have hc :
    (d : ℝ) * (Real.log (2 * (d : ℝ)) - 1 / 2) =
      (d : ℝ) * Real.log d + (d : ℝ) * (Real.log 2 - 1 / 2) := by
    rw [Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) (Nat.cast_pos.mpr hd).ne']
    ring
  rw [hc] at hv
  have hden :
    (2 * (Real.log (Real.log f.val.analyticConductor) - Real.log (2 * (d : ℝ)))) ^ 2 =
      4 * (Real.log (Real.log f.val.analyticConductor) - Real.log (2 * (d : ℝ))) ^ 2 := by
    ring
  rw [hden, hv] at hb
  refine ⟨hb.1, ?_⟩
  convert hb.2 using 1
  rw [← mul_assoc, ← mul_pow]
  congr 2
  ring

/-- For fixed degree, shift and coefficient, the correction tends to zero uniformly
on the conductor filter. Compose its real-variable limit with `log log C` tending to infinity.
This establishes the family-wide vanishing error required by the general L-value claim. -/
theorem tendsto_valueUpperCorrection_on_conductorFilter (d : ℕ) (a K : ℝ) :
    Filter.Tendsto
      (fun f : FixedDegreeFamily d ↦
        valueUpperCorrection d a K (Real.log (Real.log f.val.analyticConductor)))
      (conductorFilter d) (nhds 0) := by
  exact
    (tendsto_valueUpperCorrection d a K).comp
      (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp Filter.tendsto_comap))

/-- The normalized value majorant is real analytic at zero for every degree, shift and coefficient.
Its rational denominators are nonzero there; combine polynomial, quotient and exponential
analyticity. This justifies a second-order remainder bound. -/
theorem analyticAt_normalizedValueUpper (d : ℕ) (a K : ℝ) :
    AnalyticAt ℝ (normalizedValueUpper d a K) 0 := by
  have hu : AnalyticAt ℝ (fun u : ℝ ↦ u) 0 := analyticAt_id
  have hn := (analyticAt_const (v := (1 : ℝ))).sub ((analyticAt_const (v := a)).mul hu)
  have hl :=
    ((analyticAt_const (v := (d : ℝ))).mul hu).div ((analyticAt_const (v := (2 : ℝ))).mul hn)
      (by
        norm_num only [Pi.mul_apply, Pi.sub_apply, mul_zero, sub_zero, mul_one, ne_eq,
          OfNat.ofNat_ne_zero])
  have hr :=
    ((analyticAt_const (v := K)).mul (hu.pow 2)).div
      ((analyticAt_const (v := (4 : ℝ))).mul (hn.pow 2))
      (by
        norm_num only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, mul_zero, sub_zero, one_pow,
          mul_one, ne_eq, OfNat.ofNat_ne_zero])
  exact (hn.pow d).mul (hl.add hr).rexp

/-- The normalized majorant minus its constant and linear terms is `O(u^2)` near zero.
Use its analytic power series and the exact derivative at zero.
This supplies the rate for the first-order correction after substituting `u = 1/t`. -/
theorem isBigO_normalizedValueUpper_remainder (d : ℕ) (a K : ℝ) :
    Asymptotics.IsBigO (nhds (0 : ℝ))
      (fun u : ℝ ↦ normalizedValueUpper d a K u - 1 - u * ((d : ℝ) * (1 / 2 - a)))
      (fun u : ℝ ↦ u ^ 2) := by
  have h := (analyticAt_normalizedValueUpper d a K).hasFPowerSeriesAt.isBigO_sub_partialSum_pow 2
  simpa only [zero_add, FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
    Finset.sum_range_zero, FormalMultilinearSeries.ofScalars_apply_eq, iteratedDeriv_zero,
    iteratedDeriv_one, (hasDerivAt_normalizedValueUpper d a K).deriv, normalizedValueUpper_zero,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one, pow_zero, pow_one, smul_eq_mul,
    mul_one, zero_add, Real.norm_eq_abs, sq_abs, sub_add_eq_sub_sub, mul_comm] using h

/-- For fixed degree, shift and coefficient, the correction is `O(1/t)` at infinity.
Compose the second-order analytic remainder with `1/t` and multiply its norm bound by `t`.
This supplies the fixed-degree quantitative rate of the final polynomial error. -/
theorem isBigO_valueUpperCorrection (d : ℕ) (a K : ℝ) :
    Asymptotics.IsBigO Filter.atTop (valueUpperCorrection d a K) (fun t : ℝ ↦ 1 / t) := by
  have h := (isBigO_normalizedValueUpper_remainder d a K).comp_tendsto tendsto_inv_atTop_zero
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp h
  apply Asymptotics.IsBigO.of_bound c
  filter_upwards [hc, Filter.eventually_gt_atTop (0 : ℝ)] with t hct ht
  simp only [Function.comp_apply, ← one_div, norm_pow] at hct
  have he :
    valueUpperCorrection d a K t =
      -t * (normalizedValueUpper d a K (1 / t) - 1 - (1 / t) * ((d : ℝ) * (1 / 2 - a))) := by
    unfold valueUpperCorrection
    field_simp (disch := simp only [ht.ne', ne_eq, not_false_eq_true])
    ring
  have hf : ‖t‖ * ‖1 / t‖ ^ 2 = ‖1 / t‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht, abs_div, abs_one, abs_of_pos ht]
    field_simp (disch := simp only [ht.ne', ne_eq, not_false_eq_true])
  rw [he, norm_mul, norm_neg]
  have hh := mul_le_mul_of_nonneg_left hct (norm_nonneg t)
  change
    ‖t‖ * ‖normalizedValueUpper d a K (1 / t) - 1 - (1 / t) * ((d : ℝ) * (1 / 2 - a))‖ ≤
      ‖t‖ * (c * ‖1 / t‖ ^ 2) at hh
  convert hh using 1
  rw [← mul_assoc, mul_comm ‖t‖ c, mul_assoc, hf]

/-- The fixed-degree correction is little-o of one on the conductor filter.
Translate its zero limit to the little-o condition. This supplies the public error contract. -/
theorem isLittleO_valueUpperCorrection_on_conductorFilter (d : ℕ) (a K : ℝ) :
    Asymptotics.IsLittleO (conductorFilter d)
      (fun f : FixedDegreeFamily d ↦
        valueUpperCorrection d a K (Real.log (Real.log f.val.analyticConductor)))
      (fun _ ↦ (1 : ℝ)) := by
  exact
    (Asymptotics.isLittleO_one_iff ℝ).mpr (tendsto_valueUpperCorrection_on_conductorFilter d a K)

/-- For degree greater than one, the correction is `O(d^2(log d)^2/log log C)`
on the conductor filter. Compose the reciprocal-variable bound and multiply its scale by
the nonzero fixed-degree factor. This proves the public quantitative error scale for these
degrees; the factor vanishes at degree one, so this argument does not cover that case. -/
theorem isBigO_valueUpperCorrection_on_conductorFilter {d : ℕ} (hd : 1 < d) (a K : ℝ) :
    Asymptotics.IsBigO (conductorFilter d)
      (fun f : FixedDegreeFamily d ↦
        valueUpperCorrection d a K (Real.log (Real.log f.val.analyticConductor)))
      (fun f ↦ (d : ℝ) ^ 2 * (Real.log d) ^ 2 / Real.log (Real.log f.val.analyticConductor)) := by
  have ht :
    Filter.Tendsto (fun f : FixedDegreeFamily d ↦ Real.log (Real.log f.val.analyticConductor))
      (conductorFilter d) Filter.atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp Filter.tendsto_comap)
  have hn : (d : ℝ) ^ 2 * (Real.log d) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hd)).ne')
      (pow_ne_zero 2 (Real.log_pos (Nat.one_lt_cast.mpr hd)).ne')
  have hb := ((isBigO_valueUpperCorrection d a K).comp_tendsto ht).const_mul_right hn
  change
    Asymptotics.IsBigO (conductorFilter d)
      (fun f : FixedDegreeFamily d ↦
        valueUpperCorrection d a K (Real.log (Real.log f.val.analyticConductor)))
      (fun f ↦
        (d : ℝ) ^ 2 * (Real.log d) ^ 2 * (1 / Real.log (Real.log f.val.analyticConductor))) at hb
  simpa only [mul_one_div] using hb

/-- For every fixed degree and coefficients, the value correction is
`O(1/log log C)` on the conductor filter. Compose the reciprocal-variable estimate
with the double logarithm tending to infinity. Unlike the public degree-dependent
scale, this rate does not vanish at degree one. -/
theorem isBigO_valueUpperCorrection_reciprocal_on_conductorFilter (d : ℕ) (a K : ℝ) :
    Asymptotics.IsBigO (conductorFilter d)
      (fun f : FixedDegreeFamily d ↦
        valueUpperCorrection d a K (Real.log (Real.log f.val.analyticConductor)))
      (fun f ↦ 1 / Real.log (Real.log f.val.analyticConductor)) := by
  have ht :
    Filter.Tendsto (fun f : FixedDegreeFamily d ↦ Real.log (Real.log f.val.analyticConductor))
      (conductorFilter d) Filter.atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp Filter.tendsto_comap)
  exact (isBigO_valueUpperCorrection d a K).comp_tendsto ht

/-- For positive fixed degree, the value correction has the nonvanishing rate
`O(d²(1+log d)²/log log C)`. The fixed-degree multiplier is positive, including at
degree one. Multiply the reciprocal-logarithm estimate by this nonzero constant.
This supplies a rate usable for all degrees without altering the public proposition. -/
theorem isBigO_valueUpperCorrection_nonvanishing_on_conductorFilter {d : ℕ} (hd : 0 < d) (a K : ℝ) :
    Asymptotics.IsBigO (conductorFilter d)
      (fun f : FixedDegreeFamily d ↦
        valueUpperCorrection d a K (Real.log (Real.log f.val.analyticConductor)))
      (fun f ↦
        (d : ℝ) ^ 2 * (1 + Real.log d) ^ 2 / Real.log (Real.log f.val.analyticConductor)) := by
  have hl : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hd)
  have hp : 0 < 1 + Real.log (d : ℝ) := add_pos_of_pos_of_nonneg (by norm_num only) hl
  have hn := mul_ne_zero (pow_ne_zero 2 (Nat.cast_pos.mpr hd).ne') (pow_ne_zero 2 hp.ne')
  have hb := (isBigO_valueUpperCorrection_reciprocal_on_conductorFilter d a K).const_mul_right hn
  simpa only [mul_one_div] using hb

end PseudoPrime.LLS.Extensions.GeneralLFunction
