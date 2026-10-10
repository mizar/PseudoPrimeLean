/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Exponential pole primitives and Euler constant endpoint values

An antiderivative of `exp(-a t)/t²` for `a,t > 0` has a regularized right limit
at zero and a finite limit at infinity. These limits evaluate the zeta main term
when its pole and logarithmic singularities are combined before integration.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- The oriented interval integral of `log u * exp(-u)` from zero to a real endpoint `t`.
It is continuous even at zero and tends to minus the Euler--Mascheroni constant
as `t` tends to positive infinity. These endpoint values enter the pole primitive. -/
noncomputable def exponentialLogPrimitive (t : ℝ) : ℝ :=
  ∫ u : ℝ in 0..t, Real.log u * Real.exp (-u)

/-- On every bounded real interval, log t exp(-t) is integrable. Multiply the
locally integrable logarithm by the continuous exponential; this permits FTC at positive
endpoints. -/
theorem intervalIntegrable_log_mul_exp_neg (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ ↦ Real.log t * Real.exp (-t)) MeasureTheory.volume a b := by
  exact
    intervalIntegral.intervalIntegrable_log'.mul_continuousOn
      (Real.continuous_exp.comp continuous_neg).continuousOn

/-- The logarithmic exponential primitive is continuous on the whole real line.
Bounded-interval integrability gives continuity, including at the logarithmic singularity zero. -/
theorem continuous_exponentialLogPrimitive : Continuous exponentialLogPrimitive := by
  exact intervalIntegral.continuous_primitive intervalIntegrable_log_mul_exp_neg 0

/-- For t > 0, the derivative of the logarithmic exponential primitive is
log t exp(-t). Apply FTC where its integrand is continuous; use this in the pole antiderivative. -/
theorem hasDerivAt_exponentialLogPrimitive {t : ℝ} (ht : 0 < t) :
    HasDerivAt exponentialLogPrimitive (Real.log t * Real.exp (-t)) t := by
  have hc : ∀ u ∈ Set.Ioi (0 : ℝ), ContinuousAt (fun u : ℝ ↦ Real.log u * Real.exp (-u)) u :=
    fun u hu ↦
    (Real.continuousAt_log (ne_of_gt hu)).mul (Real.continuous_exp.comp continuous_neg).continuousAt
  exact
    intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_log_mul_exp_neg 0 t)
      (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi hc t ht) (hc t ht)

/-- At zero, the logarithmic exponential primitive tends to zero. Its global
continuity and the integral over an empty interval give the endpoint needed for pole
cancellation. -/
theorem tendsto_exponentialLogPrimitive_zero :
    Filter.Tendsto exponentialLogPrimitive (nhds 0) (nhds 0) := by
  simpa only [exponentialLogPrimitive, intervalIntegral.integral_same] using
    continuous_exponentialLogPrimitive.tendsto 0

/-- The function log t exp(-t) is integrable on t > 0. Its integral equals -gamma
and is nonzero by the positive lower bound for gamma; this justifies the improper endpoint limit. -/
theorem integrableOn_log_mul_exp_neg :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ Real.log t * Real.exp (-t)) (Set.Ioi 0) := by
  apply MeasureTheory.Integrable.of_integral_ne_zero
  rw [← neg_ne_zero, ← Real.eulerMascheroniConstant_eq_neg_integral_log]
  exact
    ne_of_gt
      (lt_trans (by norm_num only : (0 : ℝ) < 1 / 2) Real.one_half_lt_eulerMascheroniConstant)

/-- At positive infinity, the logarithmic exponential primitive tends to -gamma.
Pass from interval integrals to its integrable half-line integral and use the Euler constant
formula. -/
theorem tendsto_exponentialLogPrimitive_atTop :
    Filter.Tendsto exponentialLogPrimitive Filter.atTop (nhds (-Real.eulerMascheroniConstant)) := by
  change
    Filter.Tendsto (fun t : ℝ ↦ ∫ u : ℝ in 0..t, Real.log u * Real.exp (-u)) Filter.atTop
      (nhds (-Real.eulerMascheroniConstant))
  have h :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 integrableOn_log_mul_exp_neg
      Filter.tendsto_id
  simpa only [id_eq, ← neg_eq_iff_eq_neg.mpr Real.eulerMascheroniConstant_eq_neg_integral_log] using
    h

/-- For parameters a and t, define an antiderivative of exp(-a t)/t^2 using the
logarithmic exponential primitive. For a,t > 0 its derivative is the pole kernel; its endpoint
limits are used together with the zeta logarithmic derivative so that singularities cancel. -/
noncomputable def exponentialPolePrimitive (a t : ℝ) : ℝ :=
  -Real.exp (-a * t) / t - a * Real.exp (-a * t) * Real.log (a * t) -
    a * exponentialLogPrimitive (a * t)

/-- For a,t > 0, the exponential pole primitive has derivative exp(-a t)/t^2.
Differentiate its three terms and cancel the logarithmic contributions; this evaluates the
pole term. -/
theorem hasDerivAt_exponentialPolePrimitive {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    HasDerivAt (exponentialPolePrimitive a) (Real.exp (-a * t) / t ^ 2) t := by
  have he : HasDerivAt (fun u : ℝ ↦ Real.exp (-a * u)) (Real.exp (-a * t) * (-a)) t := by
    simpa only [neg_mul, id_eq, mul_one] using ((hasDerivAt_id t).const_mul (-a)).exp
  have hl := ((hasDerivAt_id t).const_mul a).log (ne_of_gt (mul_pos ha ht))
  have hJ :=
    (hasDerivAt_exponentialLogPrimitive (mul_pos ha ht)).comp t ((hasDerivAt_id t).const_mul a)
  have hd :=
    ((he.neg.div (hasDerivAt_id t) (ne_of_gt ht)).sub ((he.const_mul a).mul hl)).sub
      (hJ.const_mul a)
  simp only [id_eq, Pi.neg_apply, mul_one] at hd
  convert hd using 1
  · rfl
  · field_simp [ne_of_gt ht]
    ring

/-- For any real a, (1-exp(-a t))/t tends to a as t tends to zero from above.
Use the derivative of the negative exponential at zero to identify the finite part of the pole. -/
theorem tendsto_one_sub_exp_div_zero (a : ℝ) :
    Filter.Tendsto (fun t : ℝ ↦ (1 - Real.exp (-a * t)) / t) (nhdsWithin 0 (Set.Ioi 0))
      (nhds a) := by
  have hd := (((hasDerivAt_id (0 : ℝ)).const_mul (-a)).exp).neg
  have h := hd.tendsto_slope_zero_right
  simpa only [id_eq, mul_one, mul_zero, Real.exp_zero, zero_add, neg_neg, one_mul, smul_eq_mul,
    inv_mul_eq_div, neg_sub_neg, Pi.neg_apply] using h

/-- For a > 0, adding 1/t+a log t to the exponential pole primitive gives the
finite right limit a-a log a at zero. Combine the exponential difference quotient with t log t -> 0
and the continuous logarithmic exponential primitive; this cancels the zeta pole at one. -/
theorem tendsto_exponentialPolePrimitive_regularized_zero {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (fun t : ℝ ↦ exponentialPolePrimitive a t + 1 / t + a * Real.log t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (a - a * Real.log a)) := by
  have ht : Filter.Tendsto (fun t : ℝ ↦ t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    Filter.tendsto_id.mono_left nhdsWithin_le_nhds
  have he := Real.continuous_exp.continuousAt.tendsto.comp (ht.const_mul (-a))
  simp only [mul_zero, Real.exp_zero] at he
  have htA := ht.const_mul a
  simp only [mul_zero] at htA
  have hJ := tendsto_exponentialLogPrimitive_zero.comp htA
  have hs := tendsto_one_sub_exp_div_zero a
  have hl := tendsto_log_mul_rpow_nhdsGT_zero (r := (1 : ℝ)) zero_lt_one
  simp only [Real.rpow_one] at hl
  have hh := hs.mul hl
  have hf := ((hs.add (hh.const_mul a)).sub (he.const_mul (a * Real.log a))).sub (hJ.const_mul a)
  simp only [mul_zero, add_zero, mul_one, sub_zero] at hf
  apply hf.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := ht
  simp only [Function.comp_apply]
  dsimp only [exponentialPolePrimitive]
  rw [Real.log_mul (ne_of_gt ha) (ne_of_gt ht)]
  field_simp [ne_of_gt htpos]
  ring

/-- For a > 0, the exponential pole primitive tends to a times the Euler--Mascheroni
constant at infinity.
Exponential decay eliminates the rational and logarithmic terms, while the logarithmic exponential
primitive tends to -gamma. This is the upper endpoint in the combined zeta main integral. -/
theorem tendsto_exponentialPolePrimitive_atTop {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (exponentialPolePrimitive a) Filter.atTop
      (nhds (a * Real.eulerMascheroniConstant)) := by
  have ht := Filter.tendsto_id.const_mul_atTop ha
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp ht
  have hei := he.mul (tendsto_inv_atTop_zero (𝕜 := ℝ))
  have hpow := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 a ha
  simp only [Real.rpow_one] at hpow
  have hlog := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  simp only [pow_one, one_mul, add_zero] at hlog
  have hla := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (Real.log a)
  have hlogs := hla.add hlog
  have hprod := hpow.mul hlogs
  have hJ := tendsto_exponentialLogPrimitive_atTop.comp ht
  have hf := ((hei.neg.sub (hprod.const_mul a)).sub (hJ.const_mul a))
  simp only [mul_zero, add_zero, neg_zero, sub_zero, mul_neg, sub_neg_eq_add, zero_add] at hf
  apply hf.congr'
  filter_upwards [Filter.Ioi_mem_atTop (0 : ℝ)] with t ht
  have htpos : 0 < t := ht
  simp only [Function.comp_apply, id_eq]
  dsimp only [exponentialPolePrimitive]
  rw [Real.log_mul (ne_of_gt ha) (ne_of_gt htpos)]
  field_simp [ne_of_gt htpos]

end PseudoPrime.AnalyticNumberTheory.General
