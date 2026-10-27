/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RiemannWeightedErrorBounds
public import PseudoPrime.LLS.RiemannRampIncrementBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExponentialRampErrorBounds

/-! # Actual principal ramp sum with uniform error seven -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The finite clipped-log representation of A(xu)-xu, extended continuously
outside the ramp support. It agrees with the actual arithmetic error on the
support and allows applying the global continuous functional norm estimate. -/
private noncomputable def rampErrorExtension (x u : ℝ) : ℝ :=
  (∑ n ∈ Finset.Ioc 0 ⌊x * (99 / 40)⌋₊,
      ArithmeticFunction.vonMangoldt n * Analysis.positiveLogRatio ((n : ℝ) / x) u) -
    x * u

/-- At positive scale, each clipped logarithmic atom is continuous. Sum the
finite weighted atoms and subtract the linear main term.
This supplies the functional norm estimate's continuity premise. -/
private theorem rampErrorExtension_continuous {x : ℝ} (hx : 0 < x) :
    Continuous (rampErrorExtension x) := by
  exact
    (continuous_finsetSum _
          (fun n hn ↦
            continuous_const.mul
              (Analysis.positiveLogRatio_continuous
                (div_pos (Nat.cast_pos.mpr (Finset.mem_Ioc.mp hn).1) hx)))).sub
      (continuous_const.mul continuous_id)

/-- The continuous extension equals the actual logarithmically weighted error
on [0,99/40]. Use the proved common-cutoff representation and subtract xu.
This transports the norm estimate back to the actual arithmetic sum. -/
private theorem rampErrorExtension_eqOn {x : ℝ} (hx : 0 < x) :
    Set.EqOn (rampErrorExtension x)
      (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u)
      (Set.Icc 0 (99 / 40)) := by
  exact fun u hu ↦
    congrArg (fun z : ℝ ↦ z - x * u)
      (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum_eq_clipped_scaled hx hu.1 hu.2).symm

/-- At scale x>=1, the uniform logarithmic and constant error term is nonnegative.
The endpoint (99/40)x is at least one. This permits weakening the variation allowance. -/
private theorem ramp_error_log_term_nonneg {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ (1839 / 1000 : ℝ) * Real.log (x * (99 / 40)) + 21 / 20 := by
  have hX : 1 ≤ x * (99 / 40) := by nlinarith only [hx]
  linarith only [Real.log_nonneg hX]

/-- At scale x>=1, the uniform square-root, logarithmic and constant error
allowance is nonnegative. Combine positivity of the square root and log term.
This supplies the nonnegative multiplier for the mass bound 85. -/
private theorem ramp_error_uniform_nonneg {x : ℝ} (hx : 1 ≤ x) :
    0 ≤
      Real.sqrt x / 20 * (63 / 40 : ℝ) +
        ((1839 / 1000 : ℝ) * Real.log (x * (99 / 40)) + 21 / 20) := by
  linarith only [ramp_error_log_term_nonneg hx, Real.sqrt_nonneg x]

/-- Under RH and x>=1, the continuous error extension is bounded uniformly
on the ramp support by the displayed allowance. Use the actual scaled arithmetic
error and sqrt(u)<=63/40. This is the pointwise input for integration. -/
private theorem rampErrorExtension_bound (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) (u : ℝ)
    (hu : u ∈ Set.Icc 0 (99 / 40)) :
    |rampErrorExtension x u| ≤
      Real.sqrt x / 20 * (63 / 40 : ℝ) +
        ((1839 / 1000 : ℝ) * Real.log (x * (99 / 40)) + 21 / 20) := by
  rw [rampErrorExtension_eqOn (zero_lt_one.trans_le hx) hu]
  dsimp only
  have hs :=
    mul_le_mul_of_nonneg_left (Analysis.sqrt_le_ramp_right hu.2)
      (div_nonneg (Real.sqrt_nonneg x) (by norm_num only : (0 : ℝ) ≤ 20))
  have he := logWeightedMangoldtSum_scaled_ramp_error hRH hx hu.1 hu.2
  linarith only [he, hs]

/-- Under RH and x>=1, the complete error functional has the stated explicit
square-root and endpoint-logarithmic bound. Apply the actual variation norm bound
85 to the continuous arithmetic error extension and transport back to A(xu)-xu.
This discharges the ramp finite sum's analytic error input. -/
theorem gamma_ramp_error_functional_bound (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    |AnalyticNumberTheory.Arithmetic.exponentialRampVariationFunctional
          (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u)| ≤
      (135 / 20 : ℝ) * Real.sqrt x +
        86 * ((1839 / 1000 : ℝ) * Real.log (x * (99 / 40)) + 21 / 20) := by
  have he :=
    AnalyticNumberTheory.Arithmetic.exponentialRampVariationFunctional_abs_le
      (rampErrorExtension_continuous (zero_lt_one.trans_le hx)) (ramp_error_uniform_nonneg hx)
      (rampErrorExtension_bound hRH hx)
  rw [AnalyticNumberTheory.Arithmetic.exponentialRampVariationFunctional_congr
      (rampErrorExtension_eqOn (zero_lt_one.trans_le hx))] at he
  linarith only [he, ramp_error_log_term_nonneg hx, Real.sqrt_nonneg x]

/-- For L>=46000 and x=(32/99)L^2, the proved functional allowance is at most
7 sqrt(x). Use the uniform logarithmic bound and sqrt(x)>=(9/16)L.
This closes the scalar part of the lower-cutoff error budget. -/
theorem gamma_ramp_error_numerator_le_seven_root {L : ℝ} (hL : 46000 ≤ L) :
    (135 / 20 : ℝ) * Real.sqrt ((32 / 99 : ℝ) * L ^ 2) +
        86 * ((1839 / 1000 : ℝ) * Real.log (((32 / 99 : ℝ) * L ^ 2) * (99 / 40)) + 21 / 20) ≤
      7 * Real.sqrt ((32 / 99 : ℝ) * L ^ 2) := by
  have hs := Analysis.ramp_scale_sqrt_lower (show (0 : ℝ) ≤ L by linarith only [hL])
  have hl := Analysis.ramp_endpoint_log_upper hL
  linarith only [hs, hl, hL]

/-- Under RH and L>=46000, the normalized actual ramp Mangoldt sum differs
from its exact main term by at most seven. Use the proved double-partial-summation
identity, the full variation norm bound and the scalar gate.
This is the two-sided finite principal-sum estimate for the smoothed comparison. -/
theorem gamma_ramp_sum_abs_error_le_seven (hRH : RiemannHypothesis) {L : ℝ} (hL : 46000 ≤ L) :
    |AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum ((32 / 99 : ℝ) * L ^ 2) /
            Real.sqrt ((32 / 99 : ℝ) * L ^ 2) -
          (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) *
            Real.sqrt ((32 / 99 : ℝ) * L ^ 2)| ≤
      7 := by
  have hx0 : 0 < (32 / 99 : ℝ) * L ^ 2 := zero_lt_one.trans_le (Analysis.ramp_scale_ge_one hL)
  rw [AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum_normalized_eq_main_add_error hx0,
    add_sub_cancel_left, abs_div, abs_of_pos (Real.sqrt_pos.mpr hx0)]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hx0)).mpr
  exact
    (gamma_ramp_error_functional_bound hRH (Analysis.ramp_scale_ge_one hL)).trans
      (gamma_ramp_error_numerator_le_seven_root hL)

/-- Under RH and L>=46000, the normalized actual ramp finite sum is at least
its exact mass times sqrt((32/99)L^2) minus seven. Take the lower side of the
proved absolute error bound. This is contract C7 for the coefficient-0.8 comparison. -/
theorem gamma_ramp_sum_lower_seven (hRH : RiemannHypothesis) {L : ℝ} (hL : 46000 ≤ L) :
    (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) *
          Real.sqrt ((32 / 99 : ℝ) * L ^ 2) -
        7 ≤
      AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum ((32 / 99 : ℝ) * L ^ 2) /
        Real.sqrt ((32 / 99 : ℝ) * L ^ 2) := by
  have h := (abs_le.mp (gamma_ramp_sum_abs_error_le_seven hRH hL)).1
  linarith only [h]

/-- The paired-jump error numerator at any real scale.
It combines three halves of the existing uniform smoothed-error envelope
with 42 times the certified short-ramp increment.
Its quotient by sqrt(x) bounds the normalized actual ramp error under RH. -/
noncomputable def gammaRampPairedErrorNumerator (x : ℝ) : ℝ :=
  (3 / 2 : ℝ) *
      (Real.sqrt x / 20 * (63 / 40 : ℝ) + (1839 / 1000 : ℝ) * Real.log (x * (99 / 40)) + 21 / 20) +
    42 * rampSmoothedIncrementError x

/-- Under RH and x at least one, the actual smoothed arithmetic error has
variation functional bounded by the paired-jump numerator.
Use the continuous finite extension, its uniform bound and the proved RH
short-ramp increment. This keeps the signed endpoint cancellation. -/
theorem gamma_ramp_error_functional_bound_paired (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    |AnalyticNumberTheory.Arithmetic.exponentialRampVariationFunctional
          (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u)| ≤
      gammaRampPairedErrorNumerator x := by
  have hx0 := zero_lt_one.trans_le hx
  have hb :
    rampErrorExtension x (99 / 40) =
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * (99 / 40)) - x * (99 / 40) :=
    rampErrorExtension_eqOn hx0 ⟨by norm_num only, le_refl _⟩
  have ha :
    rampErrorExtension x (247 / 100) =
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * (247 / 100)) - x * (247 / 100) :=
    rampErrorExtension_eqOn hx0 ⟨by norm_num only, by norm_num only⟩
  have hinc :
    |rampErrorExtension x (99 / 40) - rampErrorExtension x (247 / 100)| ≤
      rampSmoothedIncrementError x := by
    rw [hb, ha]
    exact logWeighted_ramp_error_increment hRH hx
  have h :=
    AnalyticNumberTheory.Arithmetic.exponentialRampVariationFunctional_abs_le_of_increment
      (rampErrorExtension_continuous hx0) (rampErrorExtension_bound hRH hx) hinc
  rw [AnalyticNumberTheory.Arithmetic.exponentialRampVariationFunctional_congr
      (rampErrorExtension_eqOn hx0)] at h
  simpa only [gammaRampPairedErrorNumerator, add_assoc] using h

/-- Under RH at any scale x at least one, the normalized actual ramp sum
is at least its exact main term minus the paired-jump numerator over sqrt(x).
Insert the complete error estimate into the proved arithmetic identity.
This is the principal lower input for smaller witness entrances. -/
theorem gamma_ramp_sum_lower_paired (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) * Real.sqrt x -
        gammaRampPairedErrorNumerator x / Real.sqrt x ≤
      AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x := by
  have hx0 := zero_lt_one.trans_le hx
  have he := gamma_ramp_error_functional_bound_paired hRH hx
  rw [AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum_normalized_eq_main_add_error hx0]
  have hdiv := div_le_div_of_nonneg_right (abs_le.mp he).1 (Real.sqrt_nonneg x)
  rw [neg_div] at hdiv
  linarith only [hdiv]

end PseudoPrime.LLS
