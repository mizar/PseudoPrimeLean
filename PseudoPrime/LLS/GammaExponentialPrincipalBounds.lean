/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.GammaPrincipalUpperBounds
public import PseudoPrime.LLS.GammaSmoothedPrincipalBounds
public import PseudoPrime.LLS.RiemannExponentialErrorBounds
public import PseudoPrime.Analysis.ExponentialPolynomialMoments
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExponentialLogWeightedSummation

/-! # Full principal Gamma sum with explicit error one fifth -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under RH, x>=1 and u>=0, bound the actual logarithmically weighted error
times the exponential variation density by the displayed quadratic-exponential
majorant. Combine the affine sharp error with |u-1|<=u+1.
This supplies an integrable polynomial envelope on each finite cutoff interval. -/
theorem logWeighted_error_mul_variation_le (hRH : RiemannHypothesis) {x u : ℝ} (hx : 1 ≤ x)
    (hu : 0 ≤ u) :
    |(AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
          ((u - 1) * Real.exp (-u))| ≤
      ((Real.sqrt x / 40 + (1839 / 1000 : ℝ) * Real.log x + 21 / 20) +
          (Real.sqrt x / 20 + (1839 / 1000 : ℝ) * Real.log x + 21 / 20 + 1839 / 1000) * u +
          (Real.sqrt x / 40 + 1839 / 1000) * u ^ 2) *
        Real.exp (-u) := by
  have hr := logWeighted_error_le_exponential_affine hRH hx hu
  have hs := abs_sub u (1 : ℝ)
  rw [abs_of_nonneg hu, abs_one] at hs
  have hm := mul_le_mul hr hs (abs_nonneg (u - 1)) ((abs_nonneg _).trans hr)
  have he := mul_le_mul_of_nonneg_right hm (Real.exp_pos (-u)).le
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos (-u))]
  rw [mul_assoc] at he
  exact he.trans_eq (by ring)

/-- At positive scale, the actual logarithmically weighted error is continuous
on each finite interval [0,y]. Subtract the linear main term from the proved
arithmetic continuity. This supplies the finite error integral's integrability. -/
private theorem continuousOn_logWeighted_error_scaled {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    ContinuousOn (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u)
      (Set.uIcc 0 y) := by
  rw [Set.uIcc_of_le hy]
  exact
    (AnalyticNumberTheory.Arithmetic.continuousOn_logWeightedMangoldtSum_scaled hx y).sub
      (continuous_const.mul continuous_id).continuousOn

/-- For nonnegative quadratic coefficients and a continuous function on [0,y],
a pointwise quadratic-exponential bound controls the integral norm by a+b+2c.
Use norm domination, integral monotonicity and the exact finite moments.
This is the reusable finite-cutoff error estimate. -/
private theorem norm_integral_exponential_variation_le {a b c y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hy : 0 ≤ y) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.uIcc 0 y))
    (hbound :
      ∀ u ∈ Set.Icc 0 y,
        |f u * ((u - 1) * Real.exp (-u))| ≤ (a + b * u + c * u ^ 2) * Real.exp (-u)) :
    |∫ u in (0 : ℝ)..y, f u * ((u - 1) * Real.exp (-u))| ≤ a + b + 2 * c := by
  have hQ : Continuous (fun u : ℝ ↦ (u - 1) * Real.exp (-u)) :=
    (continuous_id.sub continuous_const).mul (Real.continuous_exp.comp continuous_id.neg)
  have hn :=
    intervalIntegral.norm_integral_le_integral_norm (f := fun u ↦ f u * ((u - 1) * Real.exp (-u)))
      (μ := MeasureTheory.volume) hy
  simp only [Real.norm_eq_abs] at hn
  have hi :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hy (f := fun u ↦
      |f u * ((u - 1) * Real.exp (-u))|) (g := fun u ↦ (a + b * u + c * u ^ 2) * Real.exp (-u))
      ((hf.mul hQ.continuousOn).abs.intervalIntegrable)
      ((show Continuous (fun u : ℝ ↦ (a + b * u + c * u ^ 2) * Real.exp (-u)) from
            (continuous_const.add (continuous_const.mul continuous_id) |>.add
                  (continuous_const.mul (continuous_id.pow 2))).mul
              (Real.continuous_exp.comp continuous_id.neg)).intervalIntegrable
        (0 : ℝ) y)
      hbound
  exact hn.trans (hi.trans (Analysis.integral_exponential_quadratic_le ha hb hc hy))

/-- Under RH, x>=1 and y>=0, the actual logarithmically weighted error integral
has the stated bound independent of y. Integrate the proved quadratic-exponential
envelope and collect its coefficients. This replaces the three-quarter-power
error in the full principal Gamma sum. -/
theorem logWeighted_error_exponential_integral_le (hRH : RiemannHypothesis) {x y : ℝ} (hx : 1 ≤ x)
    (hy : 0 ≤ y) :
    |∫ u in (0 : ℝ)..y,
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
            ((u - 1) * Real.exp (-u))| ≤
      Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10 := by
  have h :=
    norm_integral_exponential_variation_le (a :=
      Real.sqrt x / 40 + (1839 / 1000 : ℝ) * Real.log x + 21 / 20) (b :=
      Real.sqrt x / 20 + (1839 / 1000 : ℝ) * Real.log x + 21 / 20 + 1839 / 1000) (c :=
      Real.sqrt x / 40 + 1839 / 1000) (by linarith only [Real.sqrt_nonneg x, Real.log_nonneg hx])
      (by linarith only [Real.sqrt_nonneg x, Real.log_nonneg hx])
      (by linarith only [Real.sqrt_nonneg x]) hy
      (continuousOn_logWeighted_error_scaled (zero_lt_one.trans_le hx) hy)
      (fun u hu ↦ logWeighted_error_mul_variation_le hRH hx hu.1)
  exact h.trans_eq (by ring)

/-- For x,y>=0, the linear main-term variation integral is at most x.
Evaluate the quadratic-exponential primitive and discard its nonnegative
endpoint remainder. This bounds the truncated main term uniformly in y. -/
private theorem linear_exponential_integral_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (∫ u in (0 : ℝ)..y, (x * u) * ((u - 1) * Real.exp (-u))) ≤ x := by
  have hi :
    (∫ u in (0 : ℝ)..y, (x * u) * ((u - 1) * Real.exp (-u))) =
      ∫ u in (0 : ℝ)..y, (0 + (-x) * u + x * u ^ 2) * Real.exp (-u) := by
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    ring
  rw [hi, Analysis.integral_exponential_quadratic]
  have hp : 0 ≤ x * (y ^ 2 + y + 1) := mul_nonneg hx (by nlinarith only [hy, sq_nonneg y])
  have he := mul_nonneg hp (Real.exp_pos (-y)).le
  nlinarith only [he]

/-- For positive x and y>=0, split the actual weighted integral into its
linear main term and arithmetic error. Supply integrability of both products
before splitting. This retains the exact normalization in the upper estimate. -/
private theorem logWeighted_exponential_integral_eq_main_error {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    (∫ u in (0 : ℝ)..y,
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) *
          ((u - 1) * Real.exp (-u))) =
      (∫ u in (0 : ℝ)..y, (x * u) * ((u - 1) * Real.exp (-u))) +
        ∫ u in (0 : ℝ)..y,
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
            ((u - 1) * Real.exp (-u)) := by
  have hR := continuousOn_logWeighted_error_scaled hx hy
  have hQ : Continuous (fun u : ℝ ↦ (u - 1) * Real.exp (-u)) :=
    (continuous_id.sub continuous_const).mul (Real.continuous_exp.comp continuous_id.neg)
  have he :
    (fun u ↦
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) *
          ((u - 1) * Real.exp (-u))) =
      fun u ↦
      (x * u) * ((u - 1) * Real.exp (-u)) +
        (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
          ((u - 1) * Real.exp (-u)) := by
    funext u
    ring
  rw [he]
  exact
    intervalIntegral.integral_add (f := fun u ↦ (x * u) * ((u - 1) * Real.exp (-u))) (g := fun u ↦
      (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
        ((u - 1) * Real.exp (-u)))
      (((continuous_const.mul continuous_id).mul hQ).intervalIntegrable (0 : ℝ) y)
      ((hR.mul hQ.continuousOn).intervalIntegrable)

/-- Under RH, x>=1 and y>=0, the logarithmically weighted variation integral
is at most x plus the displayed square-root and logarithmic allowance.
Combine the main integral and error norm estimates.
This is the finite integral contribution to the full exponential sum. -/
theorem logWeighted_exponential_integral_upper (hRH : RiemannHypothesis) {x y : ℝ} (hx : 1 ≤ x)
    (hy : 0 ≤ y) :
    (∫ u in (0 : ℝ)..y,
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) *
          ((u - 1) * Real.exp (-u))) ≤
      x + Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10 := by
  rw [logWeighted_exponential_integral_eq_main_error (zero_lt_one.trans_le hx) hy]
  have hm := linear_exponential_integral_le (zero_le_one.trans hx) hy
  have he :=
    le_abs_self
      (∫ u in (0 : ℝ)..y,
        (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
          ((u - 1) * Real.exp (-u)))
  have hb := logWeighted_error_exponential_integral_le hRH hx hy
  linarith only [hm, he, hb]

/-- Under RH, x>=1 and y>=0, bound the actual exponential sum through xy
by the uniform allowance and an explicit quadratic-exponential boundary term.
Use the exact logarithmic partial-summation formula and polynomial bounds
for A(xy) and psi(xy). This preserves both endpoints before taking the limit. -/
theorem exponentialMangoldtSum_upper_with_boundary (hRH : RiemannHypothesis) {x y : ℝ} (hx : 1 ≤ x)
    (hy : 0 ≤ y) :
    AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum x (x * y) ≤
      x + Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10 +
        ((4 * x + x ^ 2) * y ^ 2 + 4 * y) * Real.exp (-y) := by
  rw [AnalyticNumberTheory.Arithmetic.expMangoldtSum_eq_logWeighted_integral
      (zero_lt_one.trans_le hx) hy]
  have hI := logWeighted_exponential_integral_upper hRH hx hy
  have ht : 0 ≤ x * y := mul_nonneg (zero_le_one.trans hx) hy
  have hA :=
    mul_le_mul_of_nonneg_left (logWeightedMangoldtSum_le_four_add_four hRH ht)
      (mul_nonneg hy (Real.exp_pos (-y)).le)
  have hP :=
    mul_le_mul_of_nonneg_left (AnalyticNumberTheory.Arithmetic.psi_le_self_sq ht)
      (Real.exp_pos (-y)).le
  nlinarith only [hI, hA, hP]

/-- At any fixed real scale, increasing the cutoff increases the finite
exponential Mangoldt sum. Include the smaller floor interval and use nonnegative
summands. This compares a fixed finite sum with moving large cutoffs. -/
private theorem exponentialMangoldtSum_mono_cutoff {x a b : ℝ} (hab : a ≤ b) :
    AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum x a ≤
      AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum x b := by
  exact
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl (Nat.floor_mono hab))
      (fun n _ _ ↦ mul_nonneg (Real.exp_pos _).le ArithmeticFunction.vonMangoldt_nonneg)

/-- For any fixed x, the explicit quadratic-exponential boundary tends to zero
as y tends to infinity. Use the two polynomial-exponential decay limits.
This removes the exact finite endpoint terms in the uniform upper bound. -/
theorem tendsto_exponential_boundary_zero (x : ℝ) :
    Filter.Tendsto (fun y : ℝ ↦ ((4 * x + x ^ 2) * y ^ 2 + 4 * y) * Real.exp (-y)) Filter.atTop
      (nhds 0) := by
  have h :=
    ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul (4 * x + x ^ 2)).add
      ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul (4 : ℝ))
  simp only [mul_zero, zero_add, pow_one] at h
  exact h.congr' (Filter.Eventually.of_forall (fun y ↦ by ring))

/-- Under RH and x>=1, every natural cutoff has the displayed uniform
exponential Mangoldt upper bound. Compare with larger real cutoffs and let the
proved boundary polynomial decay to zero. This passage uses finite integrals;
no exchange of an infinite sum and integral is assumed. -/
theorem exponentialMangoldtSum_upper_uniform (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x)
    (N : ℕ) :
    AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum x (N : ℝ) ≤
      x + Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10 := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have ht :=
    (tendsto_exponential_boundary_zero x).const_add
      (x + Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10)
  rw [add_zero] at ht
  apply ge_of_tendsto ht
  apply ((Filter.eventually_ge_atTop (0 : ℝ)).and (Filter.eventually_ge_atTop ((N : ℝ) / x))).mono
  intro y hy
  have hcut : (N : ℝ) ≤ x * y := by simpa only [mul_comm] using (div_le_iff₀ hx0).mp hy.2
  exact
    (exponentialMangoldtSum_mono_cutoff hcut).trans
      (exponentialMangoldtSum_upper_with_boundary hRH hx hy.1)

/-- For L>=46000 and x=(32/99)L^2, the uniform exponential error allowance
is at most sqrt(x)/5. Use the logarithmic endpoint and scale lower bounds.
This fixes the principal error budget for the smoothed coefficient-0.8 comparison. -/
theorem gamma_exponential_error_le_one_fifth_root {L : ℝ} (hL : 46000 ≤ L) :
    Real.sqrt ((32 / 99 : ℝ) * L ^ 2) / 8 +
        (1839 / 1000 : ℝ) * (2 * Real.log ((32 / 99 : ℝ) * L ^ 2) + 3) +
        21 / 10 ≤
      (1 / 5 : ℝ) * Real.sqrt ((32 / 99 : ℝ) * L ^ 2) := by
  have hx1 := Analysis.ramp_scale_ge_one hL
  have hx0 : 0 < (32 / 99 : ℝ) * L ^ 2 := zero_lt_one.trans_le hx1
  have hc :=
    Real.log_le_log hx0
      (show (32 / 99 : ℝ) * L ^ 2 ≤ ((32 / 99 : ℝ) * L ^ 2) * (99 / 40) by nlinarith only [hx1])
  have hl := Analysis.ramp_endpoint_log_upper hL
  have hs := Analysis.ramp_scale_sqrt_lower (show (0 : ℝ) ≤ L by linarith only [hL])
  linarith only [hc, hl, hs, hL]

end PseudoPrime.LLS
