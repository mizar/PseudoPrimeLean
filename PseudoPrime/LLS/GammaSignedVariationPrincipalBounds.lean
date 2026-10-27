/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialAbsoluteVariation
public import PseudoPrime.LLS.GammaExponentialPrincipalBounds

/-! # Sharper principal Gamma sums from the exact absolute variation moments -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: RH, x >= 1 and y >= 0. Claim: the weighted arithmetic error integral
is at most sqrt(x)/20+(5517/4000)log(x)+2469/800. Use the affine RH envelope
and the exact sign change of the exponential variation density.
Role: replace the coarse absolute-variation allowance without finite computation. -/
theorem logWeighted_error_exponential_integral_le_signed_variation (hRH : RiemannHypothesis)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y) :
    |∫ u in (0 : ℝ)..y,
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
            ((u - 1) * Real.exp (-u))| ≤
      Real.sqrt x / 20 + (5517 / 4000 : ℝ) * Real.log x + 2469 / 800 := by
  have hx0 := zero_lt_one.trans_le hx
  have hf :
    ContinuousOn (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u)
      (Set.uIcc 0 y) := by
    rw [Set.uIcc_of_le hy]
    exact
      (AnalyticNumberTheory.Arithmetic.continuousOn_logWeightedMangoldtSum_scaled hx0 y).sub
        (continuous_const.mul continuous_id).continuousOn
  have h :=
    Analysis.norm_integral_exponential_variation_le_affine (a :=
      Real.sqrt x / 40 + (1839 / 1000 : ℝ) * Real.log x + 21 / 20) (b :=
      Real.sqrt x / 40 + (1839 / 1000 : ℝ))
      (by linarith only [Real.sqrt_nonneg x, Real.log_nonneg hx])
      (by linarith only [Real.sqrt_nonneg x]) hy hf
      (fun u hu ↦ (logWeighted_error_le_exponential_affine hRH hx hu.1).trans_eq (by ring))
  exact h.trans_eq (by ring)

/-- Input: a positive scale and any cap on the error integral at cutoff y >= 0.
Claim: the arithmetic variation integral is at most x plus that cap. Split off
the linear main term and evaluate its primitive. Role: share the finite-cutoff
transfer independently of the numerical error formula. -/
theorem logWeighted_exponential_integral_upper_of_error_cap {x y E : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hE :
      |∫ u in (0 : ℝ)..y,
            (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
              ((u - 1) * Real.exp (-u))| ≤
        E) :
    (∫ u in (0 : ℝ)..y,
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) *
          ((u - 1) * Real.exp (-u))) ≤
      x + E := by
  have hQ : Continuous (fun u : ℝ ↦ (u - 1) * Real.exp (-u)) :=
    (continuous_id.sub continuous_const).mul (Real.continuous_exp.comp continuous_id.neg)
  have hA := AnalyticNumberTheory.Arithmetic.continuousOn_logWeightedMangoldtSum_scaled hx y
  rw [← Set.uIcc_of_le hy] at hA
  have hR :
    ContinuousOn (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u)
      (Set.uIcc 0 y) :=
    hA.sub (continuous_const.mul continuous_id).continuousOn
  have heq :
    (fun u ↦
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) *
          ((u - 1) * Real.exp (-u))) =
      fun u ↦
      (x * u) * ((u - 1) * Real.exp (-u)) +
        (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
          ((u - 1) * Real.exp (-u)) := by
    funext u; ring
  have hM :
    IntervalIntegrable (fun u : ℝ ↦ (x * u) * ((u - 1) * Real.exp (-u))) MeasureTheory.volume 0 y :=
    ((continuous_const.mul continuous_id).mul hQ).intervalIntegrable 0 y
  have hsplit := intervalIntegral.integral_add hM ((hR.mul hQ.continuousOn).intervalIntegrable)
  simp only [Pi.mul_apply] at hsplit
  rw [heq, hsplit]
  have hm : (∫ u in (0 : ℝ)..y, (x * u) * ((u - 1) * Real.exp (-u))) ≤ x := by
    have heq :
      (fun u : ℝ ↦ (x * u) * ((u - 1) * Real.exp (-u))) = fun u ↦
        (0 + (-x) * u + x * u ^ 2) * Real.exp (-u) := by
      funext u; ring
    rw [heq, Analysis.integral_exponential_quadratic]
    have hp :=
      mul_nonneg (mul_nonneg hx.le (show 0 ≤ y ^ 2 + y + 1 by nlinarith only [hy, sq_nonneg y]))
        (Real.exp_pos (-y)).le
    nlinarith only [hp]
  have he :=
    le_abs_self
      (∫ u in (0 : ℝ)..y,
        (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
          ((u - 1) * Real.exp (-u)))
  linarith only [hm, he, hE]

/-- Input: RH, x >= 1 and any integral cap uniform in the nonnegative cutoff.
Claim: every finite exponential Mangoldt sum is at most x plus the cap.
Keep the boundary term and let it decay at infinity. Role: pass to the principal
series without exchanging an infinite sum with an integral. -/
theorem exponentialMangoldtSum_upper_uniform_of_integral_cap (hRH : RiemannHypothesis) {x E : ℝ}
    (hx : 1 ≤ x)
    (hI :
      ∀ y : ℝ,
        0 ≤ y →
          (∫ u in (0 : ℝ)..y,
              AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) *
                ((u - 1) * Real.exp (-u))) ≤
            x + E)
    (N : ℕ) : AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum x (N : ℝ) ≤ x + E := by
  have hx0 := zero_lt_one.trans_le hx
  have ht := (tendsto_exponential_boundary_zero x).const_add (x + E)
  rw [add_zero] at ht
  apply ge_of_tendsto ht
  apply ((Filter.eventually_ge_atTop (0 : ℝ)).and (Filter.eventually_ge_atTop ((N : ℝ) / x))).mono
  intro y hy
  have hcut : (N : ℝ) ≤ x * y := by simpa only [mul_comm] using (div_le_iff₀ hx0).mp hy.2
  have hm :
    AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum x (N : ℝ) ≤
      AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum x (x * y) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl (Nat.floor_mono hcut))
      (fun n _ _ ↦ mul_nonneg (Real.exp_pos _).le ArithmeticFunction.vonMangoldt_nonneg)
  have hb :
    AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum x (x * y) ≤
      x + E + ((4 * x + x ^ 2) * y ^ 2 + 4 * y) * Real.exp (-y) := by
    rw [AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum_eq_logWeighted_integral hx0 hy.1]
    have ht := mul_nonneg hx0.le hy.1
    have hA :=
      mul_le_mul_of_nonneg_left (logWeightedMangoldtSum_le_four_add_four hRH ht)
        (mul_nonneg hy.1 (Real.exp_pos (-y)).le)
    have hP :=
      mul_le_mul_of_nonneg_left (AnalyticNumberTheory.Arithmetic.psi_le_self_sq ht)
        (Real.exp_pos (-y)).le
    nlinarith only [hI y hy.1, hA, hP]
  exact hm.trans hb

/-- Input: RH, x >= 1 and any natural cutoff. Claim: the exponential Mangoldt
sum is at most x+sqrt(x)/20+(5517/4000)log(x)+2469/800. Combine the improved
error integral with the uniform-cutoff transfer. Role: supply the principal upper bound. -/
theorem exponentialMangoldtSum_upper_signed_variation (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x)
    (N : ℕ) :
    AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum x (N : ℝ) ≤
      x + Real.sqrt x / 20 + (5517 / 4000 : ℝ) * Real.log x + 2469 / 800 := by
  have h :=
    exponentialMangoldtSum_upper_uniform_of_integral_cap hRH hx
      (fun y hy ↦
        logWeighted_exponential_integral_upper_of_error_cap (zero_lt_one.trans_le hx) hy
          (logWeighted_error_exponential_integral_le_signed_variation hRH hx hy))
      N
  exact h.trans_eq (by ring)

/-- Input: RH and x >= 1. Claim: the full principal Gamma series satisfies the
displayed improved upper bound. Transfer every finite sum through the exact
principal identity, then use summability. Role: improve the principal subtraction
in quadratic and MR witness separation. -/
theorem gamma_level_one_sum_upper_signed_variation (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re ≤
      Real.sqrt x +
        (Real.sqrt x / 20 + (5517 / 4000 : ℝ) * Real.log x + 2469 / 800) / Real.sqrt x := by
  have hx0 := zero_lt_one.trans_le hx
  apply PaperStatements.gamma_level_one_sum_upper_of_finite_upper hx0
  intro N
  have heq :
    (∑ n ∈ Finset.Ioc 0 N,
        (PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) =
      AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum x (N : ℝ) / Real.sqrt x := by
    simpa only [Nat.floor_natCast] using
      PaperStatements.gamma_level_one_sum_eq_exponential (y := (N : ℝ)) hx0
  rw [heq]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hx0)).mpr
  rw [add_mul, div_mul_cancel₀ _ (Real.sqrt_pos.mpr hx0).ne', ← pow_two, Real.sq_sqrt hx0.le]
  simpa only [add_assoc] using exponentialMangoldtSum_upper_signed_variation hRH hx N

end PseudoPrime.LLS
