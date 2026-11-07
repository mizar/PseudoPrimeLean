/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaSignedVariationPrincipalBounds

/-! # Finite exponential Mangoldt sums from signed variation -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A lower bound for the finite exponential Mangoldt sum follows from a
Chebyshev lower bound, a weighted boundary error bound, and a signed-variation
integral error bound. The exact second Abel identity retains both boundary
terms and the main integral. This interface supplies the analytic Gamma cells. -/
theorem finite_exp_lower_of_signed_variation {x y P S E : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hp : x * y - P ≤ Chebyshev.psi (x * y))
    (hs : |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * y) - x * y| ≤ S)
    (he :
      |∫ u in (0 : ℝ)..y,
            (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
              ((u - 1) * Real.exp (-u))| ≤
        E) :
    x * (1 - Real.exp (-y)) - Real.exp (-y) * (P + y * S) - E ≤
      AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum x (x * y) := by
  have hQ : Continuous (fun u : ℝ ↦ (u - 1) * Real.exp (-u)) :=
    (continuous_id.sub continuous_const).mul (Real.continuous_exp.comp continuous_id.neg)
  have hA := AnalyticNumberTheory.Arithmetic.continuousOn_logWeightedMangoldtSum_scaled hx y
  rw [← Set.uIcc_of_le hy] at hA
  have hR :
    ContinuousOn (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u)
      (Set.uIcc 0 y) :=
    hA.sub (continuous_const.mul continuous_id).continuousOn
  have hM :
    IntervalIntegrable (fun u : ℝ ↦ (x * u) * ((u - 1) * Real.exp (-u))) MeasureTheory.volume 0 y :=
    ((continuous_const.mul continuous_id).mul hQ).intervalIntegrable 0 y
  have hsplit := intervalIntegral.integral_add hM ((hR.mul hQ.continuousOn).intervalIntegrable)
  simp only [Pi.mul_apply] at hsplit
  have heq :
    (fun u ↦
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) *
          ((u - 1) * Real.exp (-u))) =
      fun u ↦
      (x * u) * ((u - 1) * Real.exp (-u)) +
        (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
          ((u - 1) * Real.exp (-u)) := by
    funext u
    ring
  have hm :
    (∫ u in (0 : ℝ)..y, (x * u) * ((u - 1) * Real.exp (-u))) =
      x - x * (y ^ 2 + y + 1) * Real.exp (-y) := by
    have hf :
      (fun u : ℝ ↦ (x * u) * ((u - 1) * Real.exp (-u))) = fun u ↦
        (0 + (-x) * u + x * u ^ 2) * Real.exp (-u) := by
      funext u
      ring
    rw [hf, Analysis.integral_exponential_quadratic]
    ring
  have h := AnalyticNumberTheory.Arithmetic.expMangoldtSum_eq_logWeighted_integral hx hy
  rw [heq, hsplit, hm] at h
  have hb := (abs_le.mp hs).1
  have hi := (abs_le.mp he).1
  have hbp := mul_le_mul_of_nonneg_left hp (Real.exp_pos (-y)).le
  have hbs := mul_le_mul_of_nonneg_left hb (mul_nonneg hy (Real.exp_pos (-y)).le)
  nlinarith only [h, hi, hbp, hbs]

/-- Under RH, the sharp weighted boundary and signed-variation estimates turn
any explicit Chebyshev lower bound into a finite exponential main-sum bound.
The remaining input is the pointwise lower bound for `psi` at the cutoff. -/
theorem finite_exp_lower_signed_rh (hRH : RiemannHypothesis) {x y P : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y)
    (hcut : 1 < x * y) (hp : x * y - P ≤ Chebyshev.psi (x * y)) :
    x * (1 - Real.exp (-y)) -
        Real.exp (-y) *
          (P + y * (Real.sqrt (x * y) / 20 + (1839 / 1000 : ℝ) * Real.log (x * y) + 21 / 20)) -
        (Real.sqrt x / 20 + (5517 / 4000 : ℝ) * Real.log x + 2469 / 800) ≤
      AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum x (x * y) := by
  exact
    finite_exp_lower_of_signed_variation (zero_lt_one.trans_le hx) hy hp
      (LLS.logWeightedMangoldtSum_error_le_refined hRH hcut)
      (LLS.logWeighted_exp_error_signedVariation_RH hRH hx hy)

/-- Under RH, the explicit signed-variation estimate bounds the normalized
finite Gamma main sum at cutoff `x*y`. Divide the finite exponential estimate
by the positive square root and remove the zero Mangoldt term. This is the
main-sum interface needed by analytic Gamma comparisons. -/
theorem finite_gamma_lower_signed_rh (hRH : RiemannHypothesis) {x y P : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y)
    (hcut : 1 < x * y) (hp : x * y - P ≤ Chebyshev.psi (x * y)) :
    (x * (1 - Real.exp (-y)) -
          Real.exp (-y) *
            (P + y * (Real.sqrt (x * y) / 20 + (1839 / 1000 : ℝ) * Real.log (x * y) + 21 / 20)) -
          (Real.sqrt x / 20 + (5517 / 4000 : ℝ) * Real.log x + 2469 / 800)) /
        Real.sqrt x ≤
      ∑ n ∈ Finset.Ioc 0 ⌊x * y⌋₊,
        Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n / Real.sqrt x := by
  have h :=
    div_le_div_of_nonneg_right (finite_exp_lower_signed_rh hRH hx hy hcut hp) (Real.sqrt_nonneg x)
  unfold AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum at h
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons] at h
  simp only [Nat.cast_zero, neg_zero, zero_div, Real.exp_zero, ArithmeticFunction.map_zero,
    mul_zero, zero_add] at h
  rw [Finset.sum_div] at h
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
