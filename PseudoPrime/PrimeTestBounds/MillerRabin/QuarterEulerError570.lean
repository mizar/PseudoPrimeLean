/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerAbel570
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1423toMillion
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevPsiLeeNosal

/-! # Chebyshev error integrals for the section 31 Euler tail -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Above one, the logarithm is nonnegative and every coefficient in the quadratic
factor is positive, so the derivative of the Euler weight is nonpositive. -/
theorem eulerSlope570_nonpos {t : ℝ} (ht : 1 ≤ t) : eulerSlope570 t ≤ 0 := by
  have hp := zero_le_one.trans ht
  have hl := Real.log_nonneg ht
  unfold eulerSlope570
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.rpow_nonneg hp _)) (by positivity)

/-- For a continuous majorant of the psi error on a positive interval above one,
bound the centered Abel integral by integrating the majorant against the negative slope. -/
theorem euler570_error_integral {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) {B : ℝ → ℝ}
    (hc : ContinuousOn B (Set.Icc a b)) (he : ∀ t ∈ Set.Icc a b, |Chebyshev.psi t - t| ≤ B t) :
    |∫ t : ℝ in a..b, (Chebyshev.psi t - t) * eulerSlope570 t| ≤
      ∫ t : ℝ in a..b, B t * -eulerSlope570 t := by
  have hs : ContinuousOn eulerSlope570 (Set.Icc a b) := by
    intro t ht
    have hp := (zero_lt_one.trans_le (ha.trans ht.1)).ne'
    have hl := Real.continuousAt_log hp
    exact
      ((Real.continuousAt_rpow_const t _ (Or.inl hp)).neg.mul
          ((continuousAt_const.add (continuousAt_const.mul hl)).add
            (continuousAt_const.mul (hl.pow 2)))).continuousWithinAt
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab, ← Real.norm_eq_abs]
  apply
    MeasureTheory.norm_integral_le_of_norm_le
      ((hc.mul hs.neg).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
  have h := he t ⟨ht.1.le, ht.2⟩
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (eulerSlope570_nonpos (ha.trans ht.1.le))]
  exact mul_le_mul_of_nonneg_right h (neg_nonneg.mpr (eulerSlope570_nonpos (ha.trans ht.1.le)))

/-- From 1423 through one million, the finite psi certificate bounds the Euler
remainder integral by the four-fifths square-root integral. -/
theorem euler570_error_million {a b : ℝ} (ha : 1423 ≤ a) (hab : a ≤ b) (hb : b ≤ 1000000) :
    |∫ t : ℝ in a..b, (Chebyshev.psi t - t) * eulerSlope570 t| ≤
      ∫ t : ℝ in a..b, (4 / 5 : ℝ) * Real.sqrt t * -eulerSlope570 t := by
  apply
    euler570_error_integral (by linarith only [ha]) hab
      (continuousOn_const.mul Real.continuous_sqrt.continuousOn)
  exact fun t ht ↦
    AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million (ha.trans ht.1) (ht.2.trans hb)

/-- From 101 onward, RH gives the square-root log-square majorant for psi by
dropping the nonnegative log-log correction in the Lee–Nosal bound. -/
theorem psi_log_sq_of_RH (hRH : RiemannHypothesis) {t : ℝ} (ht : 101 ≤ t) :
    |Chebyshev.psi t - t| ≤ Real.sqrt t * (Real.log t ^ 2 / 24) := by
  have hp : 0 < t := by linarith only [ht]
  have hl : 1 ≤ Real.log t :=
    (Real.le_log_iff_exp_le hp).2 (Real.exp_one_lt_d9.le.trans (by linarith only [ht]))
  have hd : (24 : ℝ) ≤ 8 * Real.pi := by linarith only [Real.pi_gt_three]
  have h := AnalyticNumberTheory.Arithmetic.psi_lee_nosal_of_RH hRH ht
  have hm : Real.log t * (Real.log t - Real.log (Real.log t)) ≤ Real.log t ^ 2 := by
    nlinarith only [mul_nonneg (zero_le_one.trans hl) (Real.log_nonneg hl)]
  have hb :=
    (div_le_div_of_nonneg_right hm (by positivity : 0 ≤ 8 * Real.pi)).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num only : (0 : ℝ) < 24) hd)
  simpa only [mul_comm] using (div_le_iff₀ (Real.sqrt_pos.mpr hp)).mp (h.trans hb)

/-- Above one million, RH gives the square-root log-square majorant for psi by
dropping the nonnegative log-log correction in the Lee–Nosal bound. -/
theorem euler570_psi_high (hRH : RiemannHypothesis) {t : ℝ} (ht : 1000000 ≤ t) :
    |Chebyshev.psi t - t| ≤ Real.sqrt t * (Real.log t ^ 2 / 24) := by
  exact psi_log_sq_of_RH hRH (by linarith only [ht])

/-- On finite intervals above one million, RH bounds the centered Euler remainder
by the explicit log-square integral needed for the section 31 tail. -/
theorem euler570_error_high (hRH : RiemannHypothesis) {a b : ℝ} (ha : 1000000 ≤ a) (hab : a ≤ b) :
    |∫ t : ℝ in a..b, (Chebyshev.psi t - t) * eulerSlope570 t| ≤
      ∫ t : ℝ in a..b, Real.sqrt t * (Real.log t ^ 2 / 24) * -eulerSlope570 t := by
  apply euler570_error_integral (by linarith only [ha]) hab
  · intro t ht
    have hp : 0 < t := by linarith only [ha, ht.1]
    exact
      (Real.continuous_sqrt.continuousAt.mul
          (((Real.continuousAt_log hp.ne').pow 2).div_const 24)).continuousWithinAt
  · exact fun t ht ↦ euler570_psi_high hRH (ha.trans ht.1)

/-- Under RH, splitting the finite Euler tail at one million cancels the intermediate
psi boundary. The two remaining error integrals use the bounds valid on each side. -/
theorem euler570_tail_split (hRH : RiemannHypothesis) {b : ℝ} (hb : 1000000 ≤ b) :
    let a : ℝ := 2701
    let v : ℝ := 1000000
    (∫ t : ℝ in a..v, eulerDensity570 t) + (∫ t : ℝ in v..b, eulerDensity570 t) +
          (Chebyshev.psi b - b) * eulerDensity570 b -
        (Chebyshev.psi a - a) * eulerDensity570 a -
        (∫ t : ℝ in a..v, (4 / 5 : ℝ) * Real.sqrt t * -eulerSlope570 t) -
        (∫ t : ℝ in v..b, Real.sqrt t * (Real.log t ^ 2 / 24) * -eulerSlope570 t) ≤
      ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n := by
  intro a v
  have hav : a ≤ v := by norm_num only [a, v]
  rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.floor_mono hav) (Nat.floor_mono hb),
    Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]
  have hlo := euler570_abel (a := a) (by norm_num only [a]) hav
  have hhi := euler570_abel (a := v) (by norm_num only [v]) hb
  have el :=
    (abs_le.mp (euler570_error_million (by norm_num only [a] : 1423 ≤ a) hav (le_refl v))).2
  have eh := (abs_le.mp (euler570_error_high hRH (le_refl v) hb)).2
  linear_combination -hlo - hhi + el + eh

end PseudoPrime.PrimeTestBounds.MillerRabin
