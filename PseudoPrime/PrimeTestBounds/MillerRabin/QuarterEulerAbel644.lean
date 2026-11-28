/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEuler644
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedAbelInterval
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerError570

/-! # Section 122 Euler abel estimates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The real-variable Euler weight at exponent 38/25. Its values at natural
indices enter the Mangoldt sum, and its derivative controls the Abel remainder. -/
noncomputable def eulerDensity644 (t : ℝ) : ℝ :=
  t ^ (-(157 / 100 : ℝ)) * (3 / 8 + 321 / 800 * Real.log t + 11449 / 80000 * Real.log t ^ 2)

/-- At every natural index the continuous-variable formula agrees with the
Dirichlet-series weight by the negative real power identity. -/
theorem eulerDensity644_nat (n : ℕ) : eulerDensity644 n = quarterEulerWeight644 n := by
  unfold eulerDensity644 quarterEulerWeight644
  rw [Real.rpow_neg (Nat.cast_nonneg n)]
  ring

/-- The derivative of the section 122 weight, written as a negative power times a
quadratic in the logarithm to permit termwise integration of its absolute value. -/
noncomputable def eulerSlope644 (t : ℝ) : ℝ :=
  -(t ^ (-(257 / 100 : ℝ))) *
    (3 / 16 + 27499 / 80000 * Real.log t + 1797493 / 8000000 * Real.log t ^ 2)

/-- At positive arguments the product and chain rules give the explicit Euler slope. -/
theorem eulerDensity644_deriv {t : ℝ} (ht : 0 < t) :
    HasDerivAt eulerDensity644 (eulerSlope644 t) t := by
  have hl := Real.hasDerivAt_log ht.ne'
  have hd :=
    (Real.hasDerivAt_rpow_const (p := -(157 / 100 : ℝ)) (Or.inl ht.ne')).mul
      (((hasDerivAt_const t (3 / 8 : ℝ)).add (hl.const_mul (321 / 800))).add
        ((hl.pow 2).const_mul (11449 / 80000)))
  apply hd.congr_deriv
  have hp : t ^ (-(257 / 100 : ℝ)) = t ^ (-(157 / 100 : ℝ)) / t := by
    rw [show -(257 / 100 : ℝ) = -(157 / 100 : ℝ) - 1 by norm_num only, Real.rpow_sub ht,
      Real.rpow_one]
  unfold eulerSlope644
  rw [show -(157 / 100 : ℝ) - 1 = -(257 / 100 : ℝ) by norm_num only, hp]
  simp only [Pi.add_apply, Pi.pow_apply]
  ring

/-- On a positive finite interval the Euler sum minus its main integral equals
the centered boundary difference minus the integral of the psi error against
the explicit slope. This specializes centered Abel summation to the section 122 tail. -/
theorem euler644_abel {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * quarterEulerWeight644 n) -
        (∫ t : ℝ in a..b, eulerDensity644 t) =
      (Chebyshev.psi b - b) * eulerDensity644 b - (Chebyshev.psi a - a) * eulerDensity644 a -
        ∫ t : ℝ in a..b, (Chebyshev.psi t - t) * eulerSlope644 t := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) := eulerDensity644_deriv (ha.trans_le ht.1)
  have hc : ContinuousOn eulerSlope644 (Set.Icc a b) := by
    intro t ht
    have hp := (ha.trans_le ht.1).ne'
    have hl := Real.continuousAt_log hp
    exact
      ((Real.continuousAt_rpow_const t _ (Or.inl hp)).neg.mul
          ((continuousAt_const.add (continuousAt_const.mul hl)).add
            (continuousAt_const.mul (hl.pow 2)))).continuousWithinAt
  have he : Set.EqOn (deriv eulerDensity644) eulerSlope644 (Set.Icc a b) := fun t ht ↦
    (hd t ht).deriv
  have hi : MeasureTheory.IntegrableOn (deriv eulerDensity644) (Set.Icc a b) :=
    (hc.congr he).integrableOn_Icc
  have h :=
    AnalyticNumberTheory.Arithmetic.mangoldt_centered_abel_interval ha.le hab
      (fun t ht ↦ (hd t ht).differentiableAt) hi
  simp only [eulerDensity644_nat] at h
  rw [h]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  exact congrArg ((Chebyshev.psi t - t) * ·) (he ht)

/-- Above one, the logarithm is nonnegative and every coefficient in the quadratic
factor is positive, so the derivative of the Euler weight is nonpositive. -/
theorem eulerSlope644_nonpos {t : ℝ} (ht : 1 ≤ t) : eulerSlope644 t ≤ 0 := by
  have hp := zero_le_one.trans ht
  have hl := Real.log_nonneg ht
  unfold eulerSlope644
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.rpow_nonneg hp _)) (by positivity)

/-- For a continuous majorant of the psi error on a positive interval above one,
bound the centered Abel integral by integrating the majorant against the negative slope. -/
theorem euler644_error_integral {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) {B : ℝ → ℝ}
    (hc : ContinuousOn B (Set.Icc a b)) (he : ∀ t ∈ Set.Icc a b, |Chebyshev.psi t - t| ≤ B t) :
    |∫ t : ℝ in a..b, (Chebyshev.psi t - t) * eulerSlope644 t| ≤
      ∫ t : ℝ in a..b, B t * -eulerSlope644 t := by
  have hs : ContinuousOn eulerSlope644 (Set.Icc a b) := by
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
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (eulerSlope644_nonpos (ha.trans ht.1.le))]
  exact mul_le_mul_of_nonneg_right h (neg_nonneg.mpr (eulerSlope644_nonpos (ha.trans ht.1.le)))

/-- From 1423 through one million, the finite psi certificate bounds the Euler
remainder integral by the four-fifths square-root integral. -/
theorem euler644_error_million {a b : ℝ} (ha : 1423 ≤ a) (hab : a ≤ b) (hb : b ≤ 1000000) :
    |∫ t : ℝ in a..b, (Chebyshev.psi t - t) * eulerSlope644 t| ≤
      ∫ t : ℝ in a..b, (4 / 5 : ℝ) * Real.sqrt t * -eulerSlope644 t := by
  apply
    euler644_error_integral (by linarith only [ha]) hab
      (continuousOn_const.mul Real.continuous_sqrt.continuousOn)
  exact fun t ht ↦
    AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million (ha.trans ht.1) (ht.2.trans hb)

/-- On finite intervals above one million, RH bounds the centered Euler remainder
by the explicit log-square integral needed for the section 122 tail. -/
theorem euler644_error_high (hRH : RiemannHypothesis) {a b : ℝ} (ha : 1000000 ≤ a) (hab : a ≤ b) :
    |∫ t : ℝ in a..b, (Chebyshev.psi t - t) * eulerSlope644 t| ≤
      ∫ t : ℝ in a..b, Real.sqrt t * (Real.log t ^ 2 / 24) * -eulerSlope644 t := by
  apply euler644_error_integral (by linarith only [ha]) hab
  · intro t ht
    have hp : 0 < t := by linarith only [ha, ht.1]
    exact
      (Real.continuous_sqrt.continuousAt.mul
          (((Real.continuousAt_log hp.ne').pow 2).div_const 24)).continuousWithinAt
  · exact fun t ht ↦ euler570_psi_high hRH (ha.trans ht.1)

end PseudoPrime.PrimeTestBounds.MillerRabin
