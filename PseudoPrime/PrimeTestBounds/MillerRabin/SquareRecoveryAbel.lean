/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt81Million
public import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Abel lower bound for the square recovery weight -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On a subinterval of [17, 1000000], the certified square-root psi error
bounds a weighted Mangoldt sum from below for a decreasing differentiable
weight vanishing at the upper endpoint. Abel summation retains the lower
endpoint atom in psi and excludes it from the sum. -/
theorem square_recovery_abel_lower {a b : ℝ} (ha : 17 ≤ a) (hab : a ≤ b) (hb : b ≤ 1000000)
    {f : ℝ → ℝ} (hf : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hd : ContinuousOn (deriv f) (Set.Icc a b)) (hneg : ∀ t ∈ Set.Icc a b, deriv f t ≤ 0)
    (hfa : 0 ≤ f a) (hfb : f b = 0) :
    -(f a * (a + 81 / 100 * Real.sqrt a)) -
        (∫ t in a..b, deriv f t * (t - 81 / 100 * Real.sqrt t)) ≤
      ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f k * ArithmeticFunction.vonMangoldt k := by
  have err (t : ℝ) (ht : t ∈ Set.Icc a b) : |Chebyshev.psi t - t| ≤ 81 / 100 * Real.sqrt t := by
    exact
      (div_le_iff₀
            (Real.sqrt_pos.mpr ((by norm_num only : (0 : ℝ) < 17).trans_le (ha.trans ht.1)))).mp
        (AnalyticNumberTheory.Arithmetic.psi81_million (ha.trans ht.1) (ht.2.trans hb))
  have abel :=
    sum_mul_eq_sub_sub_integral_mul ArithmeticFunction.vonMangoldt
      ((by norm_num only : (0 : ℝ) ≤ 17).trans ha) hab hf hd.integrableOn_Icc
  simp only [← Chebyshev.psi_eq_sum_Icc, hfb, zero_mul, zero_sub] at abel
  rw [← intervalIntegral.integral_of_le hab] at abel
  have hdu : ContinuousOn (deriv f) (Set.uIcc a b) := by rwa [Set.uIcc_of_le hab]
  have hi :=
    (Chebyshev.psi_mono.intervalIntegrable (μ := MeasureTheory.volume)).continuousOn_mul hdu
  have hc : Continuous (fun t : ℝ ↦ t - 81 / 100 * Real.sqrt t) :=
    continuous_id.sub (continuous_const.mul Real.continuous_sqrt)
  have hcomp :=
    intervalIntegral.integral_mono_on hab hi (hdu.mul hc.continuousOn).intervalIntegrable
      (fun t ht ↦
        mul_le_mul_of_nonpos_left
          (by linarith only [(abs_le.mp (err t ht)).1] :
            t - 81 / 100 * Real.sqrt t ≤ Chebyshev.psi t)
          (hneg t ht))
  have he :=
    mul_le_mul_of_nonneg_left
      (by linarith only [(abs_le.mp (err a ⟨le_rfl, hab⟩)).2] :
        Chebyshev.psi a ≤ a + 81 / 100 * Real.sqrt a)
      hfa
  rw [abel]
  exact sub_le_sub (neg_le_neg he) hcomp

/-- The upper endpoint of the square recovery window stays within the certified
psi range for every radius in [465/2, 278], so the Abel lower bound applies
to any decreasing smooth weight vanishing there. -/
theorem square_window_abel_lower {r : ℝ} (hr : 465 / 2 ≤ r) (hr' : r ≤ 278) {f : ℝ → ℝ} (V : ℝ)
    (hV : V = Real.exp (21 / 16) * r) (hf : ∀ t ∈ Set.Icc r V, DifferentiableAt ℝ f t)
    (hd : ContinuousOn (deriv f) (Set.Icc r V)) (hn : ∀ t ∈ Set.Icc r V, deriv f t ≤ 0)
    (hfr : 0 ≤ f r) (hend : f V = 0) :
    -(f r * (r + 81 / 100 * Real.sqrt r)) -
        (∫ t in r..V, deriv f t * (t - 81 / 100 * Real.sqrt t)) ≤
      ∑ k ∈ Finset.Ioc ⌊r⌋₊ ⌊V⌋₊, f k * ArithmeticFunction.vonMangoldt k := by
  have h0 : 0 ≤ r := le_trans (by norm_num only : (0 : ℝ) ≤ 465 / 2) hr
  have he : Real.exp (21 / 16) ≤ 9 := by
    have ht := Real.exp_le_exp.mpr (by norm_num only : (21 / 16 : ℝ) ≤ 1 + 1)
    rw [Real.exp_add] at ht
    exact
      ht.trans (by nlinarith only [mul_self_lt_mul_self (Real.exp_pos 1).le Real.exp_one_lt_three])
  have hlo : r ≤ V := hV ▸ le_mul_of_one_le_left h0 (Real.one_le_exp (by norm_num only))
  have hhi : V ≤ 1000000 := by
    rw [hV]
    linarith only [mul_le_mul_of_nonneg_right he h0, hr']
  exact square_recovery_abel_lower (by linarith only [hr]) hlo hhi hf hd hn hfr hend

end PseudoPrime.PrimeTestBounds.MillerRabin
