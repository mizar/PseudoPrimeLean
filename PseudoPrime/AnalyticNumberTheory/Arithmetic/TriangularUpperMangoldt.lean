/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.TriangularUpperVariation
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.Chebyshev

/-! # Upper-support alpha-18 Mangoldt Abel identities -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- At positive scale and input, the upper-support weight has the stated
derivative. Apply the chain rule to the unscaled weight. -/
theorem triangular18_upper_scaled_weight_deriv {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    HasDerivAt (fun z : ℝ ↦ (36 - Real.log (z / x)) * (z / x) ^ (-1 / 2 : ℝ))
      (((t / x) ^ (-3 / 2 : ℝ) * (Real.log (t / x) / 2 - 19)) / x) t := by
  have h := (triangular18_upper_weight_deriv (div_pos ht hx)).comp t ((hasDerivAt_id t).div_const x)
  simpa only [Function.comp_def, id_eq, mul_one_div] using h

/-- At positive scale on a positive interval, the finite upper-weight
Mangoldt sum equals its Chebyshev endpoints minus the derivative integral.
Check derivative integrability and apply Abel summation. -/
theorem triangular18_upper_scaled_mangoldt_abel {x a b : ℝ} (hx : 0 < x) (ha : 0 < a)
    (hab : a ≤ b) :
    ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
        ((36 - Real.log ((k : ℝ) / x)) * ((k : ℝ) / x) ^ (-1 / 2 : ℝ)) *
          ArithmeticFunction.vonMangoldt k =
      ((36 - Real.log (b / x)) * (b / x) ^ (-1 / 2 : ℝ)) * Chebyshev.psi b -
        ((36 - Real.log (a / x)) * (a / x) ^ (-1 / 2 : ℝ)) * Chebyshev.psi a -
        ∫ t in Set.Ioc a b,
          (((t / x) ^ (-3 / 2 : ℝ) * (Real.log (t / x) / 2 - 19)) / x) * Chebyshev.psi t := by
  let f := fun t : ℝ ↦ (36 - Real.log (t / x)) * (t / x) ^ (-1 / 2 : ℝ)
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) :=
    triangular18_upper_scaled_weight_deriv hx (lt_of_lt_of_le ha ht.1)
  have he :
    Set.EqOn (deriv f) (fun t : ℝ ↦ ((t / x) ^ (-3 / 2 : ℝ) * (Real.log (t / x) / 2 - 19)) / x)
      (Set.Icc a b) :=
    fun t ht ↦ (hd t ht).deriv
  have hc :
    ContinuousOn (fun t : ℝ ↦ ((t / x) ^ (-3 / 2 : ℝ) * (Real.log (t / x) / 2 - 19)) / x)
      (Set.Icc a b) := by
    intro t ht
    have hp := div_pos (lt_of_lt_of_le ha ht.1) hx
    have hr :=
      (Real.continuousAt_rpow_const (t / x) (-3 / 2) (Or.inl hp.ne')).comp (f := fun z : ℝ ↦ z / x)
        (x := t) (continuousAt_id.div_const x)
    have hl :=
      (Real.continuousAt_log hp.ne').comp (f := fun z : ℝ ↦ z / x) (x := t)
        (continuousAt_id.div_const x)
    exact ((hr.mul ((hl.div_const 2).sub continuousAt_const)).div_const x).continuousWithinAt
  have hi : MeasureTheory.IntegrableOn (deriv f) (Set.Icc a b) := (hc.congr he).integrableOn_Icc
  have h :=
    sum_mul_eq_sub_sub_integral_mul ArithmeticFunction.vonMangoldt ha.le hab
      (fun t ht ↦ (hd t ht).differentiableAt) hi
  simp only [← Chebyshev.psi_eq_sum_Icc] at h
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      (fun t ht ↦ congrArg (fun z : ℝ ↦ z * Chebyshev.psi t) (he ⟨ht.1.le, ht.2⟩))] at h
  exact h

/-- At positive scale, the finite upper-support Mangoldt sum has zero upper
boundary term and lower boundary -36 psi(x). Specialize the scaled Abel identity.
Together with the lower branch, its boundary error cancels at the shared endpoint. -/
theorem triangular18_upper_mangoldt_boundary {x : ℝ} (hx : 0 < x) :
    ∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊Real.exp 36 * x⌋₊,
        ((36 - Real.log ((k : ℝ) / x)) * ((k : ℝ) / x) ^ (-1 / 2 : ℝ)) *
          ArithmeticFunction.vonMangoldt k =
      -36 * Chebyshev.psi x -
        ∫ t in Set.Ioc x (Real.exp 36 * x),
          (((t / x) ^ (-3 / 2 : ℝ) * (Real.log (t / x) / 2 - 19)) / x) * Chebyshev.psi t := by
  have he : (1 : ℝ) ≤ Real.exp 36 := Real.one_le_exp_iff.mpr (by norm_num only)
  have hab : x ≤ Real.exp 36 * x := (one_mul x).symm.trans_le (mul_le_mul_of_nonneg_right he hx.le)
  have h := triangular18_upper_scaled_mangoldt_abel hx hx hab
  rw [div_self hx.ne', Real.log_one, Real.one_rpow, mul_div_cancel_right₀ _ hx.ne',
    Real.log_exp] at h
  norm_num only [sub_self, sub_zero, mul_one, zero_mul, zero_sub] at h
  simpa only [neg_div, neg_mul] using h

end PseudoPrime.Analysis
