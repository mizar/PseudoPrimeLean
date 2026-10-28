/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.TriangularCutoffVariation
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.Chebyshev

/-! # Abel identity for the alpha-18 cutoff weight -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- On a positive compact interval, the finite weighted Mangoldt sum equals
its Chebyshev boundary terms minus the explicit derivative integral.
Apply Abel summation; this supplies the identity for the cutoff error estimate. -/
theorem triangular18_cutoff_mangoldt_abel {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
        ((36 + Real.log k) * (k : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt k =
      ((36 + Real.log b) * b ^ (-1 / 2 : ℝ)) * Chebyshev.psi b -
        ((36 + Real.log a) * a ^ (-1 / 2 : ℝ)) * Chebyshev.psi a -
        ∫ t in Set.Ioc a b, (t ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log t) / 2)) * Chebyshev.psi t := by
  let f := fun t : ℝ ↦ (36 + Real.log t) * t ^ (-1 / 2 : ℝ)
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) :=
    triangular18_cutoff_weight_deriv (lt_of_lt_of_le ha ht.1)
  have he :
    Set.EqOn (deriv f) (fun t : ℝ ↦ t ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log t) / 2)) (Set.Icc a b) :=
    fun t ht ↦ (hd t ht).deriv
  have hc :
    ContinuousOn (fun t : ℝ ↦ t ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log t) / 2)) (Set.Icc a b) := by
    intro t ht
    have hp := lt_of_lt_of_le ha ht.1
    exact
      ((Real.continuousAt_rpow_const t (-3 / 2) (Or.inl hp.ne')).mul
          (continuousAt_const.sub
            ((continuousAt_const.add (Real.continuousAt_log hp.ne')).div_const
              2))).continuousWithinAt
  have hi : MeasureTheory.IntegrableOn (deriv f) (Set.Icc a b) := (hc.congr he).integrableOn_Icc
  have h :=
    sum_mul_eq_sub_sub_integral_mul ArithmeticFunction.vonMangoldt ha.le hab
      (fun t ht ↦ (hd t ht).differentiableAt) hi
  simp only [← Chebyshev.psi_eq_sum_Icc] at h
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      (fun t ht ↦ congrArg (fun z : ℝ ↦ z * Chebyshev.psi t) (he ⟨ht.1.le, ht.2⟩))] at h
  exact h

/-- At positive scale and input, the rescaled cutoff weight has the stated derivative.
The chain rule provides the factor inverse to the scale. Used in finite Abel summation. -/
theorem triangular18_cutoff_scaled_weight_deriv {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    HasDerivAt (fun z : ℝ ↦ (36 + Real.log (z / x)) * (z / x) ^ (-1 / 2 : ℝ))
      (((t / x) ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log (t / x)) / 2)) / x) t := by
  have h :=
    (triangular18_cutoff_weight_deriv (div_pos ht hx)).comp t ((hasDerivAt_id t).div_const x)
  simpa only [Function.comp_def, id_eq, mul_one_div] using h

/-- For positive scale and interval, the rescaled finite Mangoldt sum equals
its Chebyshev boundary terms minus the derivative integral.
Apply Abel summation and the scaled derivative; this is the cutoff error interface. -/
theorem triangular18_cutoff_scaled_mangoldt_abel {x a b : ℝ} (hx : 0 < x) (ha : 0 < a)
    (hab : a ≤ b) :
    ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
        ((36 + Real.log ((k : ℝ) / x)) * ((k : ℝ) / x) ^ (-1 / 2 : ℝ)) *
          ArithmeticFunction.vonMangoldt k =
      ((36 + Real.log (b / x)) * (b / x) ^ (-1 / 2 : ℝ)) * Chebyshev.psi b -
        ((36 + Real.log (a / x)) * (a / x) ^ (-1 / 2 : ℝ)) * Chebyshev.psi a -
        ∫ t in Set.Ioc a b,
          (((t / x) ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log (t / x)) / 2)) / x) * Chebyshev.psi t := by
  let f := fun t : ℝ ↦ (36 + Real.log (t / x)) * (t / x) ^ (-1 / 2 : ℝ)
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) :=
    triangular18_cutoff_scaled_weight_deriv hx (lt_of_lt_of_le ha ht.1)
  have he :
    Set.EqOn (deriv f)
      (fun t : ℝ ↦ ((t / x) ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log (t / x)) / 2)) / x)
      (Set.Icc a b) :=
    fun t ht ↦ (hd t ht).deriv
  have hc :
    ContinuousOn (fun t : ℝ ↦ ((t / x) ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log (t / x)) / 2)) / x)
      (Set.Icc a b) := by
    intro t ht
    have hp := div_pos (lt_of_lt_of_le ha ht.1) hx
    exact
      (((Real.continuousAt_rpow_const (t / x) (-3 / 2) (Or.inl hp.ne')).comp (f := fun z : ℝ ↦
                  z / x) (x := t)
                  (show ContinuousAt (fun z : ℝ ↦ z / x) t from continuousAt_id.div_const x)).mul
              (continuousAt_const.sub
                ((continuousAt_const.add
                      ((Real.continuousAt_log hp.ne').comp (f := fun z : ℝ ↦ z / x) (x := t)
                        (show ContinuousAt (fun z : ℝ ↦ z / x) t from
                          continuousAt_id.div_const x))).div_const
                  2))).div_const
          x |>.continuousWithinAt
  have hi : MeasureTheory.IntegrableOn (deriv f) (Set.Icc a b) := (hc.congr he).integrableOn_Icc
  have h :=
    sum_mul_eq_sub_sub_integral_mul ArithmeticFunction.vonMangoldt ha.le hab
      (fun t ht ↦ (hd t ht).differentiableAt) hi
  simp only [← Chebyshev.psi_eq_sum_Icc] at h
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      (fun t ht ↦ congrArg (fun z : ℝ ↦ z * Chebyshev.psi t) (he ⟨ht.1.le, ht.2⟩))] at h
  exact h

/-- At positive scale the cutoff lower endpoint vanishes, leaving the upper
Chebyshev boundary term and explicit derivative integral in the finite Mangoldt sum. -/
theorem triangular18_cutoff_mangoldt_boundary {x : ℝ} (hx : 0 < x) :
    ∑ k ∈ Finset.Ioc ⌊Real.exp (-36) * x⌋₊ ⌊x⌋₊,
        ((36 + Real.log ((k : ℝ) / x)) * ((k : ℝ) / x) ^ (-1 / 2 : ℝ)) *
          ArithmeticFunction.vonMangoldt k =
      36 * Chebyshev.psi x -
        ∫ t in Set.Ioc (Real.exp (-36) * x) x,
          (((t / x) ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log (t / x)) / 2)) / x) * Chebyshev.psi t := by
  have ha := mul_pos (Real.exp_pos (-36)) hx
  have he : Real.exp (-36 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num only)
  have hab : Real.exp (-36) * x ≤ x := (mul_le_mul_of_nonneg_right he hx.le).trans_eq (one_mul x)
  have h := triangular18_cutoff_scaled_mangoldt_abel hx ha hab
  rw [div_self hx.ne', Real.log_one, Real.one_rpow, mul_div_cancel_right₀ _ hx.ne',
    triangular18_cutoff_lower_endpoint] at h
  norm_num only [add_zero, mul_one, zero_mul, sub_zero] at h
  simpa only [neg_div] using h

/-- At positive scale, the weighted derivative integral is at most
76 times the three-quarter power of the scale. Substitute the ratio to the scale;
this is the integral budget used for the RH Chebyshev error. -/
theorem triangular18_cutoff_scaled_variation_le {x : ℝ} (hx : 0 < x) :
    (∫ t in (Real.exp (-36) * x)..x,
        |((t / x) ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log (t / x)) / 2)) / x| * t ^ (3 / 4 : ℝ)) ≤
      76 * x ^ (3 / 4 : ℝ) := by
  let g := fun u : ℝ ↦ |u ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log u) / 2)| * u ^ (3 / 4 : ℝ)
  have he (t : ℝ) (ht : t ∈ Set.uIcc (Real.exp (-36) * x) x) :
    |((t / x) ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log (t / x)) / 2)) / x| * t ^ (3 / 4 : ℝ) =
      (x ^ (3 / 4 : ℝ) / x) * g (t / x) := by
    have he0 : Real.exp (-36 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num only)
    have hab : Real.exp (-36) * x ≤ x := (mul_le_mul_of_nonneg_right he0 hx.le).trans_eq (one_mul x)
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : 0 ≤ t := (mul_pos (Real.exp_pos _) hx).le.trans ht.1
    have hp := Real.div_rpow ht0 hx.le (3 / 4)
    rw [abs_div, abs_of_pos hx]
    dsimp only [g]
    rw [hp]
    field_simp [hx.ne', (Real.rpow_pos_of_pos hx (3 / 4)).ne']
  rw [intervalIntegral.integral_congr he, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div g hx.ne', mul_div_cancel_right₀ _ hx.ne', div_self hx.ne',
    smul_eq_mul]
  have hv := triangular18_cutoff_original_variation_le
  have hh := mul_le_mul_of_nonneg_left hv (Real.rpow_nonneg hx.le (3 / 4))
  dsimp only [g] at *
  rw [← mul_assoc, div_mul_cancel₀ _ hx.ne']
  simpa only [mul_comm] using hh

/-- A Chebyshev error bounded by C times the three-quarter power gives
an integrated cutoff derivative error at most 76 C times that power of the scale.
The proof uses an integrable majorant and the scaled variation bound. -/
theorem triangular18_cutoff_psi_error_integral_le {x C : ℝ} (hx : 0 < x)
    (hpsi : ∀ t : ℝ, 0 ≤ t → |Chebyshev.psi t - t| ≤ C * t ^ (3 / 4 : ℝ)) :
    |∫ t in (Real.exp (-36) * x)..x,
          (((t / x) ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log (t / x)) / 2)) / x) *
            (Chebyshev.psi t - t)| ≤
      C * (76 * x ^ (3 / 4 : ℝ)) := by
  let d := fun t : ℝ ↦ ((t / x) ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log (t / x)) / 2)) / x
  have ha := mul_pos (Real.exp_pos (-36)) hx
  have he : Real.exp (-36 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num only)
  have hab : Real.exp (-36) * x ≤ x := (mul_le_mul_of_nonneg_right he hx.le).trans_eq (one_mul x)
  have hC : 0 ≤ C := by
    have h := hpsi 1 (by norm_num only)
    norm_num only [Real.one_rpow, mul_one] at h
    exact (abs_nonneg _).trans h
  have hc :
    ContinuousOn (fun t : ℝ ↦ C * (|d t| * t ^ (3 / 4 : ℝ))) (Set.uIcc (Real.exp (-36) * x) x) := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    have ht0 := lt_of_lt_of_le ha ht.1
    have hp := div_pos ht0 hx
    have hr :=
      (Real.continuousAt_rpow_const (t / x) (-3 / 2) (Or.inl hp.ne')).comp (f := fun z : ℝ ↦ z / x)
        (x := t) (continuousAt_id.div_const x)
    have hl :=
      (Real.continuousAt_log hp.ne').comp (f := fun z : ℝ ↦ z / x) (x := t)
        (continuousAt_id.div_const x)
    have hd : ContinuousAt d t :=
      (hr.mul (continuousAt_const.sub ((continuousAt_const.add hl).div_const 2))).div_const x
    exact
      (continuousAt_const.mul
          (hd.abs.mul (Real.continuousAt_rpow_const t (3 / 4) (Or.inl ht0.ne')))).continuousWithinAt
  have hb :=
    intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) hab (f := fun t : ℝ ↦
      d t * (Chebyshev.psi t - t))
      (Filter.Eventually.of_forall
        (fun t ht ↦ by
          rw [Real.norm_eq_abs, abs_mul]
          have ht0 : 0 ≤ t := ha.le.trans ht.1.le
          have h := mul_le_mul_of_nonneg_left (hpsi t ht0) (abs_nonneg (d t))
          simpa only [mul_assoc, mul_comm, mul_left_comm] using h))
      hc.intervalIntegrable
  rw [intervalIntegral.integral_const_mul, Real.norm_eq_abs] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (triangular18_cutoff_scaled_variation_le hx) hC)

/-- Under a Chebyshev error constant 13, the upper boundary error minus
the cutoff derivative error integral has absolute value at most 1456 times
the three-quarter power of the positive scale. Combine budgets 36 and 76;
this controls the Abel error before evaluating the main-term integral. -/
theorem triangular18_cutoff_psi_boundary_error_le {x : ℝ} (hx : 0 < x)
    (hpsi : ∀ t : ℝ, 0 ≤ t → |Chebyshev.psi t - t| ≤ 13 * t ^ (3 / 4 : ℝ)) :
    |36 * (Chebyshev.psi x - x) -
          ∫ t in (Real.exp (-36) * x)..x,
            (((t / x) ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log (t / x)) / 2)) / x) *
              (Chebyshev.psi t - t)| ≤
      1456 * x ^ (3 / 4 : ℝ) := by
  have hi := triangular18_cutoff_psi_error_integral_le hx hpsi
  have he := mul_le_mul_of_nonneg_left (hpsi x hx.le) (by norm_num only : (0 : ℝ) ≤ 36)
  have ht :=
    abs_sub (36 * (Chebyshev.psi x - x))
      (∫ t in (Real.exp (-36) * x)..x,
        (((t / x) ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log (t / x)) / 2)) / x) * (Chebyshev.psi t - t))
  rw [abs_mul, show |(36 : ℝ)| = 36 by norm_num only] at ht
  linarith only [hi, he, ht]

/-- A Chebyshev error constant 13 bounds the difference between the finite
cutoff Mangoldt sum and its Abel main term by 1456 times the scale to power 3/4.
The proof checks integrability before separating the Chebyshev error integral. -/
theorem triangular18_cutoff_mangoldt_error_le {x : ℝ} (hx : 0 < x)
    (hpsi : ∀ t : ℝ, 0 ≤ t → |Chebyshev.psi t - t| ≤ 13 * t ^ (3 / 4 : ℝ)) :
    |(∑ k ∈ Finset.Ioc ⌊Real.exp (-36) * x⌋₊ ⌊x⌋₊,
            ((36 + Real.log ((k : ℝ) / x)) * ((k : ℝ) / x) ^ (-1 / 2 : ℝ)) *
              ArithmeticFunction.vonMangoldt k) -
          (36 * x -
            ∫ t in (Real.exp (-36) * x)..x,
              (((t / x) ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log (t / x)) / 2)) / x) * t)| ≤
      1456 * x ^ (3 / 4 : ℝ) := by
  let a := Real.exp (-36) * x
  let d := fun t : ℝ ↦ ((t / x) ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log (t / x)) / 2)) / x
  have ha : 0 < a := mul_pos (Real.exp_pos _) hx
  have he : Real.exp (-36 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num only)
  have hab : a ≤ x := (mul_le_mul_of_nonneg_right he hx.le).trans_eq (one_mul x)
  have hc : ContinuousOn d (Set.Icc a x) := by
    intro t ht
    have hp := div_pos (lt_of_lt_of_le ha ht.1) hx
    have hr :=
      (Real.continuousAt_rpow_const (t / x) (-3 / 2) (Or.inl hp.ne')).comp (f := fun z : ℝ ↦ z / x)
        (x := t) (continuousAt_id.div_const x)
    have hl :=
      (Real.continuousAt_log hp.ne').comp (f := fun z : ℝ ↦ z / x) (x := t)
        (continuousAt_id.div_const x)
    exact
      ((hr.mul (continuousAt_const.sub ((continuousAt_const.add hl).div_const 2))).div_const
          x).continuousWithinAt
  have hi : MeasureTheory.IntegrableOn (fun t ↦ d t * Chebyshev.psi t) (Set.Ioc a x) := by
    have h :=
      integrableOn_mul_sum_Icc ArithmeticFunction.vonMangoldt (m := 0) ha.le hc.integrableOn_Icc
    simp only [← Chebyshev.psi_eq_sum_Icc] at h
    exact h.mono_set Set.Ioc_subset_Icc_self
  have hj : MeasureTheory.IntegrableOn (fun t ↦ d t * t) (Set.Ioc a x) :=
    (hc.mul continuousOn_id).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hsub :
    (∫ t in a..x, d t * (Chebyshev.psi t - t)) =
      (∫ t in a..x, d t * Chebyshev.psi t) - ∫ t in a..x, d t * t := by
    simp only [mul_sub]
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_of_le hab, MeasureTheory.integral_sub hi hj]
  have h := triangular18_cutoff_psi_boundary_error_le hx hpsi
  change |36 * (Chebyshev.psi x - x) - ∫ t in a..x, d t * (Chebyshev.psi t - t)| ≤ _ at h
  rw [hsub] at h
  rw [triangular18_cutoff_mangoldt_boundary hx, ← intervalIntegral.integral_of_le hab]
  change
    |(36 * Chebyshev.psi x - ∫ t in a..x, d t * Chebyshev.psi t) -
          (36 * x - ∫ t in a..x, d t * t)| ≤
      _
  convert h using 1
  congr 1
  ring

end PseudoPrime.Analysis
