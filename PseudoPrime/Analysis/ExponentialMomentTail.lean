/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogPowerTailIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Exponential moment tail integrals -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- At every nonzero rate, the tail polynomial has derivative equal to its rate times
the polynomial minus its leading monomial. This also applies to growing exponentials. -/
theorem log_power_tail_poly_deriv_ne {r : ℝ} (hr : r ≠ 0) (k : ℕ) (z : ℝ) :
    HasDerivAt (logPowerTailPoly r k) (r * logPowerTailPoly r k z - z ^ k) z := by
  induction k with
  | zero =>
    have h := hasDerivAt_const z (1 / r)
    convert h using 1
    · rfl
    · dsimp only [logPowerTailPoly]
      field_simp [hr]
      norm_num only
  | succ k
    ih =>
    have h :=
      (((hasDerivAt_id z).pow (k + 1)).div_const r).add (ih.const_mul (((k + 1 : ℕ) : ℝ) / r))
    apply h.congr_deriv
    dsimp only [logPowerTailPoly]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, id_eq]
    field_simp [hr]
    ring

/-- For every nonzero rate, the exponential times the tail polynomial is a primitive
of the corresponding exponential moment. It applies to both signs of the rate. -/
theorem exponential_moment_primitive_deriv {r : ℝ} (hr : r ≠ 0) (k : ℕ) (z : ℝ) :
    HasDerivAt (fun x : ℝ ↦ -Real.exp (-r * x) * logPowerTailPoly r k x) (z ^ k * Real.exp (-r * z))
      z := by
  have he := ((hasDerivAt_id z).const_mul (-r)).exp
  have hp := log_power_tail_poly_deriv_ne hr k z
  have h := he.neg.mul hp
  apply h.congr_deriv
  simp only [Pi.neg_apply, id_eq]
  ring

/-- At any nonzero rate, evaluate the exponential moment on a nonnegative finite interval.
The endpoint formula also covers growing exponentials. -/
theorem exponential_moment_interval_ne {r z : ℝ} (hr : r ≠ 0) (hz : 0 ≤ z) (k : ℕ) :
    (∫ v in Set.Ioc (0 : ℝ) z, v ^ k * Real.exp (-r * v)) =
      logPowerTailPoly r k 0 - Real.exp (-r * z) * logPowerTailPoly r k z := by
  have hi :
    IntervalIntegrable (fun v : ℝ ↦ v ^ k * Real.exp (-r * v)) MeasureTheory.volume 0 z := by
    exact
      ((continuous_id.pow k).mul
            (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable
        0 z
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v _ ↦ exponential_moment_primitive_deriv hr k v) hi
  rw [intervalIntegral.integral_of_le hz] at h
  simp only [mul_zero, Real.exp_zero, neg_one_mul] at h
  linarith only [h]

/-- For a positive decay rate and nonnegative lower endpoint, the tail of
an exponential moment is the corresponding logarithmic-tail polynomial times
the endpoint exponential. The logarithmic substitution reuses the existing
tail integral formula. -/
theorem exponential_moment_tail {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (k : ℕ) :
    (∫ v in Set.Ioi a, v ^ k * Real.exp (-r * v)) = Real.exp (-r * a) * logPowerTailPoly r k a := by
  have hsub :=
    MeasureTheory.integral_comp_log_Ioi (fun v : ℝ ↦ v ^ k * Real.exp (-r * v)) (Real.exp_pos a)
  have hlog : (1 : ℝ) ≤ Real.exp a := Real.one_le_exp_iff.mpr ha
  have htail := log_power_tail_integral hr hlog k
  have he :
    (∫ x in Set.Ioi (Real.exp a), x⁻¹ * (Real.log x ^ k * Real.exp (-r * Real.log x))) =
      ∫ x in Set.Ioi (Real.exp a), Real.log x ^ k * x ^ (-r - 1) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    have hx0 : 0 < x := (Real.exp_pos a).trans hx
    rw [show -r * Real.log x = Real.log x * (-r) by ring, ← Real.rpow_def_of_pos hx0, ←
      Real.rpow_neg_one]
    calc
      _ = Real.log x ^ k * (x ^ (-1 : ℝ) * x ^ (-r)) := by ring
      _ = _ := by
        have hexponent : (-1 : ℝ) + (-r) = -r - 1 := by ring
        rw [← Real.rpow_add hx0, hexponent]
  simp only [Real.log_exp, smul_eq_mul] at hsub
  rw [he, htail, Real.log_exp, Real.rpow_def_of_pos (Real.exp_pos a), Real.log_exp] at hsub
  have hexp : a * -r = -r * a := by ring
  rw [hexp] at hsub
  exact hsub.symm

/-- Every natural exponential moment with positive decay is integrable on
the positive half-line. This supplies the integrability needed to subtract
two tail integrals. -/
theorem exponential_moment_integrable {r : ℝ} (hr : 0 < r) (k : ℕ) :
    MeasureTheory.IntegrableOn (fun v : ℝ ↦ v ^ k * Real.exp (-r * v)) (Set.Ioi 0) := by
  have hs : (-1 : ℝ) < (k : ℝ) := by
    have h := Nat.cast_nonneg (α := ℝ) k
    linarith only [h]
  have h :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (s := (k : ℝ)) (p := 1) (b := r) hs (by norm_num only) hr
  change
    MeasureTheory.IntegrableOn (fun v : ℝ ↦ v ^ ((k : ℕ) : ℝ) * Real.exp (-r * v ^ (1 : ℝ))) _ at h
  simpa only [Real.rpow_natCast, Real.rpow_one] using h

/-- The exponential moment on `(0, z]` is the difference of the complete
moment and the tail at `z`. This finite-interval identity follows from the
tail formula and requires `z ≥ 0`. -/
theorem exponential_moment_interval {r z : ℝ} (hr : 0 < r) (hz : 0 ≤ z) (k : ℕ) :
    (∫ v in Set.Ioc (0 : ℝ) z, v ^ k * Real.exp (-r * v)) =
      logPowerTailPoly r k 0 - Real.exp (-r * z) * logPowerTailPoly r k z := by
  have hi := exponential_moment_integrable hr k
  have h := intervalIntegral.integral_Ioi_sub_Ioi hi hz
  rw [intervalIntegral.integral_of_le hz, exponential_moment_tail hr (le_refl 0) k,
    exponential_moment_tail hr hz k] at h
  norm_num only [mul_zero, neg_zero, Real.exp_zero, one_mul] at h
  exact h.symm

end PseudoPrime.Analysis
