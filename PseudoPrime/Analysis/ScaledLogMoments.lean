/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.MellinLogMoments
/-! # Logarithmic moments with exponential upper endpoint -/

public section

namespace PseudoPrime.Analysis
/-- For positive exponent parameter, logarithmic moments up to `exp a` are integrable
and equal `exp(a*s) n! / s^(n+1)`. Scale the unit-interval moment and track
both the real power and Jacobian exactly. -/
theorem scaled_log_moment (n : ℕ) (a : ℝ) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ u ^ (s - 1) * (a - Real.log u) ^ n)
      (Set.Ioc 0 (Real.exp a)) ∧
    (∫ u : ℝ in (0 : ℝ)..Real.exp a, u ^ (s - 1) * (a - Real.log u) ^ n) =
      Real.exp (a * s) * ((n.factorial : ℝ) / s ^ (n + 1)) := by
  let f : ℝ → ℝ := fun u ↦ u ^ (s - 1) * (-Real.log u) ^ n
  have hm := real_log_moment n hs
  have hf : IntervalIntegrable f MeasureTheory.volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr hm.1
  have hc : IntervalIntegrable (fun u ↦ f (u / Real.exp a)) MeasureTheory.volume
      0 (Real.exp a) := by
    have h := hf.comp_mul_left (c := (Real.exp a)⁻¹)
    simpa only [zero_div, one_div, inv_inv, inv_mul_eq_div] using h
  have he {u : ℝ} (hu : 0 < u) :
      u ^ (s - 1) * (a - Real.log u) ^ n =
        Real.exp (a * (s - 1)) * f (u / Real.exp a) := by
    dsimp only [f]
    rw [Real.log_div hu.ne' (Real.exp_ne_zero a), Real.log_exp,
      Real.div_rpow hu.le (Real.exp_pos a).le,
      Real.rpow_def_of_pos (Real.exp_pos a), Real.log_exp]
    rw [neg_sub]
    symm
    calc
      _ = (Real.exp (a * (s - 1)) * (Real.exp (a * (s - 1)))⁻¹) *
          (u ^ (s - 1) * (a - Real.log u) ^ n) := by ring
      _ = _ := by rw [mul_inv_cancel₀ (Real.exp_ne_zero _), one_mul]
  have hi : IntervalIntegrable
      (fun u : ℝ ↦ u ^ (s - 1) * (a - Real.log u) ^ n) MeasureTheory.volume
      0 (Real.exp a) := by
    apply IntervalIntegrable.congr ?_ (hc.const_mul (Real.exp (a * (s - 1))))
    intro u hu
    have hu' : u ∈ Set.Ioc 0 (Real.exp a) := by
      simpa only [Set.uIoc_of_le (Real.exp_pos a).le] using hu
    exact (he hu'.1).symm
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le (Real.exp_pos a).le).mp hi, ?_⟩
  have hcongr : (∫ u : ℝ in (0 : ℝ)..Real.exp a,
      u ^ (s - 1) * (a - Real.log u) ^ n) =
      ∫ u : ℝ in (0 : ℝ)..Real.exp a,
        Real.exp (a * (s - 1)) * f (u / Real.exp a) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with u hu
    have hu' : u ∈ Set.Ioc 0 (Real.exp a) := by
      simpa only [Set.uIoc_of_le (Real.exp_pos a).le] using hu
    exact he hu'.1
  rw [hcongr, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div f (Real.exp_ne_zero a), zero_div,
    div_self (Real.exp_ne_zero a)]
  have hmoment : (∫ u : ℝ in (0 : ℝ)..1, f u) =
      (n.factorial : ℝ) / s ^ (n + 1) := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact hm.2
  rw [hmoment]
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring
end PseudoPrime.Analysis
