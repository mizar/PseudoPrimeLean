/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFixedPowers632
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFixedPowers632

/-! # Radius-dependent recovery from the existing fixed prime powers -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem fixed_power_damped_mono632 :
    MonotoneOn (fun t : ℝ ↦ t ^ 5 * Real.exp (-(7 / 4) * t)) (Set.Icc 0 2.856) := by
  have hd (t : ℝ) := (hasDerivAt_pow 5 t).mul (((hasDerivAt_id t).const_mul (-(7 / 4 : ℝ))).exp)
  apply
    monotoneOn_of_deriv_nonneg (convex_Icc _ _) (fun x _ ↦ (hd x).continuousAt.continuousWithinAt)
      (fun x _ ↦ (hd x).differentiableAt.differentiableWithinAt)
  intro t ht
  obtain ⟨ht0, ht1⟩ := (interior_subset ht : t ∈ Set.Icc (0 : ℝ) 2.856)
  rw [(hd t).deriv]
  norm_num only [id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one]
  have hh :=
    mul_nonneg (mul_nonneg (pow_nonneg ht0 4) (Real.exp_pos (-(7 / 4) * t)).le)
      (show 0 ≤ 5 - (7 / 4 : ℝ) * t by linarith only [ht1])
  linear_combination hh

private theorem fixed_power_growth_kernel {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) (hw : w ≤ 2.856) :
    Real.exp ((3 / 4) * (w - v)) * (v ^ 5 * Real.exp (-v)) ≤ w ^ 5 * Real.exp (-w) := by
  have h := fixed_power_damped_mono632 ⟨hv, hvw.trans hw⟩ ⟨hv.trans hvw, hw⟩ hvw
  have h' := mul_le_mul_of_nonneg_left h (Real.exp_pos ((3 / 4) * w)).le
  dsimp only at h'
  have hEq (t : ℝ) :
    Real.exp (3 / 4 * w) * Real.exp (-(7 / 4) * t) =
      Real.exp (3 / 4 * (w - t)) * Real.exp (-t) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simpa only [mul_left_comm, hEq, sub_self, mul_zero, Real.exp_zero, one_mul] using h'

private theorem fixed_power_term_growth632 {r : ℝ} (hr : r ∈ Set.Icc 313 316) {m : ℕ}
    (hm : m ∈ powerIndices632) :
    Real.exp (1.53 * (Real.log r - Real.log 313)) *
        (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) (313 ^ 2) m).re ≤
      (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) m).re := by
  obtain ⟨hlo, hhi, _⟩ := power_data632 m hm
  have hr0 : 0 < r := by linarith only [hr.1]
  have hm0 : 0 < m := (by decide : 0 < 316 ^ 2).trans hlo
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm0
  have hs : Real.log ((m : ℝ) / (313 : ℝ) ^ 2) ≤ 14 / 5 := by
    have hb : (m : ℝ) / (313 : ℝ) ^ 2 ≤ (2 : ℝ) ^ 4 :=
      (div_le_iff₀ (by norm_num only)).mpr (by exact_mod_cast hhi)
    have h := Real.log_le_log (div_pos hmR (by norm_num only)) hb
    rw [Real.log_pow, Nat.cast_ofNat] at h
    linarith only [h, Real.log_two_lt_d9]
  have hmr : r ^ 2 ≤ (m : ℝ) := (pow_le_pow_left₀ hr0.le hr.2 2).trans (by exact_mod_cast hlo.le)
  have hl := Real.log_nonneg ((one_le_div (sq_pos_of_pos hr0)).mpr hmr)
  have hd : Real.log ((m : ℝ) / r ^ 2) ≤ Real.log ((m : ℝ) / (313 : ℝ) ^ 2) :=
    Real.log_le_log (div_pos hmR (sq_pos_of_pos hr0))
      (div_le_div_of_nonneg_left hmR.le (by norm_num only)
        (pow_le_pow_left₀ (by norm_num only) hr.1 2))
  rw [quarter_summand_570 (by norm_num only) hm0 hs,
    quarter_summand_570 (sq_pos_of_pos hr0) hm0 (hd.trans hs)]
  unfold quarterWeight570
  dsimp only
  let v := (2 * (7 / 5) - Real.log ((m : ℝ) / (313 : ℝ) ^ 2)) / (2 * (25 / 51))
  let w := (2 * (7 / 5) - Real.log ((m : ℝ) / r ^ 2)) / (2 * (25 / 51))
  have h :=
    fixed_power_growth_kernel (v := v) (w := w)
      (by
        dsimp only [v]; norm_num only at hs ⊢; linarith only [hs])
      (by
        dsimp only [v, w]; norm_num only at hd ⊢; linarith only [hd])
      (by
        dsimp only [w]; norm_num only at ⊢; linarith only [hl])
  have he : (3 / 4) * (w - v) = 1.53 * (Real.log r - Real.log 313) := by
    dsimp only [v, w]
    rw [Real.log_div hmR.ne' (sq_pos_of_pos hr0).ne', Real.log_div hmR.ne' (by norm_num only),
      Real.log_pow, Real.log_pow, Nat.cast_ofNat]
    ring
  rw [he] at h
  change
    _ * ((1 / Real.sqrt m) * (v ^ 5 * Real.exp (-v) / 120) * ArithmeticFunction.vonMangoldt m) ≤
      (1 / Real.sqrt m) * (w ^ 5 * Real.exp (-w) / 120) * ArithmeticFunction.vonMangoldt m
  linear_combination (1 / Real.sqrt m * ArithmeticFunction.vonMangoldt m / 120) * h

/-- The certified recovery at radius 313 increases at an explicit linear rate.
The same prime powers and the same finite sum certificate are used throughout. -/
theorem fixed_power_gain_growth_632 {r : ℝ} (hr : r ∈ Set.Icc 313 316) :
    0.1448 * (1 + 1.53 * ((r - 313) / 316)) < fixedPowerGain632 r := by
  have hr0 : 0 < r := by linarith only [hr.1]
  have h := Real.log_le_sub_one_of_pos (div_pos (by norm_num only : (0 : ℝ) < 313) hr0)
  rw [Real.log_div (by norm_num only) hr0.ne'] at h
  have hd := div_le_div_of_nonneg_left (sub_nonneg.mpr hr.1) hr0 hr.2
  rw [sub_div r 313 r, div_self hr0.ne'] at hd
  have hl : (r - 313) / 316 ≤ Real.log r - Real.log 313 := by linarith only [h, hd]
  have hE :=
    (Real.add_one_le_exp _).trans
      (Real.exp_le_exp.mpr
        (show 1.53 * ((r - 313) / 316) ≤ 1.53 * (Real.log r - Real.log 313) by linarith only [hl]))
  have hm := fixed_power_gain_lower_632 (r := 313) (by norm_num only [Set.mem_Icc, and_self])
  have hg :
    Real.exp (1.53 * (Real.log r - Real.log 313)) * fixedPowerGain632 313 ≤
      fixedPowerGain632 r := by
    unfold fixedPowerGain632
    rw [mul_left_comm, Finset.mul_sum]
    exact
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun _ hk ↦ fixed_power_term_growth632 hr hk))
        (by norm_num only)
  have hbound := mul_le_mul_of_nonneg_left hE (by norm_num only : (0 : ℝ) ≤ 0.1448)
  rw [mul_comm (0.1448 : ℝ) (Real.exp _)] at hbound
  rw [add_comm (1 : ℝ)]
  exact hbound.trans_lt ((mul_lt_mul_of_pos_left hm (Real.exp_pos _)).trans_le hg)

end PseudoPrime.PrimeTestBounds.MillerRabin
