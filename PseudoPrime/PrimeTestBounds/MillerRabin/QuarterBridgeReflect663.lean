/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterBroadComparison656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterBroadComparison656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflected570

/-! # Principal reflection on the quarter-square bridge -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private noncomputable def bridgeReflectCoeff (j : ℕ) : ℝ :=
  if j = 0 then 579389
  else if j = 1 then 192278 else if j = 2 then 24616 else if j = 3 then 1445 else 26

private theorem bridge_reflect_poly {w : ℝ} (h₀ : 0 ≤ w) (h₈ : w ≤ 8) :
    (∑ j ∈ Finset.range 5, bridgeReflectCoeff j * w ^ j) ≤ (14.21 + w) ^ 5 * (1 - w / 50) := by
  have h4 : 0 ≤ w ^ 4 := pow_nonneg h₀ _
  have h5 := mul_le_mul_of_nonneg_right h₈ h4
  have h6 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h₀ h₈ 2) h4
  norm_num only [bridgeReflectCoeff, Finset.sum_range_succ, Finset.sum_range_zero, pow_zero,
    pow_one, ite_eq_left, ite_eq_right]
  nlinarith only [h₀, h4, h5, h6, pow_nonneg h₀ 2, pow_nonneg h₀ 3]

private theorem bridge_reflect_atom {z : ℝ} (hz : 14.21 ≤ z) {n : ℕ} (hn : n ∈ Finset.Ioc 0 2701) :
    (∑ j ∈ Finset.range 5, bridgeReflectCoeff j * quarterMangoldtMoment j n) ≤
      ArithmeticFunction.vonMangoldt n * ((z + Real.log n) ^ 5 / (n : ℝ) ^ (8 / 5 : ℝ)) := by
  let w := Real.log n
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr (Finset.mem_Ioc.mp hn).1
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 2701) (j := 12) (n := 24) (lo := 7) (hi := 8)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat] at hlog
  have hw₀ : 0 ≤ w := Real.log_natCast_nonneg n
  have hw₈ : w ≤ 8 := (Real.log_le_log hn₀ (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2)).trans hlog
  have he : 1 - w / 50 ≤ (n : ℝ) ^ (-(1 / 50) : ℝ) := by
    rw [Real.rpow_def_of_pos hn₀]
    linarith only [Real.add_one_le_exp (w * -(1 / 50 : ℝ))]
  have hp := pow_le_pow_left₀ (by linarith only [hw₀] : 0 ≤ 14.21 + w) (add_le_add hz (le_refl w)) 5
  have hh :=
    (bridge_reflect_poly hw₀ hw₈).trans
      (mul_le_mul hp he (by linarith only [hw₈]) (pow_nonneg (by linarith only [hz, hw₀]) 5))
  -- Separate the two inverse powers, then collect their exponents.
  have hpow :
    (n : ℝ) ^ (-(1 / 50) : ℝ) * (n : ℝ) ^ (-(79 / 50) : ℝ) = ((n : ℝ) ^ (8 / 5 : ℝ))⁻¹ := by
    rw [← Real.rpow_add hn₀, show -(1 / 50 : ℝ) + -(79 / 50 : ℝ) = -(8 / 5 : ℝ) by norm_num only,
      Real.rpow_neg hn₀.le]
  calc
    _ =
        (∑ j ∈ Finset.range 5, bridgeReflectCoeff j * w ^ j) *
          (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(79 / 50) : ℝ)) :=
      by
      rw [Finset.sum_mul]
      exact
        Finset.sum_congr rfl fun j _ ↦ by
          unfold quarterMangoldtMoment; dsimp only [w]; ring
    _ ≤
        (z + w) ^ 5 * (n : ℝ) ^ (-(1 / 50) : ℝ) *
          (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(79 / 50) : ℝ)) :=
      mul_le_mul_of_nonneg_right hh
        (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg hn₀.le _))
    _ = _ := by
      rw [show
          (z + w) ^ 5 * (n : ℝ) ^ (-(1 / 50) : ℝ) *
              (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(79 / 50) : ℝ)) =
            ArithmeticFunction.vonMangoldt n * (z + w) ^ 5 *
              ((n : ℝ) ^ (-(1 / 50) : ℝ) * (n : ℝ) ^ (-(79 / 50) : ℝ))
          by ring,
        hpow]
      dsimp only [w]
      ring

private theorem bridge_reflect_moment_lower {z : ℝ} (hz : 14.21 ≤ z) :
    1485000 ≤
      ∑ n ∈ Finset.Ioc 0 2701,
        ArithmeticFunction.vonMangoldt n * ((z + Real.log n) ^ 5 / (n : ℝ) ^ (8 / 5 : ℝ)) := by
  refine le_trans ?_ (Finset.sum_le_sum fun _ hn ↦ bridge_reflect_atom hz hn)
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  refine
    le_trans ?_
      (Finset.sum_le_sum fun j hj ↦
        mul_le_mul_of_nonneg_left (moment_floor j ((Finset.mem_range.mp hj).le))
          (by
            unfold bridgeReflectCoeff; split_ifs <;> norm_num only))
  norm_num only [bridgeReflectCoeff, momentFloor570, Finset.sum_range_succ, Finset.sum_range_zero,
    ite_eq_right, ite_eq_left]

private theorem bridge_reflect_geometry {r : ℝ} (hr : r ∈ Set.Icc 328 (663 / 2)) :
    14.21 ≤ 21 / 8 + Real.log (r ^ 2) ∧
      0.000000158 ≤ Real.exp (-(11 / 10) * (21 / 8 + Real.log (r ^ 2))) := by
  have h₀ := (by norm_num only : (0 : ℝ) < 328).trans_le hr.1
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 27) (lo := 5.793) (hi := 6)
        (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 663 / 2) (j := 9) (n := 27) (lo := 5) (hi :=
        5.80363) (by decide +kernel)).2
  have he :=
    (Analysis.rationalLogIntervalCheck_sound (N := 500000000 / 79) (j := 23) (n := 32) (lo :=
        15.659) (hi := 16) (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_ofScientific] at hl hu he
  have hz : 14.21 ≤ 21 / 8 + Real.log (r ^ 2) := by
    rw [Real.log_pow]
    linarith only [hl, Real.log_le_log (by norm_num only : (0 : ℝ) < 328) hr.1]
  have hd : 0.000000158 ≤ Real.exp (-(11 / 10) * (21 / 8 + Real.log (r ^ 2))) := by
    apply (Real.log_le_iff_le_exp (by norm_num only)).mp
    have hi : Real.log (0.000000158 : ℝ)⁻¹ ≥ 15.659 := by
      norm_num only at he ⊢; exact he
    rw [Real.log_inv] at hi
    rw [Real.log_pow]
    linarith only [hi, hu, Real.log_le_log h₀ hr.2]
  exact ⟨hz, hd⟩

/-- The prefix through 2701 gives a uniform lower bound for three copies
of the principal reflected Euler series on the bridge. -/
theorem quarter_bridge_reflect_credit {r : ℝ} (hr : r ∈ Set.Icc 328 (663 / 2)) :
    0.009446 ≤ 3 * quarterMainEuler656 (1 : DirichletCharacter ℂ 1) (r ^ 2) := by
  have hx : 1 ≤ r ^ 2 := one_le_pow₀ ((by norm_num only : (1 : ℝ) ≤ 328).trans hr.1)
  obtain ⟨hz, hd⟩ := bridge_reflect_geometry hr
  have h := principal_reflect_prefix_656 hx
  have hprod :=
    mul_le_mul hd (bridge_reflect_moment_lower hz) (by norm_num only : (0 : ℝ) ≤ 1485000)
      (Real.exp_pos _).le
  rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hx)] at h
  rw [show
      -(11 / 10 : ℝ) * (21 / 8 + Real.log (r ^ 2)) =
        -(11 / 10) * (21 / 8) + Real.log (r ^ 2) * -(11 / 10)
      by ring,
    Real.exp_add] at hprod
  nlinarith only [h, hprod]

/-- The weight at the lower endpoint stays above 0.001228 on the bridge. -/
theorem quarter_bridge_weight_one_lower {r : ℝ} (hr : r ∈ Set.Icc 328 (663 / 2)) :
    0.001228 ≤ quarterWeight656 (r ^ 2) 1 := by
  obtain ⟨hz, hd⟩ := bridge_reflect_geometry hr
  have hz' :=
    pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ (11 / 10) * 14.21)
      (mul_le_mul_of_nonneg_left hz (by norm_num only)) 5
  have h :=
    mul_le_mul hz' hd (by norm_num only : (0 : ℝ) ≤ 0.000000158)
      (pow_nonneg (by linarith only [hz]) 5)
  unfold quarterWeight656
  simp only [Real.sqrt_one, one_div, inv_one, one_mul, Real.log_inv, sub_neg_eq_add]
  ring_nf at h ⊢
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
