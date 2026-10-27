/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ThirteenthLogEnergyBudget
public import PseudoPrime.Analysis.LogarithmicMomentScales

/-! # Coefficient-sensitive thirteenth-power logarithmic energy budgets -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Normalize the error alternative with arbitrary nonnegative moment and
band coefficients U,V. Retain their exact sixth and eighth powers instead
of rounding them independently. This supports explicit energy constants. -/
theorem thirteenth_error_budget_coeff {p E T J L U V : ℝ} (hp : 0 ≤ p) (hT : 0 ≤ T) (hJ : 0 ≤ J)
    (hL : 0 ≤ L) (hU : 0 ≤ U) (hTb : T ≤ U * p ^ 3 * L) (hJb : J ≤ V * L)
    (he : E ^ 13 ≤ 10995116277760000 * p ^ 14 * T ^ 6 * J ^ 8) :
    E ^ 13 ≤ (10995116277760000 * U ^ 6 * V ^ 8) * p ^ 32 * L ^ 14 := by
  have ht := pow_le_pow_left₀ hT hTb 6
  have hj := pow_le_pow_left₀ hJ hJb 8
  have hprod :=
    mul_le_mul ht hj (pow_nonneg hJ 8)
      (pow_nonneg (mul_nonneg (mul_nonneg hU (pow_nonneg hp 3)) hL) 6)
  have hs :=
    mul_le_mul_of_nonneg_left hprod
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 10995116277760000) (pow_nonneg hp 14))
  nlinarith only [he, hs]

/-- Normalize the main cubic alternative using the same U,V. The generic
cubic-to-thirteenth comparison gives coefficient 4(2048UV^3)^4.
This keeps all coefficient losses visible before choosing a common bound. -/
theorem thirteenth_main_budget_coeff {p E T J L U V : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) (hJ : 0 ≤ J)
    (hL : 0 ≤ L) (hU : 0 ≤ U) (hV : 0 ≤ V) (hEp : E ≤ p ^ 3) (hL2 : L ^ 2 ≤ 4 * p)
    (hTb : T ≤ U * p ^ 3 * L) (hJb : J ≤ V * L) (hc : E ^ 3 ≤ 2048 * p ^ 4 * T * J ^ 3) :
    E ^ 13 ≤ (4 * (2048 * U * V ^ 3) ^ 4) * p ^ 32 * L ^ 14 := by
  have hj := pow_le_pow_left₀ hJ hJb 3
  have htj := mul_le_mul hTb hj (pow_nonneg hJ 3) (mul_nonneg (mul_nonneg hU (pow_nonneg hp 3)) hL)
  have hs :=
    mul_le_mul_of_nonneg_left htj (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2048) (pow_nonneg hp 4))
  have hc' : E ^ 3 ≤ (2048 * U * V ^ 3) * p ^ 7 * L ^ 4 := by nlinarith only [hc, hs]
  exact
    thirteenth_le_of_cubic_log_budget hp hE hL
      (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2048) hU) (pow_nonneg hV 3)) hEp hc' hL2

/-- Three energy alternatives fit any coefficient C dominating their two
explicit normalized coefficients. The small diagonal case is handled
separately by the consumer. No new moment or incidence estimate is assumed. -/
theorem thirteenth_alternatives_budget_coeff {p E T J L U V C : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hT : 0 ≤ T) (hJ : 1 ≤ J) (hL : 0 ≤ L) (hU : 0 ≤ U) (hV : 0 ≤ V) (hEp : E ≤ p ^ 3)
    (hL2 : L ^ 2 ≤ 4 * p) (hTb : T ≤ U * p ^ 3 * L) (hJb : J ≤ V * L)
    (hCm : 4 * (2048 * U * V ^ 3) ^ 4 ≤ C) (hCe : 10995116277760000 * U ^ 6 * V ^ 8 ≤ C)
    (ha :
      E ^ 3 ≤ 40 * p ^ 4 * T * J ∨
        E ^ 3 ≤ 2048 * p ^ 4 * T * J ^ 3 ∨ E ^ 13 ≤ 10995116277760000 * p ^ 14 * T ^ 6 * J ^ 8) :
    E ^ 13 ≤ C * p ^ 32 * L ^ 14 := by
  have hJ0 : 0 ≤ J := zero_le_one.trans hJ
  have hscale : 0 ≤ p ^ 32 * L ^ 14 := mul_nonneg (pow_nonneg hp 32) (pow_nonneg hL 14)
  have hmain (hc : E ^ 3 ≤ 2048 * p ^ 4 * T * J ^ 3) : E ^ 13 ≤ C * p ^ 32 * L ^ 14 := by
    have hb := thirteenth_main_budget_coeff hp hE hJ0 hL hU hV hEp hL2 hTb hJb hc
    have hs := mul_le_mul_of_nonneg_right hCm hscale
    nlinarith only [hb, hs]
  rcases ha with hd | hm | he
  · apply hmain
    have hj13 : J ≤ J ^ 3 := by simpa only [pow_one] using pow_le_pow_right₀ hJ (by decide : 1 ≤ 3)
    have hb :=
      mul_le_mul_of_nonneg_left hj13
        (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 40) (pow_nonneg hp 4)) hT)
    have hc :=
      mul_le_mul_of_nonneg_right (by norm_num only : (40 : ℝ) ≤ 2048)
        (mul_nonneg (mul_nonneg (pow_nonneg hp 4) hT) (pow_nonneg hJ0 3))
    nlinarith only [hd, hb, hc]
  · exact hmain hm
  · have hb := thirteenth_error_budget_coeff hp hT hJ0 hL hU hTb hJb he
    have hs := mul_le_mul_of_nonneg_right hCe hscale
    nlinarith only [hb, hs]

/-- For every natural n, log2(n)+1 is at most 3/2 times 1+ln(n).
Use ln(2)>2/3 rather than the coarser 1/2 bound. This reduces the eighth
power of the dyadic band coefficient in the energy normalization. -/
theorem log2_succ_le_three_halves_one_add_log (n : ℕ) :
    ((Nat.log2 n + 1 : ℕ) : ℝ) ≤ (3 / 2 : ℝ) * (1 + Real.log n) := by
  have hl := Real.log_natCast_nonneg n
  have h₂ : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left h₂ hl
  have hd : Real.log n / Real.log 2 ≤ (3 / 2 : ℝ) * Real.log n :=
    (div_le_iff₀ (Real.log_pos (by norm_num only : (1 : ℝ) < 2))).mpr (by nlinarith only [hm])
  have hj := Real.log2_le_logb n
  rw [Real.logb] at hj
  rw [Nat.cast_add, Nat.cast_one]
  linarith only [hj, hd]

/-- The actual moment coefficient 786433 and band coefficient 3/2 fit
the common energy coefficient 2^176. Apply the parameterized alternatives
and verify the two rational coefficient inequalities exactly. -/
theorem refined_thirteenth_budget_of_alternatives {p E T J L : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hT : 0 ≤ T) (hJ : 1 ≤ J) (hL : 0 ≤ L) (hEp : E ≤ p ^ 3) (hL2 : L ^ 2 ≤ 4 * p)
    (hTb : T ≤ 786433 * p ^ 3 * L) (hJb : J ≤ (3 / 2 : ℝ) * L)
    (ha :
      E ^ 3 ≤ 40 * p ^ 4 * T * J ∨
        E ^ 3 ≤ 2048 * p ^ 4 * T * J ^ 3 ∨ E ^ 13 ≤ 10995116277760000 * p ^ 14 * T ^ 6 * J ^ 8) :
    E ^ 13 ≤ 2 ^ 176 * p ^ 32 * L ^ 14 := by
  exact
    thirteenth_alternatives_budget_coeff hp hE hT hJ hL (by norm_num only : (0 : ℝ) ≤ 786433)
      (by norm_num only : (0 : ℝ) ≤ 3 / 2) hEp hL2 hTb hJb (by norm_num only) (by norm_num only) ha

/-- Small energy E<=4p^2 also fits the refined coefficient for p,L>=1.
Raise the small bound to the thirteenth power, then enlarge the p and L
powers. This closes the diagonal branch without a finite certificate. -/
theorem refined_thirteenth_budget_of_small_energy {p E L : ℝ} (hp : 1 ≤ p) (hE : 0 ≤ E) (hL : 1 ≤ L)
    (hb : E ≤ 4 * p ^ 2) : E ^ 13 ≤ 2 ^ 176 * p ^ 32 * L ^ 14 := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hs := pow_le_pow_left₀ hE hb 13
  have hp26 := pow_le_pow_right₀ hp (by decide : 26 ≤ 32)
  have hm :=
    mul_le_mul (by norm_num only : (4 : ℝ) ^ 13 ≤ 2 ^ 176) hp26 (pow_nonneg hp0 26)
      (by norm_num only : (0 : ℝ) ≤ 2 ^ 176)
  have hb' : E ^ 13 ≤ 2 ^ 176 * p ^ 32 := by nlinarith only [hs, hm]
  have ht :=
    mul_le_mul_of_nonneg_left (one_le_pow₀ hL (n := 14))
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2 ^ 176) (pow_nonneg hp0 32))
  nlinarith only [hb', ht]

end PseudoPrime.Analysis
