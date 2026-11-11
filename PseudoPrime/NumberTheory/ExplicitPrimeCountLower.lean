/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.ChebyshevPrimeCountLower
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevFiveTerm

/-! # A pointwise elementary prime-count lower bound -/

public section

namespace PseudoPrime.NumberTheory

/-- The logarithm tangent at `2^k` turns the Chebyshev lower bound into
an affine lower bound for `pi(B) log B`. This keeps the logarithm of two
symbolic so small rational constants can be checked without prime tables. -/
private theorem primeCounting_log_tangent (B k : ℕ) :
    ((B : ℝ) - k) * Real.log 2 - ((B : ℝ) + 1) / (2 : ℝ) ^ k + 1 ≤
      (B.primeCounting : ℝ) * Real.log B := by
  have hB : 0 < (B : ℝ) + 1 := by positivity
  have htwo : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num only) k
  have hlog := Real.log_le_sub_one_of_pos (div_pos hB htwo)
  rw [Real.log_div hB.ne' htwo.ne', Real.log_pow] at hlog
  have hmain := chebyshev_lower_le_primeCounting_mul_log B
  nlinarith only [hlog, hmain]

/-- For `B ≥ 4`, `B/4 ≤ pi(B) log B` unconditionally. Use the logarithm
tangent at four and `log 2 ≥ 69/100`. No prime enumeration is required. -/
theorem quarter_le_primeCounting_mul_log {B : ℕ} (hB : 4 ≤ B) :
    (B : ℝ) / 4 ≤ (B.primeCounting : ℝ) * Real.log B := by
  have hBR : (4 : ℝ) ≤ B := by exact_mod_cast hB
  have hlog : (69 / 100 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (B : ℝ) - 2 by linarith only [hBR])
  have ht := primeCounting_log_tangent B 2
  norm_num only [Nat.cast_ofNat, pow_succ, pow_zero, mul_one] at ht
  nlinarith only [hm, ht, hBR]

/-- For `B ≥ 16`, `B/2 ≤ pi(B) log B` unconditionally. Use the logarithm
tangent at sixteen; grouping prime powers avoids a square-root error. -/
theorem half_le_primeCounting_mul_log {B : ℕ} (hB : 16 ≤ B) :
    (B : ℝ) / 2 ≤ (B.primeCounting : ℝ) * Real.log B := by
  have hBR : (16 : ℝ) ≤ B := by exact_mod_cast hB
  have hlog : (69 / 100 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (B : ℝ) - 4 by linarith only [hBR])
  have ht := primeCounting_log_tangent B 4
  norm_num only [Nat.cast_ofNat, pow_succ, pow_zero, mul_one] at ht
  nlinarith only [hm, ht, hBR]

/-- For `B ≥ 32`, `(71/125) B ≤ pi(B) log B` unconditionally. The logarithm
tangent at thirty-two retains the coefficient used by the MR smooth-number
criterion while greatly lowering its prime-count entrance. -/
theorem primeCounting_log_lower_71_125 {B : ℕ} (hB : 32 ≤ B) :
    (568 / 1000 : ℝ) * B ≤ (B.primeCounting : ℝ) * Real.log B := by
  have hBR : (32 : ℝ) ≤ B := by exact_mod_cast hB
  have hlog : (69 / 100 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (B : ℝ) - 5 by linarith only [hBR])
  have ht := primeCounting_log_tangent B 5
  norm_num only [Nat.cast_ofNat, pow_succ, pow_zero, mul_one] at ht
  nlinarith only [hm, ht, hBR]

/-- For `B ≥ 256`, `(4/5) B ≤ pi(B) log B` unconditionally. Combine the
five-term Chebyshev lower bound with the logarithm tangent at 256.
This supplies a stronger product-counting density without a prime table. -/
theorem four_fifths_le_primeCounting_mul_log {B : ℕ} (hB : 256 ≤ B) :
    (4 / 5 : ℝ) * B ≤ (B.primeCounting : ℝ) * Real.log B := by
  have hBR : (256 : ℝ) ≤ B := by exact_mod_cast hB
  have hBp : (0 : ℝ) < B := by linarith only [hBR]
  have ht := Real.log_le_sub_one_of_pos (div_pos hBp (by norm_num only : (0 : ℝ) < 256))
  rw [Real.log_div hBp.ne' (by norm_num only : (256 : ℝ) ≠ 0),
    show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num only, Real.log_pow] at ht
  norm_num only [Nat.cast_ofNat] at ht
  have hs : (9 / 10 : ℝ) ≤ AnalyticNumberTheory.Arithmetic.chebyshevSlope := by
    linarith only [AnalyticNumberTheory.Arithmetic.chebyshevSlope_bounds.1]
  have hm := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg B : (0 : ℝ) ≤ B)
  have hp := AnalyticNumberTheory.Arithmetic.psi_lower_fiveTerm
    (show (30 : ℝ) ≤ B by linarith only [hBR])
  have hcount := Chebyshev.psi_le_primeCounting_mul_log B
  have hlog : Real.log 2 ≤ (7 / 10 : ℝ) := by linarith only [Real.log_two_lt_d9]
  nlinarith only [ht, hm, hp, hcount, hlog, hBR]

/-- For 0<A≤2 and L>1, a floor cutoff above 64^4 and the quantitative
gap L^(A-b)≥32 log L imply pi(floor(L^A))≥2L^b. Keep the floor loss
and apply the elementary quarter lower bound, without an eventual premise. -/
theorem two_mul_rpow_le_primeCounting_floor_of_gap {L A b : ℝ} (hL : 1 < L) (hA : 0 < A)
    (hA2 : A ≤ 2) (hB : 64 ^ 4 ≤ Nat.floor (L ^ A)) (hgap : 32 * Real.log L ≤ L ^ (A - b)) :
    2 * L ^ b ≤ ((Nat.floor (L ^ A)).primeCounting : ℝ) := by
  have hLp : 0 < L := zero_lt_one.trans hL
  have hz : 0 < Real.log L := Real.log_pos hL
  have hpow : 0 ≤ L ^ b := Real.rpow_nonneg hLp.le b
  have hB1 : (1 : ℝ) ≤ Nat.floor (L ^ A) := by exact_mod_cast (le_trans (by decide : 1 ≤ 64 ^ 4) hB)
  have hf := Nat.lt_floor_add_one (L ^ A)
  have hhalf : L ^ A ≤ 2 * (Nat.floor (L ^ A) : ℝ) := by linarith only [hf, hB1]
  have hlogB :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one hB1) (Nat.floor_le (Real.rpow_nonneg hLp.le A))
  rw [Real.log_rpow hLp A] at hlogB
  have hpi := quarter_le_primeCounting_mul_log ((by norm_num only : 4 ≤ 64 ^ 4).trans hB)
  have hm :=
    mul_le_mul_of_nonneg_left hlogB
      (Nat.cast_nonneg ((Nat.floor (L ^ A)).primeCounting) : (0 : ℝ) ≤ _)
  have hg := mul_le_mul_of_nonneg_right hgap hpow
  rw [← Real.rpow_add hLp, sub_add_cancel] at hg
  have hs := mul_nonneg (sub_nonneg.mpr hA2) (mul_nonneg hpow hz.le)
  apply (mul_le_mul_iff_left₀ (mul_pos hA hz)).mp
  nlinarith only [hpi, hm, hhalf, hg, hs]

/-- For $0<A\le2$ and $L>1$, the stronger pointwise prime-count bound and
the gap $L^{A-b}\ge16\log L$ imply $\pi(\lfloor L^A\rfloor)\ge2L^b$.
The floor loss is retained explicitly. -/
theorem two_mul_rpow_le_primeCounting_floor_of_half_gap {L A b : ℝ} (hL : 1 < L) (hA : 0 < A)
    (hA2 : A ≤ 2) (hB : 64 ^ 4 ≤ Nat.floor (L ^ A)) (hgap : 16 * Real.log L ≤ L ^ (A - b)) :
    2 * L ^ b ≤ ((Nat.floor (L ^ A)).primeCounting : ℝ) := by
  have hLp : 0 < L := zero_lt_one.trans hL
  have hz : 0 < Real.log L := Real.log_pos hL
  have hpow : 0 ≤ L ^ b := Real.rpow_nonneg hLp.le b
  have hB1 : (1 : ℝ) ≤ Nat.floor (L ^ A) := by exact_mod_cast (le_trans (by decide : 1 ≤ 64 ^ 4) hB)
  have hf := Nat.lt_floor_add_one (L ^ A)
  have hhalf : L ^ A ≤ 2 * (Nat.floor (L ^ A) : ℝ) := by linarith only [hf, hB1]
  have hlogB :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one hB1) (Nat.floor_le (Real.rpow_nonneg hLp.le A))
  rw [Real.log_rpow hLp A] at hlogB
  have hpi := half_le_primeCounting_mul_log (B := Nat.floor (L ^ A))
      ((by norm_num only : 16 ≤ 64 ^ 4).trans hB)
  have hm :=
    mul_le_mul_of_nonneg_left hlogB
      (Nat.cast_nonneg ((Nat.floor (L ^ A)).primeCounting) : (0 : ℝ) ≤ _)
  have hg := mul_le_mul_of_nonneg_right hgap hpow
  rw [← Real.rpow_add hLp, sub_add_cancel] at hg
  have hs := mul_nonneg (sub_nonneg.mpr hA2) (mul_nonneg hpow hz.le)
  apply (mul_le_mul_iff_left₀ (mul_pos hA hz)).mp
  nlinarith only [hpi, hm, hhalf, hg, hs]

/-- If `0 < A ≤ 1900001/1000000`, `L > 1`, the cutoff is at least 256,
and `L^(A-b) ≥ (9501/1000) log L`, then `pi(floor(L^A)) ≥ 2 L^b`.
Use the four-fifths prime-count bound and retain the floor loss. -/
theorem two_mul_rpow_le_primeCount_of_exp_gap {L A b : ℝ} (hL : 1 < L) (hA : 0 < A)
    (hA2 : A ≤ 1900001 / 1000000) (hB : 256 ≤ Nat.floor (L ^ A))
    (hgap : (9501 / 1000 : ℝ) * Real.log L ≤ L ^ (A - b)) :
    2 * L ^ b ≤ ((Nat.floor (L ^ A)).primeCounting : ℝ) := by
  have hLp : 0 < L := zero_lt_one.trans hL
  have hz : 0 < Real.log L := Real.log_pos hL
  have hpow : 0 ≤ L ^ b := Real.rpow_nonneg hLp.le b
  have hB1 : (1 : ℝ) ≤ Nat.floor (L ^ A) := by exact_mod_cast (le_trans (by decide : 1 ≤ 256) hB)
  have hf := Nat.lt_floor_add_one (L ^ A)
  have hhalf : L ^ A ≤ 2 * (Nat.floor (L ^ A) : ℝ) := by linarith only [hf, hB1]
  have hlogB :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one hB1) (Nat.floor_le (Real.rpow_nonneg hLp.le A))
  rw [Real.log_rpow hLp A] at hlogB
  have hpi := four_fifths_le_primeCounting_mul_log (B := Nat.floor (L ^ A)) hB
  have hm :=
    mul_le_mul_of_nonneg_left hlogB
      (Nat.cast_nonneg ((Nat.floor (L ^ A)).primeCounting) : (0 : ℝ) ≤ _)
  have hg := mul_le_mul_of_nonneg_right hgap hpow
  rw [← Real.rpow_add hLp, sub_add_cancel] at hg
  have hr : 4000 * A ≤ 800 * (9501 / 1000 : ℝ) := by nlinarith only [hA2]
  have hmargin : 0 ≤ (4 / 5 : ℝ) * (9501 / 1000) / 2 - 2 * A := by nlinarith only [hr]
  have hs := mul_nonneg hmargin (mul_nonneg hpow hz.le)
  apply (mul_le_mul_iff_left₀ (mul_pos hA hz)).mp
  nlinarith only [hpi, hm, hhalf, hg, hs]

end PseudoPrime.NumberTheory
