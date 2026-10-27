/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMRNumerics

/-! # Coefficient 0.282924 for MR local divisor moduli

At n≥10^142, a local modulus with q²≤10^9*n has its old LLS envelope
max(3000,log(q)²) strictly below (282924/1000000)log(n)².
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A nonnegative logarithmic shift at most (9/142)L gives the strict
quarter-square coefficient 282924/1000000. Compare squares with (151/142)L and use
the exact positive rational gap. This absorbs the finite-index logarithmic shift. -/
theorem mr_local_shift_quarter_lt {L A : ℝ} (hL : 0 < L) (hA : 0 ≤ A)
    (hAL : A ≤ (9 / 142 : ℝ) * L) : (L + A) ^ 2 / 4 < (282924 / 1000000 : ℝ) * L ^ 2 := by
  have hb : L + A ≤ (151 / 142 : ℝ) * L := by linarith only [hAL]
  have hs := mul_self_le_mul_self (add_nonneg hL.le hA) hb
  have hpos := sq_pos_of_pos hL
  nlinarith only [hs, hpos]

/-- At log scale at least 326, the coefficient 282924/1000000 envelope exceeds 3000.
Compare squares at the endpoint. This covers small local moduli by prime divisors. -/
theorem mr_local_small_modulus_floor_lt {L : ℝ} (hL : 326 ≤ L) :
    (3000 : ℝ) < (282924 / 1000000 : ℝ) * L ^ 2 := by
  have hs := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 326) hL 2
  nlinarith only [hs]

/-- The decimal cutoff 10^142 absorbs both 3000 and the shifted quarter-square.
Retain the exact log(10) factor to bound the relative shift by 9/142.
This is the finite-index local coefficient certificate. -/
theorem mr_local_shifted_envelope_lt_of_decimal {n : ℕ} (hn : 10 ^ 142 ≤ n) :
    max 3000 (((Real.log n + 9 * Real.log 10) ^ 2) / 4) <
      (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 := by
  have hl := gaussianMR_log_of_decimal hn
  norm_num only [Nat.cast_ofNat] at hl
  have hL : 326 ≤ Real.log n := by linarith only [hl]
  have hlog :=
    Real.log_le_log (pow_pos (by norm_num only : (0 : ℝ) < 10) 142)
      (by exact_mod_cast hn : (10 : ℝ) ^ 142 ≤ n)
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hAL : 9 * Real.log 10 ≤ (9 / 142 : ℝ) * Real.log n := by
    have h := mul_le_mul_of_nonneg_left hlog (by norm_num only : (0 : ℝ) ≤ 9 / 142)
    nlinarith only [h]
  apply max_lt
  · exact mr_local_small_modulus_floor_lt hL
  · exact
      mr_local_shift_quarter_lt ((by norm_num only : (0 : ℝ) < 326).trans_le hL)
        (mul_nonneg (by norm_num only) (Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 10))) hAL

/-- A positive local modulus q with q²≤10^9*n has log(q) at most
(log(n)+9log(10))/2. Apply logarithmic monotonicity and product identities.
This transfers a local arithmetic size bound into the analytic cutoff. -/
theorem mr_local_log_le_of_square_le {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    (hsize : q ^ 2 ≤ 10 ^ 9 * n) : Real.log q ≤ (Real.log n + 9 * Real.log 10) / 2 := by
  have h :=
    Real.log_le_log (sq_pos_of_pos (Nat.cast_pos.mpr hq : (0 : ℝ) < q))
      (by exact_mod_cast hsize : (q : ℝ) ^ 2 ≤ (10 : ℝ) ^ 9 * n)
  rw [Real.log_pow,
    Real.log_mul (pow_ne_zero 9 (by norm_num only : (10 : ℝ) ≠ 0)) (Nat.cast_pos.mpr hn).ne',
    Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h]

/-- For n≥10^142 and positive q with q²≤10^9*n, the old LLS local
envelope is strictly below (282924/1000000)log(n)². Square the nonnegative local log
and use the certified shifted envelope. This feeds the local subgroup MR witness. -/
theorem mr_local_envelope_lt_of_square_le {n q : ℕ} (hn : 10 ^ 142 ≤ n) (hq : 0 < q)
    (hsize : q ^ 2 ≤ 10 ^ 9 * n) :
    max 3000 ((Real.log q) ^ 2) < (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 := by
  have hnpos : 0 < n := lt_of_lt_of_le (pow_pos (by decide : (0 : ℕ) < 10) 142) hn
  have hlog := mr_local_log_le_of_square_le hnpos hq hsize
  have hs := mul_self_le_mul_self (Real.log_natCast_nonneg q) hlog
  have hbound : (Real.log q) ^ 2 ≤ (Real.log n + 9 * Real.log 10) ^ 2 / 4 := by nlinarith only [hs]
  exact (max_le_max (le_refl 3000) hbound).trans_lt (mr_local_shifted_envelope_lt_of_decimal hn)

/-- The elementary decimal logarithm bound used to compare local and global scales. -/
theorem log_ten_lt_seven_thirds : Real.log 10 < 7 / 3 := by
  have hExp1 : (27 / 10 : ℝ) < Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
  have hpow : (27 / 10 : ℝ) ^ 7 < Real.exp 1 ^ 7 :=
    pow_lt_pow_left₀ hExp1 (by norm_num only) (by decide : 7 ≠ 0)
  have hexp7 : Real.exp 7 = Real.exp 1 ^ 7 := by
    rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num only]
    exact Real.exp_nat_mul 1 7
  have hExp7 : 1000 < Real.exp 7 := by
    rw [hexp7]
    exact (by norm_num only : (1000 : ℝ) < (27 / 10) ^ 7).trans hpow
  have hexpSevenThirds : Real.exp (7 / 3 : ℝ) ^ 3 = Real.exp 7 := by
    rw [← Real.exp_nat_mul (7 / 3 : ℝ) 3]
    congr 1
    norm_num only
  have hExpSevenThirds : 10 < Real.exp (7 / 3 : ℝ) := by
    apply lt_of_pow_lt_pow_left₀ 3 (Real.exp_pos _).le
    rw [hexpSevenThirds]
    norm_num only at hExp7 ⊢
    exact hExp7
  exact (Real.log_lt_iff_lt_exp (by norm_num only)).2 hExpSevenThirds

/-- A logarithmic scale of 250 already places n above the cube of the
10^9 finite-index threshold. -/
theorem ten_pow_twentyseven_le_of_log_ge_250 {n : ℕ} [NeZero n] (hL : 250 ≤ Real.log n) :
    10 ^ 27 ≤ n := by
  by_contra hnot
  have hsmall : n < 10 ^ 27 := Nat.lt_of_not_ge hnot
  have hcast : (n : ℝ) < (10 : ℝ) ^ 27 := by exact_mod_cast hsmall
  have hlogsmall := Real.log_lt_log (Nat.cast_pos.mpr (NeZero.pos n)) hcast
  have hlog27 : Real.log ((10 : ℝ) ^ 27) < 250 := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [log_ten_lt_seven_thirds]
  exact (not_lt_of_ge hL) (hlogsmall.trans hlog27)

/-- A logarithmic scale of 240 already places n above the cube of the
10^9 finite-index threshold. -/
theorem ten_pow_twentyseven_le_of_log_ge_240 {n : ℕ} [NeZero n] (hL : 240 ≤ Real.log n) :
    10 ^ 27 ≤ n := by
  by_contra hnot
  have hsmall : n < 10 ^ 27 := Nat.lt_of_not_ge hnot
  have hcast : (n : ℝ) < (10 : ℝ) ^ 27 := by exact_mod_cast hsmall
  have hlogsmall := Real.log_lt_log (Nat.cast_pos.mpr (NeZero.pos n)) hcast
  have hlog27 : Real.log ((10 : ℝ) ^ 27) < 240 := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [log_ten_lt_seven_thirds]
  exact (not_lt_of_ge hL) (hlogsmall.trans hlog27)

/-- A local modulus with `q² ≤ 10^9 n` has the envelope below `0.3 L²`
from logarithmic scale 250. Use `log(10) < 7/3` and the exact shifted-square
identity at the anchor 250. -/
theorem mr_local_envelope_lt_of_square_le_log250 {n q : ℕ} (hn : 0 < n) (hL : 250 ≤ Real.log n)
    (hq : 0 < q) (hsize : q ^ 2 ≤ 10 ^ 9 * n) :
    max 3000 ((Real.log q) ^ 2) < (3 / 10 : ℝ) * (Real.log n) ^ 2 := by
  have hlog10 := log_ten_lt_seven_thirds
  have hlogq := mr_local_log_le_of_square_le (Nat.cast_pos.mpr hn) hq hsize
  have hshift : 9 * Real.log 10 ≤ 21 := by nlinarith only [hlog10]
  have hqbound : Real.log q ≤ (Real.log n + 21) / 2 := by
    calc
      Real.log q ≤ (Real.log n + 9 * Real.log 10) / 2 := hlogq
      _ ≤ (Real.log n + 21) / 2 := by nlinarith only [hshift]
  have hLpos : 0 < Real.log n := by linarith only [hL]
  have htsq : 0 ≤ (Real.log n - 250) ^ 2 := sq_nonneg _
  have hgapIdentity :
    (3 / 10 : ℝ) * (Real.log n) ^ 2 - ((Real.log n + 21) / 2) ^ 2 =
      (Real.log n - 250) ^ 2 / 20 + 29 * (Real.log n - 250) / 2 + 1559 / 4 := by
    ring
  have hgap : 0 < (3 / 10 : ℝ) * (Real.log n) ^ 2 - ((Real.log n + 21) / 2) ^ 2 := by
    rw [hgapIdentity]
    have ht : 0 ≤ Real.log n - 250 := by linarith only [hL]
    nlinarith only [ht, htsq]
  have hpoly : ((Real.log n + 21) / 2) ^ 2 < (3 / 10 : ℝ) * (Real.log n) ^ 2 := by
    linarith only [hgap]
  have hLsq : (250 : ℝ) ^ 2 ≤ (Real.log n) ^ 2 := by nlinarith only [hL]
  have hfloor : (3000 : ℝ) < (3 / 10 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hLsq]
  have hlogsq := mul_self_le_mul_self (Real.log_natCast_nonneg q) hqbound
  have hlogsq' : (Real.log q) ^ 2 ≤ ((Real.log n + 21) / 2) ^ 2 := by nlinarith only [hlogsq]
  exact max_lt hfloor (hlogsq'.trans_lt hpoly)

/-- A local modulus with `q² ≤ 10^9 n` has its old LLS envelope strictly
below `0.3 (log n)²` once `log n ≥ 240`. The shifted-square identity is
anchored at 240. -/
theorem mr_local_envelope_lt_of_square_le_log240 {n q : ℕ} (hn : 0 < n) (hL : 240 ≤ Real.log n)
    (hq : 0 < q) (hsize : q ^ 2 ≤ 10 ^ 9 * n) :
    max 3000 ((Real.log q) ^ 2) < (3 / 10 : ℝ) * (Real.log n) ^ 2 := by
  have hlog10 := log_ten_lt_seven_thirds
  have hlogq := mr_local_log_le_of_square_le (Nat.cast_pos.mpr hn) hq hsize
  have hshift : 9 * Real.log 10 ≤ 21 := by nlinarith only [hlog10]
  have hqbound : Real.log q ≤ (Real.log n + 21) / 2 := by
    calc
      Real.log q ≤ (Real.log n + 9 * Real.log 10) / 2 := hlogq
      _ ≤ (Real.log n + 21) / 2 := by nlinarith only [hshift]
  have htsq : 0 ≤ (Real.log n - 240) ^ 2 := sq_nonneg _
  have hgapIdentity :
    (3 / 10 : ℝ) * (Real.log n) ^ 2 - ((Real.log n + 21) / 2) ^ 2 =
      (Real.log n - 240) ^ 2 / 20 + 27 * (Real.log n - 240) / 2 + 999 / 4 := by
    ring
  have hgap : 0 < (3 / 10 : ℝ) * (Real.log n) ^ 2 - ((Real.log n + 21) / 2) ^ 2 := by
    rw [hgapIdentity]
    have ht : 0 ≤ Real.log n - 240 := by linarith only [hL]
    nlinarith only [ht, htsq]
  have hpoly : ((Real.log n + 21) / 2) ^ 2 < (3 / 10 : ℝ) * (Real.log n) ^ 2 := by
    linarith only [hgap]
  have hLsq : (240 : ℝ) ^ 2 ≤ (Real.log n) ^ 2 := by nlinarith only [hL]
  have hfloor : (3000 : ℝ) < (3 / 10 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hLsq]
  have hlogsq := mul_self_le_mul_self (Real.log_natCast_nonneg q) hqbound
  have hlogsq' : (Real.log q) ^ 2 ≤ ((Real.log n + 21) / 2) ^ 2 := by nlinarith only [hlogsq]
  exact max_lt hfloor (hlogsq'.trans_lt hpoly)

end PseudoPrime.Analysis
