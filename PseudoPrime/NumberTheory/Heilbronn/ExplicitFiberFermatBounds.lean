/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.ExplicitFiberFermatReduction
public import PseudoPrime.NumberTheory.Heilbronn.ExplicitFiberLogThreshold
public import PseudoPrime.NumberTheory.ExplicitPrimeCountLower
public import PseudoPrime.Analysis.ExplicitSmoothLogBudgets
public import PseudoPrime.Analysis.ExplicitRationalFloorBudget
public import PseudoPrime.Analysis.ExplicitRationalFloorBudget

/-! # A fully explicit logarithmic Fermat-quotient bound -/

public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Every odd prime p≥2^(2^(1388714689827)) has a prime q≤log(p)^(1838239/1000000)
whose (p-1)-st power is nontrivial modulo p². Prove all pointwise
smooth budgets from the explicit double-logarithm threshold and apply
the finite-fiber interval bound. No GRH or external estimate is assumed. -/
theorem exists_prime_pow_ne_one_1838239_1000000 {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold (1388714689827) ≤ p) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log p) ^ (1838239 / 1000000 : ℝ) ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  have hp := (Fact.out : p.Prime).pos
  have hLp : 0 < Real.log p := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hz := le_log_log_387000000000 hlarge
  have hzsmall : (10 : ℝ) ^ 11 ≤ Real.log (Real.log p) := by exact le_trans (by norm_num only) hz
  have hz20 : 20000000000 ≤ Real.log (Real.log p) := le_trans (by norm_num only) hzsmall
  obtain ⟨hL, _⟩ :=
    Analysis.fixed_smooth_log_size_bounds hLp
      (le_trans (by norm_num only : (2000000000 : ℝ) ≤ 20000000000) hz20)
  have hgap := Analysis.explicit_smooth_scale_125_68_gap hL hzsmall
  have hL1 : 1 ≤ Real.log p := by linarith only [hL]
  have hpow : Real.log p ≤ (Real.log p) ^ (1838239 / 1000000 : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num only : (1 : ℝ) ≤ 1838239 / 1000000)
  have hB : 64 ^ 4 ≤ Nat.floor ((Real.log p) ^ (1838239 / 1000000 : ℝ)) := by
    apply Nat.le_floor
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    linarith only [hL, hpow]
  have hC : 0 < Nat.floor ((p : ℝ) ^ (8382354 / 10000000 : ℝ)) :=
    Nat.lt_of_lt_of_le (by decide : 0 < 1)
      (Nat.le_floor
        (by
          simpa only [Nat.cast_one] using
            Real.one_le_rpow (Nat.one_le_cast.mpr (Nat.succ_le_of_lt hp))
              (by norm_num only : (0 : ℝ) ≤ 8382354 / 10000000)))
  have hpowergap :
    32 * Real.log (Real.log p) ≤ (Real.log p) ^ ((1838239 / 1000000 : ℝ) - 1838238 / 1000000) := by
    rw [show (1838239 / 1000000 : ℝ) - 1838238 / 1000000 = 1 / 1000000 by norm_num only,
      Real.rpow_def_of_pos hLp]
    convert Analysis.thirty_two_mul_le_exp_gap_million hz using 1
  have hMp :=
    NumberTheory.two_mul_rpow_le_primeCounting_floor_of_gap
      (lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 10 ^ 20) hL)
      (by norm_num only : (0 : ℝ) < 1838239 / 1000000)
      (by norm_num only : (1838239 / 1000000 : ℝ) ≤ 2) hB hpowergap
  exact
    exists_prime_pow_ne_one_1838239_d6_smooth hodd hlarge (by linarith only [hL])
      (Nat.lt_of_lt_of_le (by decide : 0 < 64 ^ 4) hB) hC (by linarith only [hz]) hMp hgap
      (fun k hcut ↦ Analysis.rational_cutoff_125_68_le_prime_mul_floor hp hL hcut)

/-- Every odd prime p≥P(283000007562) has a prime q≤log(p)^(1850004/1000000)
whose (p−1)-st power is nontrivial modulo p². Prove each pointwise smooth
budget from the double-logarithm threshold and apply the 74/40 interval bound. -/
theorem exists_prime_pow_ne_one_1850004_1000000 {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 283000007562 ≤ p) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log p) ^ (1850004 / 1000000 : ℝ) ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  have hp := (Fact.out : p.Prime).pos
  have hLp : 0 < Real.log p := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hz := le_log_log_100000000000 hlarge
  have hzsmall : (10 : ℝ) ^ 11 ≤ Real.log (Real.log p) := by exact le_trans (by norm_num only) hz
  have hz20 : 20000000000 ≤ Real.log (Real.log p) := le_trans (by norm_num only) hzsmall
  obtain ⟨hL, _⟩ :=
    Analysis.fixed_smooth_log_size_bounds hLp
      (le_trans (by norm_num only : (2000000000 : ℝ) ≤ 20000000000) hz20)
  have hgap := Analysis.explicit_smooth_scale_74_40_gap hL hzsmall
  have hL1 : 1 ≤ Real.log p := by linarith only [hL]
  have hpow : Real.log p ≤ (Real.log p) ^ (1850004 / 1000000 : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num only : (1 : ℝ) ≤ 1850004 / 1000000)
  have hB : 64 ^ 4 ≤ Nat.floor ((Real.log p) ^ (1850004 / 1000000 : ℝ)) := by
    apply Nat.le_floor
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    linarith only [hL, hpow]
  have hC : 0 < Nat.floor ((p : ℝ) ^ (8500002 / 10000000 : ℝ)) :=
    Nat.lt_of_lt_of_le (by decide : 0 < 1)
      (Nat.le_floor
        (by
          simpa only [Nat.cast_one] using
            Real.one_le_rpow (Nat.one_le_cast.mpr (Nat.succ_le_of_lt hp))
              (by norm_num only : (0 : ℝ) ≤ 8500002 / 10000000)))
  have hpowergap :
    32 * Real.log (Real.log p) ≤ (Real.log p) ^ ((1850004 / 1000000 : ℝ) - 1850003 / 1000000) := by
    rw [show (1850004 / 1000000 : ℝ) - 1850003 / 1000000 = 1 / 1000000 by norm_num only,
      Real.rpow_def_of_pos hLp]
    convert Analysis.mul_32_le_exp_gap_1000000_of_ge_100000000000 hz using 1
  have hMp :=
    NumberTheory.two_mul_rpow_le_primeCounting_floor_of_gap
      (lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 10 ^ 20) hL)
      (by norm_num only : (0 : ℝ) < 1850004 / 1000000)
      (by norm_num only : (1850004 / 1000000 : ℝ) ≤ 2) hB hpowergap
  exact
    exists_prime_pow_ne_one_1850004_d6_smooth hodd hlarge (by linarith only [hL])
      (Nat.lt_of_lt_of_le (by decide : 0 < 64 ^ 4) hB) hC (by linarith only [hz]) hMp hgap
      (fun k hcut ↦ Analysis.rational_cutoff_74_40_le_prime_mul_floor hp hL hcut)

/-- Every odd prime p≥P(242591045876) has a prime q≤log(p)^(184211/100000)
whose (p−1)-st power is nontrivial modulo p². Prove each pointwise smooth
budget from the double-logarithm threshold and apply the 70/38 interval bound. -/
theorem exists_prime_pow_ne_one_184211_100000 {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 242591045876 ≤ p) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log p) ^ (184211 / 100000 : ℝ) ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  have hp := (Fact.out : p.Prime).pos
  have hLp : 0 < Real.log p := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hz := le_log_log_100000000000_38_70 hlarge
  have hzsmall : (10 : ℝ) ^ 11 ≤ Real.log (Real.log p) := by exact le_trans (by norm_num only) hz
  have hz20 : 20000000000 ≤ Real.log (Real.log p) := le_trans (by norm_num only) hzsmall
  obtain ⟨hL, _⟩ :=
    Analysis.fixed_smooth_log_size_bounds hLp
      (le_trans (by norm_num only : (2000000000 : ℝ) ≤ 20000000000) hz20)
  have hgap := Analysis.explicit_smooth_scale_70_38_gap hL hzsmall
  have hL1 : 1 ≤ Real.log p := by linarith only [hL]
  have hpow : Real.log p ≤ (Real.log p) ^ (184211 / 100000 : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num only : (1 : ℝ) ≤ 184211 / 100000)
  have hB : 64 ^ 4 ≤ Nat.floor ((Real.log p) ^ (184211 / 100000 : ℝ)) := by
    apply Nat.le_floor
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    linarith only [hL, hpow]
  have hC : 0 < Nat.floor ((p : ℝ) ^ (160000019 / 190000000 : ℝ)) :=
    Nat.lt_of_lt_of_le (by decide : 0 < 1)
      (Nat.le_floor
        (by
          simpa only [Nat.cast_one] using
            Real.one_le_rpow (Nat.one_le_cast.mpr (Nat.succ_le_of_lt hp))
              (by norm_num only : (0 : ℝ) ≤ 160000019 / 190000000)))
  have hpowergap :
    32 * Real.log (Real.log p) ≤ (Real.log p) ^ ((184211 / 100000 : ℝ) - 1842109 / 1000000) := by
    rw [show (184211 / 100000 : ℝ) - 1842109 / 1000000 = 1 / 1000000 by norm_num only,
      Real.rpow_def_of_pos hLp]
    convert Analysis.mul_32_le_exp_gap_1000000_of_ge_100000000000 hz using 1
  have hMp :=
    NumberTheory.two_mul_rpow_le_primeCounting_floor_of_gap
      (lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 10 ^ 20) hL)
      (by norm_num only : (0 : ℝ) < 184211 / 100000) (by norm_num only : (184211 / 100000 : ℝ) ≤ 2)
      hB hpowergap
  exact
    exists_prime_pow_ne_one_184211_d5_smooth hodd hlarge (by linarith only [hL])
      (Nat.lt_of_lt_of_le (by decide : 0 < 64 ^ 4) hB) hC (by linarith only [hz]) hMp hgap
      (fun k hcut ↦ Analysis.rational_cutoff_70_38_le_prime_mul_floor hp hL hcut)

/-- Every odd prime p≥P(145000006050) has a prime q≤log(p)^(1843755/1000000)
whose (p−1)-st power is nontrivial modulo p². Derive the smooth-number
budgets from the double-log threshold and apply the 59/32 interval bound. -/
theorem exists_prime_pow_ne_one_1843755_1000000 {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 145000006050 ≤ p) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log p) ^ (1843755 / 1000000 : ℝ) ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  have hp := (Fact.out : p.Prime).pos
  have hLp : 0 < Real.log p := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hz := le_log_log_20000000000_32_59 hlarge
  have hzsmall : (10 : ℝ) ^ 10 ≤ Real.log (Real.log p) := by exact le_trans (by norm_num only) hz
  have hz2 : 2000000000 ≤ Real.log (Real.log p) := le_trans (by norm_num only) hz
  obtain ⟨hL, _⟩ := Analysis.fixed_smooth_log_size_bounds hLp hz2
  have hgap := Analysis.explicit_smooth_scale_59_32_gap hL hz2
  have hL1 : 1 ≤ Real.log p := by linarith only [hL]
  have hpow : Real.log p ≤ (Real.log p) ^ (1843755 / 1000000 : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num only : (1 : ℝ) ≤ 1843755 / 1000000)
  have hB : 64 ^ 4 ≤ Nat.floor ((Real.log p) ^ (1843755 / 1000000 : ℝ)) := by
    apply Nat.le_floor
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    linarith only [hL, hpow]
  have hC : 0 < Nat.floor ((p : ℝ) ^ (8437505 / 10000000 : ℝ)) :=
    Nat.lt_of_lt_of_le (by decide : 0 < 1)
      (Nat.le_floor
        (by
          simpa only [Nat.cast_one] using
            Real.one_le_rpow (Nat.one_le_cast.mpr (Nat.succ_le_of_lt hp))
              (by norm_num only : (0 : ℝ) ≤ 8437505 / 10000000)))
  have hpowergap :
    32 * Real.log (Real.log p) ≤ (Real.log p) ^ ((1843755 / 1000000 : ℝ) - 1843754 / 1000000) := by
    rw [show (1843755 / 1000000 : ℝ) - 1843754 / 1000000 = 1 / 1000000 by norm_num only,
      Real.rpow_def_of_pos hLp]
    convert Analysis.thirty_two_mul_le_exp_gap_million_of_two_billion hz2 using 1
  have hMp :=
    NumberTheory.two_mul_rpow_le_primeCounting_floor_of_gap
      (lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 10 ^ 20) hL)
      (by norm_num only : (0 : ℝ) < 1843755 / 1000000)
      (by norm_num only : (1843755 / 1000000 : ℝ) ≤ 2) hB hpowergap
  exact
    exists_prime_pow_ne_one_1843755_d6_smooth hodd hlarge (by linarith only [hL])
      (Nat.lt_of_lt_of_le (by decide : 0 < 64 ^ 4) hB) hC (by linarith only [hz]) hMp hgap
      (fun k hcut ↦ Analysis.rational_cutoff_59_32_le_prime_mul_floor hp hL hcut)

/-- Every odd prime p≥P(4449271510) has a prime q with
q≤(log p)^(1900000016707/1000000000000) whose (p−1)-st power is nontrivial
modulo p². Derive the smooth-number budgets from the double-log threshold and
apply the 19/10 interval bound. -/
theorem exists_prime_pow_ne_one_1900000016707_d12 {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 4449271510 ≤ p) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log p) ^ (1900000016707 / 1000000000000 : ℝ) ∧
        (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  have hp := (Fact.out : p.Prime).pos
  have hLp : 0 < Real.log p := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hz : 3084000000 ≤ Real.log (Real.log p) := le_log_log_3084000000_10_19 hlarge
  have hz2 : 2000000000 ≤ Real.log (Real.log p) := by exact le_trans (by norm_num only) hz
  have hzBudget : 3084000000 ≤ Real.log (Real.log p) := hz
  obtain ⟨hL, _⟩ := Analysis.fixed_smooth_log_size_bounds hLp hz2
  have hgap := Analysis.smooth_scale_19_10_gap_of_log_ge_3084000000 hL hzBudget
  have hL1 : 1 ≤ Real.log p := by linarith only [hL]
  have hpow : Real.log p ≤ (Real.log p) ^ (1900000016707 / 1000000000000 : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1
        (by norm_num only : (1 : ℝ) ≤ 1900000016707 / 1000000000000)
  have hB : 64 ^ 4 ≤ Nat.floor ((Real.log p) ^ (1900000016707 / 1000000000000 : ℝ)) := by
    apply Nat.le_floor
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    linarith only [hL, hpow]
  have hC : 0 < Nat.floor ((p : ℝ) ^ (900000000000000001 / 1000000000000000000 : ℝ)) :=
    Nat.lt_of_lt_of_le (by decide : 0 < 1)
      (Nat.le_floor
        (by
          simpa only [Nat.cast_one] using
            Real.one_le_rpow (Nat.one_le_cast.mpr (Nat.succ_le_of_lt hp))
              (by norm_num only : (0 : ℝ) ≤ 900000000000000001 / 1000000000000000000)))
  have hpowergap_base :
    32 * Real.log (Real.log p) ≤ (Real.log p) ^ (820868 / 100000000000000 : ℝ) := by
    rw [Real.rpow_def_of_pos hLp]
    simpa only [mul_comm] using Analysis.thirty_two_mul_le_exp_gap_820868 hz
  have hpowergap_delta :
    (820868 / 100000000000000 : ℝ) ≤
      (1900000016707 / 1000000000000 : ℝ) - 1900000008498 / 1000000000000 := by
    norm_num only
  have hpowergap :
    32 * Real.log (Real.log p) ≤
      (Real.log p) ^ ((1900000016707 / 1000000000000 : ℝ) - 1900000008498 / 1000000000000) :=
    le_trans hpowergap_base (Real.rpow_le_rpow_of_exponent_le hL1 hpowergap_delta)
  have hMp :=
    NumberTheory.two_mul_rpow_le_primeCounting_floor_of_gap
      (lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 10 ^ 20) hL)
      (by norm_num only : (0 : ℝ) < 1900000016707 / 1000000000000)
      (by norm_num only : (1900000016707 / 1000000000000 : ℝ) ≤ 2) hB hpowergap
  exact
    exists_prime_pow_ne_one_1900000016707_d12_smooth hodd hlarge (by linarith only [hL])
      (Nat.lt_of_lt_of_le (by decide : 0 < 64 ^ 4) hB) hC (by linarith only [hz]) hMp hgap
      (fun k hcut ↦ Analysis.rational_cutoff_19_10_le_prime_mul_floor hp hL hcut)

/-- Every odd prime p≥P(76598623) has a prime q at most
(log p)^1.9000007986 whose (p−1)-st power is nontrivial modulo p². -/
theorem exists_prime_pow_ne_one_19000007986_d10 {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 76598623 ≤ p) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log p) ^ (19000007986 / 10000000000 : ℝ) ∧
        (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  have hp := (Fact.out : p.Prime).pos
  have hLp : 0 < Real.log p := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hz := le_log_log_53000000 (Nat.le_refl 76598623) hlarge
  have hlogLower := Analysis.pow_10_12_le_of_log_ge_53000000 hLp hz
  have hlogScale := Analysis.pow_10_20_le_of_log_ge_53000000 hLp hz
  have hgap :=
    Analysis.smooth_scale_19_10_gap_of_log_lower_bound hlogLower hz
      (by norm_num only : (0 : ℝ) < 53000000)
      (by norm_num only : (0 : ℝ) ≤ 19000007986 / 10000000000)
      (by norm_num only :
        (99999954008 / 100000000000 : ℝ) * (19000007986 / 10000000000) +
            (19000007986 / 10000000000) * (2 / 53000000) <
          19 / 10)
  have hL1 : 1 ≤ Real.log p := by linarith only [hlogLower]
  have hpow : Real.log p ≤ (Real.log p) ^ (19000007986 / 10000000000 : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num only : (1 : ℝ) ≤ 19000007986 / 10000000000)
  have hB : 64 ^ 4 ≤ Nat.floor ((Real.log p) ^ (19000007986 / 10000000000 : ℝ)) := by
    apply Nat.le_floor
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    nlinarith only [hlogLower, hpow]
  have hC : 0 < Nat.floor ((p : ℝ) ^ (900000000000000001 / 1000000000000000000 : ℝ)) :=
    Nat.lt_of_lt_of_le (by decide : 0 < 1)
      (Nat.le_floor
        (by
          simpa only [Nat.cast_one] using
            Real.one_le_rpow (Nat.one_le_cast.mpr (Nat.succ_le_of_lt hp))
              (by norm_num only : (0 : ℝ) ≤ 900000000000000001 / 1000000000000000000)))
  have hpowergap :
    (13381 / 1000 : ℝ) * Real.log (Real.log p) ≤
      (Real.log p) ^ ((19000007986 / 10000000000 : ℝ) - 1900000414 / 1000000000) := by
    rw [show (19000007986 / 10000000000 : ℝ) - 1900000414 / 1000000000 = 3846 / 10000000000 by
        norm_num only]
    rw [Real.rpow_def_of_pos hLp]
    simpa only [mul_comm] using Analysis.mul_13381_1000_le_exp_gap_3846_d10 hz
  have hMp :=
    NumberTheory.two_mul_rpow_le_primeCount_of_exp_gap (b := 1900000414 / 1000000000)
      (lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 10 ^ 12) hlogLower)
      (by norm_num only : (0 : ℝ) < 19000007986 / 10000000000)
      (by norm_num only : (19000007986 / 10000000000 : ℝ) ≤ 1900001 / 1000000) hB hpowergap
  exact
    exists_prime_pow_ne_one_19000007986_d10_smooth hodd (Nat.le_refl 76598623) hlarge
      (by linarith only [hlogLower]) (Nat.lt_of_lt_of_le (by decide : 0 < 64 ^ 4) hB) hC
      (by linarith only [hz]) hMp hgap
      (fun k hcut ↦ Analysis.rational_cutoff_19_10_le_prime_mul_floor hp hlogScale hcut)

/-- Every odd prime above `P(1411732827)` has a prime Fermat-quotient witness
at most `(log p)^1.83`. The 150/82 cutoff uses the free finite-fiber count,
and the explicit smooth-count margins are verified at double-log threshold
53000000. -/
theorem exists_prime_pow_ne_one_183_100 {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 1411732827 ≤ p) :
    ∃ q : ℕ,
      q.Prime ∧ (q : ℝ) ≤ (Real.log p) ^ (183 / 100 : ℝ) ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  have hp := (Fact.out : p.Prime).pos
  have hLp : 0 < Real.log p := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hz := le_log_log_53000000 (by norm_num only : 76598623 ≤ 1411732827) hlarge
  have hlogLower := Analysis.pow_10_12_le_of_log_ge_53000000 hLp hz
  have hL1 : 1 < Real.log p := by linarith only [hlogLower]
  have hLge : 1 ≤ Real.log p := le_of_lt hL1
  have hpow : Real.log p ≤ (Real.log p) ^ (183 / 100 : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hLge (by norm_num only : (1 : ℝ) ≤ 183 / 100)
  have hB : 64 ^ 4 ≤ Nat.floor ((Real.log p) ^ (183 / 100 : ℝ)) := by
    apply Nat.le_floor
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    nlinarith only [hlogLower, hpow]
  have hC : 0 < Nat.floor ((p : ℝ) ^ (4147 / 5000 : ℝ)) :=
    Nat.lt_of_lt_of_le (by decide : 0 < 1)
      (Nat.le_floor
        (by
          simpa only [Nat.cast_one] using
            Real.one_le_rpow (Nat.one_le_cast.mpr (Nat.succ_le_of_lt hp))
              (by norm_num only : (0 : ℝ) ≤ 4147 / 5000)))
  have hcL : 2 * (2499 / 2500 : ℝ) ≤ Real.log (Real.log p) := by nlinarith only [hz]
  have hgap :=
    Analysis.smooth_scale_gap_of_log_lower_bound hlogLower hz
      (by norm_num only : (0 : ℝ) < 53000000) (by norm_num only : (0 : ℝ) ≤ 183 / 100)
      (by norm_num only : (2499 / 2500 : ℝ) * (183 / 100) + (183 / 100) * (2 / 53000000) < 75 / 41)
  have hpowergap :
    32 * Real.log (Real.log p) ≤ (Real.log p) ^ ((183 / 100 : ℝ) - 1829999 / 1000000) := by
    have hexp := Analysis.thirty_two_mul_le_exp_gap_half_million hz
    have hmono :
      Real.exp (Real.log (Real.log p) * (1 / 2000000 : ℝ)) ≤
        Real.exp (Real.log (Real.log p) * ((183 / 100 : ℝ) - 1829999 / 1000000)) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hz]
    have hrpow :
      Real.exp (Real.log (Real.log p) * ((183 / 100 : ℝ) - 1829999 / 1000000)) =
        (Real.log p) ^ ((183 / 100 : ℝ) - 1829999 / 1000000) := by
      rw [Real.rpow_def_of_pos hLp]
    exact (hexp.trans hmono).trans_eq hrpow
  have hMp :=
    NumberTheory.two_mul_rpow_le_primeCounting_floor_of_gap (L := Real.log p) (A := 183 / 100) (b :=
      1829999 / 1000000) hL1 (by norm_num only) (by norm_num only) hB hpowergap
  have hlogC :
    Real.log (Nat.floor ((p : ℝ) ^ (4147 / 5000 : ℝ))) ≤ (4147 / 5000 : ℝ) * Real.log p := by
    have h :=
      Real.log_le_log (Nat.cast_pos.mpr hC) (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg p) _))
    rw [Real.log_rpow (Nat.cast_pos.mpr hp)] at h
    exact h
  have hBpos : 0 < Nat.floor ((Real.log p) ^ (183 / 100 : ℝ)) :=
    Nat.lt_of_lt_of_le (by decide : 0 < 64 ^ 4) hB
  have hgap' :
    2499 / 2500 * (183 / 100 : ℝ) * Real.log p + (183 / 100 : ℝ) * Real.log (Real.log p) <
      (150 / 82 : ℝ) * Real.log p := by
    rw [show (75 / 41 : ℝ) = 150 / 82 by norm_num only] at hgap
    exact hgap
  exact
    exists_prime_pow_ne_one_fiber_150_82 hodd hlarge (by linarith only [hlogLower]) hBpos hC hcL hMp
      hgap' hlogC
      (fun k hcut ↦ Analysis.rational_cutoff_150_82_le_prime_mul_floor hp hlogLower hcut)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only : (4147 / 5000 : ℝ) < (2499 / 2500) * ((1829999 / 1000000 : ℝ) - 1))

/-- Every odd prime above `P(1411732827)` has a prime Fermat-quotient witness
at most `(log p)^1.8297`. The 75/41 finite-fiber interval is squared to the
150/82 scale used by the smooth-count estimate. -/
theorem exists_prime_pow_ne_one_18297_10000 {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 1411732827 ≤ p) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log p) ^ (18297 / 10000 : ℝ) ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  have hp := (Fact.out : p.Prime).pos
  have hLp : 0 < Real.log p := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hz := le_log_log_53000000 (by norm_num only : 76598623 ≤ 1411732827) hlarge
  have hlogLower := Analysis.pow_10_12_le_of_log_ge_53000000 hLp hz
  have hL1 : 1 < Real.log p := by linarith only [hlogLower]
  have hLge : 1 ≤ Real.log p := le_of_lt hL1
  have hpow : Real.log p ≤ (Real.log p) ^ (18297 / 10000 : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hLge (by norm_num only : (1 : ℝ) ≤ 18297 / 10000)
  have hB : 64 ^ 4 ≤ Nat.floor ((Real.log p) ^ (18297 / 10000 : ℝ)) := by
    apply Nat.le_floor
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    nlinarith only [hlogLower, hpow]
  have hC : 0 < Nat.floor ((p : ℝ) ^ (4147 / 5000 : ℝ)) :=
    Nat.lt_of_lt_of_le (by decide : 0 < 1)
      (Nat.le_floor
        (by
          simpa only [Nat.cast_one] using
            Real.one_le_rpow (Nat.one_le_cast.mpr (Nat.succ_le_of_lt hp))
              (by norm_num only : (0 : ℝ) ≤ 4147 / 5000)))
  have hcL : 2 * (9997 / 10000 : ℝ) ≤ Real.log (Real.log p) := by nlinarith only [hz]
  have hgap :=
    Analysis.smooth_scale_gap_of_log_lower_bound hlogLower hz
      (by norm_num only : (0 : ℝ) < 53000000) (by norm_num only : (0 : ℝ) ≤ 18297 / 10000)
      (by norm_num only :
        (9997 / 10000 : ℝ) * (18297 / 10000) + (18297 / 10000) * (2 / 53000000) < 75 / 41)
  have hpowergap :
    32 * Real.log (Real.log p) ≤ (Real.log p) ^ ((18297 / 10000 : ℝ) - 182966 / 100000) := by
    have hexp := Analysis.thirty_two_mul_le_exp_gap_half_million hz
    have hmono :
      Real.exp (Real.log (Real.log p) * (1 / 2000000 : ℝ)) ≤
        Real.exp (Real.log (Real.log p) * (1 / 25000 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hz]
    have hrpow :
      Real.exp (Real.log (Real.log p) * (1 / 25000 : ℝ)) =
        (Real.log p) ^ ((18297 / 10000 : ℝ) - 182966 / 100000) := by
      rw [Real.rpow_def_of_pos hLp]
      congr 1
      norm_num only
    exact (hexp.trans hmono).trans_eq hrpow
  have hMp :=
    NumberTheory.two_mul_rpow_le_primeCounting_floor_of_gap (L := Real.log p) (A := 18297 / 10000)
      (b := 182966 / 100000) hL1 (by norm_num only) (by norm_num only) hB hpowergap
  have hlogC :
    Real.log (Nat.floor ((p : ℝ) ^ (4147 / 5000 : ℝ))) ≤ (4147 / 5000 : ℝ) * Real.log p := by
    have h :=
      Real.log_le_log (Nat.cast_pos.mpr hC) (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg p) _))
    rw [Real.log_rpow (Nat.cast_pos.mpr hp)] at h
    exact h
  obtain ⟨k, hk, _, hlo, hhi, hcount⟩ := exists_fiber_interval_bound_75_41_free hodd hlarge
  have hlo82 : p ^ 150 ≤ k ^ 82 := by
    have h := Nat.pow_le_pow_left hlo 2
    simpa only [← pow_mul] using h
  have hhi82 : k ^ 82 ≤ 2 ^ 82 * p ^ 150 := by
    have h := Nat.pow_le_pow_left hhi 2
    rw [mul_pow] at h
    simpa only [← pow_mul] using h
  have hgap' :
    (9997 / 10000 : ℝ) * (18297 / 10000 : ℝ) * Real.log p +
        (18297 / 10000 : ℝ) * Real.log (Real.log p) <
      (150 / 82 : ℝ) * Real.log p := by
    rw [show (75 / 41 : ℝ) = 150 / 82 by norm_num only] at hgap
    exact hgap
  have hscale :
    ∀ k' : ℕ,
      k' ^ 82 ≤ 2 ^ 82 * p ^ 150 → 256 * k' ≤ p * Nat.floor ((p : ℝ) ^ (4147 / 5000 : ℝ)) := by
    intro k' hcut
    exact Analysis.rational_cutoff_150_82_le_prime_mul_floor hp hlogLower hcut
  exact
    exists_prime_pow_ne_one_fiber_150_82 hodd hlarge (by linarith only [hlogLower])
      (Nat.lt_of_lt_of_le (by decide : 0 < 64 ^ 4) hB) hC hcL hMp hgap' hlogC hscale
      (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only : (4147 / 5000 : ℝ) < (9997 / 10000) * ((182966 / 100000 : ℝ) - 1))

/-- Every odd prime above `P(1411732827)` has a prime Fermat-quotient witness
at most `(log p)^1.82927`. A finer smooth-count exponent and the generic
150/82 floor budget sharpen the 75/41 finite-fiber estimate. -/
theorem exists_prime_pow_ne_one_182927_100000 {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 1411732827 ≤ p) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log p) ^ (182927 / 100000 : ℝ) ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  have hp := (Fact.out : p.Prime).pos
  have hLp : 0 < Real.log p := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hz := le_log_log_53000000 (by norm_num only : 76598623 ≤ 1411732827) hlarge
  have hlogLower := Analysis.pow_10_12_le_of_log_ge_53000000 hLp hz
  have hL1 : 1 < Real.log p := by linarith only [hlogLower]
  have hLge : 1 ≤ Real.log p := le_of_lt hL1
  have hpow : Real.log p ≤ (Real.log p) ^ (182927 / 100000 : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hLge (by norm_num only : (1 : ℝ) ≤ 182927 / 100000)
  have hB : 64 ^ 4 ≤ Nat.floor ((Real.log p) ^ (182927 / 100000 : ℝ)) := by
    apply Nat.le_floor
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    nlinarith only [hlogLower, hpow]
  have hC : 0 < Nat.floor ((p : ℝ) ^ (8292684 / 10000000 : ℝ)) :=
    Nat.lt_of_lt_of_le (by decide : 0 < 1)
      (Nat.le_floor
        (by
          simpa only [Nat.cast_one] using
            Real.one_le_rpow (Nat.one_le_cast.mpr (Nat.succ_le_of_lt hp))
              (by norm_num only : (0 : ℝ) ≤ 8292684 / 10000000)))
  have hcL : 2 * (999999 / 1000000 : ℝ) ≤ Real.log (Real.log p) := by nlinarith only [hz]
  have hgap :=
    Analysis.smooth_scale_gap_of_log_lower_bound (L := Real.log p) (A := 182927 / 100000) (rho :=
      999999 / 1000000) (z0 := 53000000) (kappa := 75 / 41) hlogLower hz
      (by norm_num only : (0 : ℝ) < 53000000) (by norm_num only : (0 : ℝ) ≤ 182927 / 100000)
      (by norm_num only :
        (999999 / 1000000 : ℝ) * (182927 / 100000) + (182927 / 100000 : ℝ) * (2 / 53000000) <
          75 / 41)
  have hpowergap :
    32 * Real.log (Real.log p) ≤ (Real.log p) ^ ((182927 / 100000 : ℝ) - 18292695 / 10000000) := by
    have hexp := Analysis.thirty_two_mul_le_exp_gap_half_million hz
    have hrpow :
      Real.exp (Real.log (Real.log p) * (1 / 2000000 : ℝ)) =
        (Real.log p) ^ ((182927 / 100000 : ℝ) - 18292695 / 10000000) := by
      rw [Real.rpow_def_of_pos hLp]
      congr 1
      norm_num only
    exact hexp.trans_eq hrpow
  have hMp :=
    NumberTheory.two_mul_rpow_le_primeCounting_floor_of_gap (L := Real.log p) (A := 182927 / 100000)
      (b := 18292695 / 10000000) hL1 (by norm_num only) (by norm_num only) hB hpowergap
  have hlogC :
    Real.log (Nat.floor ((p : ℝ) ^ (8292684 / 10000000 : ℝ))) ≤
      (8292684 / 10000000 : ℝ) * Real.log p := by
    have h :=
      Real.log_le_log (Nat.cast_pos.mpr hC) (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg p) _))
    rw [Real.log_rpow (Nat.cast_pos.mpr hp)] at h
    exact h
  obtain ⟨k, hk, _, hlo, hhi, hcount⟩ := exists_fiber_interval_bound_75_41_free hodd hlarge
  have hlo82 : p ^ 150 ≤ k ^ 82 := by
    have h := Nat.pow_le_pow_left hlo 2
    simpa only [← pow_mul] using h
  have hhi82 : k ^ 82 ≤ 2 ^ 82 * p ^ 150 := by
    have h := Nat.pow_le_pow_left hhi 2
    rw [mul_pow] at h
    simpa only [← pow_mul] using h
  have hgap' :
    (999999 / 1000000 : ℝ) * (182927 / 100000 : ℝ) * Real.log p +
        (182927 / 100000 : ℝ) * Real.log (Real.log p) <
      (150 / 82 : ℝ) * Real.log p := by
    rw [show (75 / 41 : ℝ) = 150 / 82 by norm_num only] at hgap
    exact hgap
  have hscale :
    ∀ k' : ℕ,
      k' ^ 82 ≤ 2 ^ 82 * p ^ 150 →
        256 * k' ≤ p * Nat.floor ((p : ℝ) ^ (8292684 / 10000000 : ℝ)) := by
    intro k' hcut
    exact Analysis.cutoff_150_82_le_prime_mul_floor hp hlogLower (by norm_num only) hcut
  exact
    exists_prime_pow_ne_one_fiber_150_82 hodd hlarge (by linarith only [hlogLower])
      (Nat.lt_of_lt_of_le (by decide : 0 < 64 ^ 4) hB) hC hcL hMp hgap' hlogC hscale
      (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only :
        (8292684 / 10000000 : ℝ) < (999999 / 1000000) * ((18292695 / 10000000 : ℝ) - 1))

/-- Every odd prime above `P(4,217,312,731)` has a prime Fermat-quotient
witness at most `(ln p)^(1.82861)`. The 192/105 finite-fiber interval and
the displayed prime-count and smooth-product margins give this bound. -/
theorem exists_prime_pow_ne_one_182861_100000 {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 4217312731 ≤ p) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log p) ^ (182861 / 100000 : ℝ) ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  have hp := (Fact.out : p.Prime).pos
  have hLp : 0 < Real.log p := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hz := le_log_log_53000000 (by norm_num only : 76598623 ≤ 4217312731) hlarge
  have hlogLower := Analysis.pow_10_12_le_of_log_ge_53000000 hLp hz
  have hL : 2 ≤ Real.log p := by linarith only [hlogLower]
  have hL1 : 1 < Real.log p := by linarith only [hL]
  have hLge : 1 ≤ Real.log p := le_of_lt hL1
  have hpow : Real.log p ≤ (Real.log p) ^ (182861 / 100000 : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hLge (by norm_num only : (1 : ℝ) ≤ 182861 / 100000)
  have hB : 64 ^ 4 ≤ Nat.floor ((Real.log p) ^ (182861 / 100000 : ℝ)) := by
    apply Nat.le_floor
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    nlinarith only [hlogLower, hpow]
  have hBpos : 0 < Nat.floor ((Real.log p) ^ (182861 / 100000 : ℝ)) :=
    Nat.lt_of_lt_of_le (by norm_num only : 0 < 64 ^ 4) hB
  have hC : 0 < Nat.floor ((p : ℝ) ^ (828579 / 1000000 : ℝ)) :=
    Nat.lt_of_lt_of_le (by decide : 0 < 1)
      (Nat.le_floor
        (by
          simpa only [Nat.cast_one] using
            Real.one_le_rpow (Nat.one_le_cast.mpr (Nat.succ_le_of_lt hp))
              (by norm_num only : (0 : ℝ) ≤ 828579 / 1000000)))
  have hcL : 2 * (999977 / 1000000 : ℝ) ≤ Real.log (Real.log p) := by nlinarith only [hz]
  have hgap :=
    Analysis.smooth_scale_gap_of_log_lower_bound (L := Real.log p) (A := 182861 / 100000) (rho :=
      999977 / 1000000) (z0 := 53000000) (kappa := 192 / 105) hlogLower hz
      (by norm_num only : (0 : ℝ) < 53000000) (by norm_num only : (0 : ℝ) ≤ 182861 / 100000)
      (by norm_num only :
        (999977 / 1000000 : ℝ) * (182861 / 100000) + (182861 / 100000 : ℝ) * (2 / 53000000) <
          192 / 105)
  have hpowergap :
    32 * Real.log (Real.log p) ≤ (Real.log p) ^ ((182861 / 100000 : ℝ) - 182860 / 100000) := by
    have hexp :=
      Analysis.mul_32_le_exp_gap_14_d7 ((by norm_num only : (14900000 : ℝ) ≤ 53000000).trans hz)
    rw [Real.rpow_def_of_pos hLp]
    calc
      32 * Real.log (Real.log p) ≤ Real.exp (Real.log (Real.log p) * (14 / 10000000 : ℝ)) := hexp
      _ ≤ Real.exp (Real.log (Real.log p) * (1 / 100000 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [hz]
      _ = _ := by
        congr 1; norm_num only
  have hMp :=
    NumberTheory.two_mul_rpow_le_primeCounting_floor_of_gap (L := Real.log p) (A := 182861 / 100000)
      (b := 182860 / 100000) hL1 (by norm_num only) (by norm_num only) hB hpowergap
  have hlogC :
    Real.log (Nat.floor ((p : ℝ) ^ (828579 / 1000000 : ℝ))) ≤
      (828579 / 1000000 : ℝ) * Real.log p := by
    have h :=
      Real.log_le_log (Nat.cast_pos.mpr hC) (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg p) _))
    rw [Real.log_rpow (Nat.cast_pos.mpr hp)] at h
    exact h
  obtain ⟨k, hk, _, hlo, hhi, hcount⟩ := exists_fiber_interval_bound_192_105_free hodd hlarge
  have hgap' :
    (999977 / 1000000 : ℝ) * (182861 / 100000) * Real.log p +
        (182861 / 100000 : ℝ) * Real.log (Real.log p) <
      (192 / 105 : ℝ) * Real.log p :=
    hgap
  have hscale :
    ∀ k' : ℕ,
      k' ^ 105 ≤ 2 ^ 105 * p ^ 192 →
        256 * k' ≤ p * Nat.floor ((p : ℝ) ^ (828579 / 1000000 : ℝ)) := by
    intro k' hcut
    exact Analysis.cutoff_192_105_le_prime_mul_floor hp hlogLower (by norm_num only) hcut
  have hsmooth :=
    smooth_count_at_rational_cutoff_of_log_bounds (a := 105) (t := 192) (A := 182861 / 100000) (b :=
      182860 / 100000) (c := 999977 / 1000000) (beta := 828579 / 1000000) (by norm_num only) hp
      hBpos hC hk hL (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only) hcL
      hMp (Nat.floor_le (Real.rpow_nonneg (by linarith only [hL]) _)) hgap' hlogC (hscale _ hhi) hlo
  obtain ⟨q, hq, hqy, hpowq⟩ := exists_prime_pow_ne_one_of_interval_smooth hcount hsmooth
  exact
    ⟨q, hq,
      (Nat.cast_le.mpr (Nat.lt_add_one_iff.mp hqy)).trans
        (Nat.floor_le (Real.rpow_nonneg (by linarith only [hL]) _)),
      hpowq⟩

/-- Every odd prime above `P(21518759)` has a prime Fermat-quotient witness
at most `(log p)^1.900003`. The free 10/19 finite-fiber bound and explicit
smooth-count margins apply from double-log threshold 14900000. -/
theorem exists_prime_pow_ne_one_1900003_1000000 {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 21518759 ≤ p) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log p) ^ (1900003 / 1000000 : ℝ) ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  have hp := (Fact.out : p.Prime).pos
  have hLp : 0 < Real.log p := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hz := le_log_log_14900000 (Nat.le_refl 21518759) hlarge
  have hlogLower := Analysis.pow_10_12_le_of_log_ge_14900000 hLp hz
  have hlogScale := Analysis.pow_10_20_le_of_log_ge_14900000 hLp hz
  have hL : 2 ≤ Real.log p := by linarith only [hlogLower]
  have hLge : 1 ≤ Real.log p := le_trans (by norm_num only : (1 : ℝ) ≤ 2) hL
  have hpow : Real.log p ≤ (Real.log p) ^ (1900003 / 1000000 : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hLge (by norm_num only : (1 : ℝ) ≤ 1900003 / 1000000)
  have hB : 64 ^ 4 ≤ Nat.floor ((Real.log p) ^ (1900003 / 1000000 : ℝ)) := by
    apply Nat.le_floor
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    nlinarith only [hlogLower, hpow]
  have hC : 0 < Nat.floor ((p : ℝ) ^ (900000000000000001 / 1000000000000000000 : ℝ)) :=
    Nat.lt_of_lt_of_le (by decide : 0 < 1)
      (Nat.le_floor
        (by
          simpa only [Nat.cast_one] using
            Real.one_le_rpow (Nat.one_le_cast.mpr (Nat.succ_le_of_lt hp))
              (by norm_num only : (0 : ℝ) ≤ 900000000000000001 / 1000000000000000000)))
  have hcL : 2 * (99999825 / 100000000 : ℝ) ≤ Real.log (Real.log p) := by nlinarith only [hz]
  have hgap :=
    Analysis.smooth_scale_19_10_gap_of_log_lower_bound hlogLower hz
      (by norm_num only : (0 : ℝ) < 14900000) (by norm_num only : (0 : ℝ) ≤ 1900003 / 1000000)
      (by norm_num only :
        (99999825 / 100000000 : ℝ) * (1900003 / 1000000) + (1900003 / 1000000) * (2 / 14900000) <
          19 / 10)
  have hpowergap :
    32 * Real.log (Real.log p) ≤
      (Real.log p) ^ ((1900003 / 1000000 : ℝ) - 19000016 / 10000000) := by
    rw [show (1900003 / 1000000 : ℝ) - 19000016 / 10000000 = 14 / 10000000 by norm_num only]
    rw [Real.rpow_def_of_pos hLp]
    simpa only [mul_comm] using Analysis.mul_32_le_exp_gap_14_d7 hz
  have hMp :=
    NumberTheory.two_mul_rpow_le_primeCounting_floor_of_gap (L := Real.log p) (A :=
      1900003 / 1000000) (b := 19000016 / 10000000) (by linarith only [hlogLower])
      (by norm_num only) (by norm_num only) hB hpowergap
  have hlogC :
    Real.log (Nat.floor ((p : ℝ) ^ (900000000000000001 / 1000000000000000000 : ℝ))) ≤
      (900000000000000001 / 1000000000000000000 : ℝ) * Real.log p := by
    have h :=
      Real.log_le_log (Nat.cast_pos.mpr hC) (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg p) _))
    rw [Real.log_rpow (Nat.cast_pos.mpr hp)] at h
    exact h
  exact
    exists_prime_pow_ne_one_fiber_10_19 hodd hlarge hL
      (Nat.lt_of_lt_of_le (by decide : 0 < 64 ^ 4) hB) hC hcL hMp hgap hlogC
      (fun k hcut ↦ Analysis.rational_cutoff_19_10_le_prime_mul_floor hp hlogScale hcut)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only :
        (900000000000000001 / 1000000000000000000 : ℝ) <
          (99999825 / 100000000 : ℝ) * ((19000016 / 10000000 : ℝ) - 1))

/-- Inputs: an odd prime `p ≥ P(21518759)`.
Claim: A prime `q ≤ (log p)^(1876/1000)` has nontrivial `(p - 1)`-st power
modulo `p^2`. Content: The 30/16 finite-fiber branch uses double-log threshold
14,900,000 and the explicit smooth-number margins. Proof: Establish prime
supply, smooth-count, and cutoff inequalities, then apply the interval
extraction theorem. Role: Provides the Fermat witness used by the public
Miller–Rabin bound for nonsquarefree odd inputs. -/
theorem exists_prime_pow_ne_one_1876_1000 {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 21518759 ≤ p) :
    ∃ q : ℕ,
      q.Prime ∧ (q : ℝ) ≤ (Real.log p) ^ (1876 / 1000 : ℝ) ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  have hp := (Fact.out : p.Prime).pos
  have hLp : 0 < Real.log p := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hz := le_log_log_14900000 (by norm_num only : 21518759 ≤ 21518759) hlarge
  have hlogLower := Analysis.pow_10_12_le_of_log_ge_14900000 hLp hz
  have hL : 2 ≤ Real.log p := by linarith only [hlogLower]
  have hLge : 1 ≤ Real.log p := le_trans (by norm_num only : (1 : ℝ) ≤ 2) hL
  have hB : 64 ^ 4 ≤ Nat.floor ((Real.log p) ^ (1876 / 1000 : ℝ)) := by
    apply Nat.le_floor
    have hpow :=
      Real.rpow_le_rpow_of_exponent_le hLge (by norm_num only : (1 : ℝ) ≤ (1876 / 1000 : ℝ))
    have hpow' : Real.log p ≤ (Real.log p) ^ (1876 / 1000 : ℝ) := by
      simpa only [Real.rpow_one] using hpow
    norm_num only [Nat.cast_pow]
    nlinarith only [hlogLower, hpow']
  have hC : 0 < Nat.floor ((p : ℝ) ^ (87501 / 100000 : ℝ)) :=
    Nat.lt_of_lt_of_le (by decide : 0 < 1)
      (Nat.le_floor
        (by
          simpa only [Nat.cast_one] using
            Real.one_le_rpow (Nat.one_le_cast.mpr (Nat.succ_le_of_lt hp))
              (by norm_num only : (0 : ℝ) ≤ 87501 / 100000)))
  have hcL : 2 * (999 / 1000 : ℝ) ≤ Real.log (Real.log p) := by nlinarith only [hz]
  have hexp := Analysis.mul_32_le_exp_gap_14_d7 hz
  have hpowergap :
    32 * Real.log (Real.log p) ≤ (Real.log p) ^ ((1876 / 1000 : ℝ) - (18759 / 10000 : ℝ)) := by
    rw [Real.rpow_def_of_pos hLp]
    calc
      _ ≤ Real.exp (Real.log (Real.log p) * (14 / 10000000 : ℝ)) := hexp
      _ ≤ Real.exp (Real.log (Real.log p) * ((1876 / 1000 : ℝ) - (18759 / 10000 : ℝ))) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [hz]
      _ = _ := by congr 1
  have hMp :=
    NumberTheory.two_mul_rpow_le_primeCounting_floor_of_gap (L := Real.log p) (A := 1876 / 1000)
      (b := 18759 / 10000) (by linarith only [hlogLower]) (by norm_num only) (by norm_num only) hB
      hpowergap
  have hgap :=
    Analysis.smooth_scale_gap_of_log_lower_bound hlogLower hz
      (by norm_num only : (0 : ℝ) < 14900000) (by norm_num only : (0 : ℝ) ≤ 1876 / 1000)
      (by norm_num only :
        (999 / 1000 : ℝ) * (1876 / 1000) + (1876 / 1000) * (2 / 14900000) < 15 / 8)
  have hgap' :
    (999 / 1000 : ℝ) * (1876 / 1000) * Real.log p + (1876 / 1000) * Real.log (Real.log p) <
      (30 / 16 : ℝ) * Real.log p := by
    rw [show (30 / 16 : ℝ) = 15 / 8 by norm_num only]
    exact hgap
  have hlogC :
    Real.log (Nat.floor ((p : ℝ) ^ (87501 / 100000 : ℝ))) ≤ (87501 / 100000 : ℝ) * Real.log p := by
    have h :=
      Real.log_le_log (Nat.cast_pos.mpr hC) (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg p) _))
    rw [Real.log_rpow (Nat.cast_pos.mpr hp)] at h
    exact h
  exact
    exists_prime_pow_ne_one_fiber_30_16 hodd hlarge hL
      (Nat.lt_of_lt_of_le (by decide : 0 < 64 ^ 4) hB) hC hcL hMp hgap' hlogC
      (fun k hcut ↦ Analysis.rational_cutoff_30_16_le_prime_mul_floor hp hlogLower hcut)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only : (87501 / 100000 : ℝ) < (999 / 1000 : ℝ) * ((18759 / 10000 : ℝ) - 1))

/-- Every odd prime `p ≥ P(21518759)` has a prime Fermat-quotient witness
at most `(log p)^(1868/1000)`. The 28/15 finite-fiber bound and explicit
smooth-count margins apply from double-log threshold 14,900,000. -/
theorem exists_prime_pow_ne_one_1868_1000 {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 21518759 ≤ p) :
    ∃ q : ℕ,
      q.Prime ∧ (q : ℝ) ≤ (Real.log p) ^ (1868 / 1000 : ℝ) ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  have hp := (Fact.out : p.Prime).pos
  have hLp : 0 < Real.log p := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hz := le_log_log_14900000 (by norm_num only : 21518759 ≤ 21518759) hlarge
  have hlogLower := Analysis.pow_10_12_le_of_log_ge_14900000 hLp hz
  have hL : 2 ≤ Real.log p := by linarith only [hlogLower]
  have hLge : 1 ≤ Real.log p := le_trans (by norm_num only : (1 : ℝ) ≤ 2) hL
  have hB : 64 ^ 4 ≤ Nat.floor ((Real.log p) ^ (1868 / 1000 : ℝ)) := by
    apply Nat.le_floor
    have hpow :=
      Real.rpow_le_rpow_of_exponent_le hLge (by norm_num only : (1 : ℝ) ≤ (1868 / 1000 : ℝ))
    have hpow' : Real.log p ≤ (Real.log p) ^ (1868 / 1000 : ℝ) := by
      simpa only [Real.rpow_one] using hpow
    norm_num only [Nat.cast_pow]
    nlinarith only [hlogLower, hpow']
  have hC : 0 < Nat.floor ((p : ℝ) ^ (8668 / 10000 : ℝ)) :=
    Nat.lt_of_lt_of_le (by decide : 0 < 1)
      (Nat.le_floor
        (by
          simpa only [Nat.cast_one] using
            Real.one_le_rpow (Nat.one_le_cast.mpr (Nat.succ_le_of_lt hp))
              (by norm_num only : (0 : ℝ) ≤ 8668 / 10000)))
  have hcL : 2 * (999 / 1000 : ℝ) ≤ Real.log (Real.log p) := by nlinarith only [hz]
  have hpowergap :
    32 * Real.log (Real.log p) ≤ (Real.log p) ^ ((1868 / 1000 : ℝ) - (18678 / 10000 : ℝ)) := by
    rw [Real.rpow_def_of_pos hLp]
    calc
      _ ≤ Real.exp (Real.log (Real.log p) * (14 / 10000000 : ℝ)) :=
        Analysis.mul_32_le_exp_gap_14_d7 hz
      _ ≤ Real.exp (Real.log (Real.log p) * ((1868 / 1000 : ℝ) - (18678 / 10000 : ℝ))) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [hz]
      _ = _ := by congr 1
  have hMp :=
    NumberTheory.two_mul_rpow_le_primeCounting_floor_of_gap (L := Real.log p) (A := 1868 / 1000)
      (b := 18678 / 10000) (by linarith only [hlogLower]) (by norm_num only) (by norm_num only) hB
      hpowergap
  have hgap :=
    Analysis.smooth_scale_gap_of_log_lower_bound hlogLower hz
      (by norm_num only : (0 : ℝ) < 14900000) (by norm_num only : (0 : ℝ) ≤ 1868 / 1000)
      (by norm_num only :
        (999 / 1000 : ℝ) * (1868 / 1000) + (1868 / 1000 : ℝ) * (2 / 14900000) < 28 / 15)
  have hlogC :
    Real.log (Nat.floor ((p : ℝ) ^ (8668 / 10000 : ℝ))) ≤ (8668 / 10000 : ℝ) * Real.log p := by
    have h :=
      Real.log_le_log (Nat.cast_pos.mpr hC) (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg p) _))
    rw [Real.log_rpow (Nat.cast_pos.mpr hp)] at h
    exact h
  exact
    exists_prime_pow_ne_one_fiber_28_15 (u := 21518759) hodd
      (by norm_num only : 17431511 ≤ 21518759) hlarge hL
      (Nat.lt_of_lt_of_le (by decide : 0 < 64 ^ 4) hB) hC hcL hMp hgap hlogC
      (fun k hcut ↦ Analysis.rational_cutoff_28_15_le_prime_mul_floor hp hlogLower hcut)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only : (8668 / 10000 : ℝ) < (999 / 1000 : ℝ) * ((18678 / 10000 : ℝ) - 1))

/-- Every odd prime `p ≥ P(21518759)` has a prime Fermat-quotient witness
at most `(log p)^(18666701/10000000)`. Retain the 28/15 cutoff and sharpen the
prime-counting exponent while preserving the 14,900,000 double-log range. -/
theorem exists_prime_pow_ne_one_18666701_d7 {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hlarge : explicitFiniteFiberPrimeThreshold 21518759 ≤ p) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log p) ^ (18666701 / 10000000 : ℝ) ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  have hp := (Fact.out : p.Prime).pos
  have hLp : 0 < Real.log p := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hz := le_log_log_14900000 (by norm_num only : 21518759 ≤ 21518759) hlarge
  have hlogLower := Analysis.pow_10_12_le_of_log_ge_14900000 hLp hz
  have hL : 2 ≤ Real.log p := by linarith only [hlogLower]
  have hLge : 1 ≤ Real.log p := le_trans (by norm_num only : (1 : ℝ) ≤ 2) hL
  have hB : 64 ^ 4 ≤ Nat.floor ((Real.log p) ^ (18666701 / 10000000 : ℝ)) := by
    apply Nat.le_floor
    have hpow :=
      Real.rpow_le_rpow_of_exponent_le hLge (by norm_num only : (1 : ℝ) ≤ (18666701 / 10000000 : ℝ))
    have hpow' : Real.log p ≤ (Real.log p) ^ (18666701 / 10000000 : ℝ) := by
      simpa only [Real.rpow_one] using hpow
    norm_num only [Nat.cast_pow]
    nlinarith only [hlogLower, hpow']
  have hC : 0 < Nat.floor ((p : ℝ) ^ (8666667 / 10000000 : ℝ)) :=
    Nat.lt_of_lt_of_le (by decide : 0 < 1)
      (Nat.le_floor
        (by
          simpa only [Nat.cast_one] using
            Real.one_le_rpow (Nat.one_le_cast.mpr (Nat.succ_le_of_lt hp))
              (by norm_num only : (0 : ℝ) ≤ 8666667 / 10000000)))
  have hcL : 2 * (499999 / 500000 : ℝ) ≤ Real.log (Real.log p) := by nlinarith only [hz]
  have hpowergap :
    32 * Real.log (Real.log p) ≤
      (Real.log p) ^ ((18666701 / 10000000 : ℝ) - (18666686 / 10000000 : ℝ)) := by
    rw [Real.rpow_def_of_pos hLp]
    calc
      _ ≤ Real.exp (Real.log (Real.log p) * (14 / 10000000 : ℝ)) :=
        Analysis.mul_32_le_exp_gap_14_d7 hz
      _ ≤
          Real.exp
            (Real.log (Real.log p) * ((18666701 / 10000000 : ℝ) - (18666686 / 10000000 : ℝ))) :=
        by
        apply Real.exp_le_exp.mpr
        nlinarith only [hz]
      _ = _ := by congr 1
  have hMp :=
    NumberTheory.two_mul_rpow_le_primeCounting_floor_of_gap (L := Real.log p) (A :=
      18666701 / 10000000) (b := 18666686 / 10000000) (by linarith only [hlogLower])
      (by norm_num only) (by norm_num only) hB hpowergap
  have hgap :=
    Analysis.smooth_scale_gap_of_log_lower_bound hlogLower hz
      (by norm_num only : (0 : ℝ) < 14900000) (by norm_num only : (0 : ℝ) ≤ 18666701 / 10000000)
      (by norm_num only :
        (499999 / 500000 : ℝ) * (18666701 / 10000000) +
            (18666701 / 10000000 : ℝ) * (2 / 14900000 : ℝ) <
          28 / 15)
  have hlogC :
    Real.log (Nat.floor ((p : ℝ) ^ (8666667 / 10000000 : ℝ))) ≤
      (8666667 / 10000000 : ℝ) * Real.log p := by
    have h :=
      Real.log_le_log (Nat.cast_pos.mpr hC) (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg p) _))
    rw [Real.log_rpow (Nat.cast_pos.mpr hp)] at h
    exact h
  exact
    exists_prime_pow_ne_one_fiber_28_15 (u := 21518759) hodd
      (by norm_num only : 17431511 ≤ 21518759) hlarge hL
      (Nat.lt_of_lt_of_le (by decide : 0 < 64 ^ 4) hB) hC hcL hMp hgap hlogC
      (fun k hcut ↦ Analysis.rational_cutoff_28_15_le_prime_mul_floor_beta hp hlogLower hcut)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only :
        (8666667 / 10000000 : ℝ) < (499999 / 500000 : ℝ) * ((18666686 / 10000000 : ℝ) - 1))

/-- Inputs: an odd prime `p≥P(u)` with `u≥17,431,511`.
Claim: a prime q≤(log p)^(1.8666703) has nontrivial `(p-1)`-st power modulo
p². Use the 12,082,601 double-log bound, the 28/15 cutoff, and the sharper
prime-counting gap. Role: supplies the Fermat witness for the lower-start MR
branch. -/
theorem exists_prime_pow_ne_one_18666703_d7 {p u : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hu : 17431511 ≤ u) (hlarge : explicitFiniteFiberPrimeThreshold u ≤ p) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log p) ^ (18666703 / 10000000 : ℝ) ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  have hp := (Fact.out : p.Prime).pos
  have hLp : 0 < Real.log p := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hz := le_log_log_12082601 hu hlarge
  have hlogLower := Analysis.pow_10_12_le_of_log_ge_12082601 hLp hz
  have hL : 2 ≤ Real.log p := by linarith only [hlogLower]
  have hLge : 1 ≤ Real.log p := le_trans (by norm_num only : (1 : ℝ) ≤ 2) hL
  have hB : 64 ^ 4 ≤ Nat.floor ((Real.log p) ^ (18666703 / 10000000 : ℝ)) := by
    apply Nat.le_floor
    have hpow :=
      Real.rpow_le_rpow_of_exponent_le hLge (by norm_num only : (1 : ℝ) ≤ (18666703 / 10000000 : ℝ))
    have hpow' : Real.log p ≤ (Real.log p) ^ (18666703 / 10000000 : ℝ) := by
      simpa only [Real.rpow_one] using hpow
    norm_num only [Nat.cast_pow]
    nlinarith only [hlogLower, hpow']
  have hC : 0 < Nat.floor ((p : ℝ) ^ (8666667 / 10000000 : ℝ)) :=
    Nat.lt_of_lt_of_le (by decide : 0 < 1)
      (Nat.le_floor
        (by
          simpa only [Nat.cast_one] using
            Real.one_le_rpow (Nat.one_le_cast.mpr (Nat.succ_le_of_lt hp))
              (by norm_num only : (0 : ℝ) ≤ 8666667 / 10000000)))
  have hcL : 2 * (99999782 / 100000000 : ℝ) ≤ Real.log (Real.log p) := by nlinarith only [hz]
  have hpowergap :
    32 * Real.log (Real.log p) ≤
      (Real.log p) ^ ((18666703 / 10000000 : ℝ) - (18666686 / 10000000 : ℝ)) := by
    rw [Real.rpow_def_of_pos hLp]
    calc
      _ ≤ Real.exp (Real.log (Real.log p) * (17 / 10000000 : ℝ)) :=
        Analysis.mul_32_le_exp_gap_17_d7 hz
      _ ≤
          Real.exp
            (Real.log (Real.log p) * ((18666703 / 10000000 : ℝ) - (18666686 / 10000000 : ℝ))) :=
        by
        apply Real.exp_le_exp.mpr
        nlinarith only
      _ = _ := by congr 1
  have hMp :=
    NumberTheory.two_mul_rpow_le_primeCounting_floor_of_gap (L := Real.log p) (A :=
      18666703 / 10000000) (b := 18666686 / 10000000) (by linarith only [hlogLower])
      (by norm_num only) (by norm_num only) hB hpowergap
  have hgap :=
    Analysis.smooth_scale_gap_of_log_lower_bound hlogLower hz
      (by norm_num only : (0 : ℝ) < 12082601) (by norm_num only : (0 : ℝ) ≤ 18666703 / 10000000)
      (by norm_num only :
        (99999782 / 100000000 : ℝ) * (18666703 / 10000000 : ℝ) +
            (18666703 / 10000000 : ℝ) * (2 / 12082601 : ℝ) <
          28 / 15)
  have hlogC :
    Real.log (Nat.floor ((p : ℝ) ^ (8666667 / 10000000 : ℝ))) ≤
      (8666667 / 10000000 : ℝ) * Real.log p := by
    have h :=
      Real.log_le_log (Nat.cast_pos.mpr hC) (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg p) _))
    rw [Real.log_rpow (Nat.cast_pos.mpr hp)] at h
    exact h
  exact
    exists_prime_pow_ne_one_fiber_28_15 (u := u) hodd hu hlarge hL
      (Nat.lt_of_lt_of_le (by decide : 0 < 64 ^ 4) hB) hC hcL hMp hgap hlogC
      (fun k hcut ↦ Analysis.rational_cutoff_28_15_le_prime_mul_floor_beta hp hlogLower hcut)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only :
        (8666667 / 10000000 : ℝ) < (99999782 / 100000000 : ℝ) * ((18666686 / 10000000 : ℝ) - 1))

/-- Inputs: an odd prime `p≥P(u)` with `u≥17,431,511`.
Claim: a prime q≤(log p)^(1.86667019) has nontrivial `(p-1)`-st power modulo
p². Keep the 28/15 cutoff and double-log threshold, and tighten the prime and
smooth-count exponents. Role: supplies the improved Fermat witness. -/
theorem exists_prime_pow_ne_one_186667019_d8 {p u : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hu : 17431511 ≤ u) (hlarge : explicitFiniteFiberPrimeThreshold u ≤ p) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log p) ^ (186667019 / 100000000 : ℝ) ∧
        (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  have hp := (Fact.out : p.Prime).pos
  have hLp : 0 < Real.log p := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hz := le_log_log_12082601 hu hlarge
  have hlogLower := Analysis.pow_10_12_le_of_log_ge_12082601 hLp hz
  have hL : 2 ≤ Real.log p := by linarith only [hlogLower]
  have hLge : 1 ≤ Real.log p := le_trans (by norm_num only : (1 : ℝ) ≤ 2) hL
  have hB : 64 ^ 4 ≤ Nat.floor ((Real.log p) ^ (186667019 / 100000000 : ℝ)) := by
    apply Nat.le_floor
    have hpow :=
      Real.rpow_le_rpow_of_exponent_le hLge
        (by norm_num only : (1 : ℝ) ≤ (186667019 / 100000000 : ℝ))
    have hpow' : Real.log p ≤ (Real.log p) ^ (186667019 / 100000000 : ℝ) := by
      simpa only [Real.rpow_one] using hpow
    norm_num only [Nat.cast_pow]
    nlinarith only [hlogLower, hpow']
  have hC : 0 < Nat.floor ((p : ℝ) ^ (8666667 / 10000000 : ℝ)) :=
    Nat.lt_of_lt_of_le (by decide : 0 < 1)
      (Nat.le_floor
        (by
          simpa only [Nat.cast_one] using
            Real.one_le_rpow (Nat.one_le_cast.mpr (Nat.succ_le_of_lt hp))
              (by norm_num only : (0 : ℝ) ≤ 8666667 / 10000000)))
  have hcL : 2 * (99999794 / 100000000 : ℝ) ≤ Real.log (Real.log p) := by nlinarith only [hz]
  have hpowergap :
    32 * Real.log (Real.log p) ≤
      (Real.log p) ^ ((186667019 / 100000000 : ℝ) - (186666849 / 100000000 : ℝ)) := by
    rw [Real.rpow_def_of_pos hLp]
    calc
      _ ≤ Real.exp (Real.log (Real.log p) * (17 / 10000000 : ℝ)) :=
        Analysis.mul_32_le_exp_gap_17_d7 hz
      _ ≤
          Real.exp
            (Real.log (Real.log p) * ((186667019 / 100000000 : ℝ) - (186666849 / 100000000 : ℝ))) :=
        by
        apply Real.exp_le_exp.mpr
        nlinarith only
      _ = _ := by congr 1
  have hMp :=
    NumberTheory.two_mul_rpow_le_primeCounting_floor_of_gap (L := Real.log p) (A :=
      186667019 / 100000000) (b := 186666849 / 100000000) (by linarith only [hlogLower])
      (by norm_num only) (by norm_num only) hB hpowergap
  have hgap :=
    Analysis.smooth_scale_gap_of_log_lower_bound hlogLower hz
      (by norm_num only : (0 : ℝ) < 12082601) (by norm_num only : (0 : ℝ) ≤ 186667019 / 100000000)
      (by norm_num only :
        (99999794 / 100000000 : ℝ) * (186667019 / 100000000) +
            (186667019 / 100000000 : ℝ) * (2 / 12082601 : ℝ) <
          28 / 15)
  have hlogC :
    Real.log (Nat.floor ((p : ℝ) ^ (8666667 / 10000000 : ℝ))) ≤
      (8666667 / 10000000 : ℝ) * Real.log p := by
    have h :=
      Real.log_le_log (Nat.cast_pos.mpr hC) (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg p) _))
    rw [Real.log_rpow (Nat.cast_pos.mpr hp)] at h
    exact h
  exact
    exists_prime_pow_ne_one_fiber_28_15 (u := u) hodd hu hlarge hL
      (Nat.lt_of_lt_of_le (by decide : 0 < 64 ^ 4) hB) hC hcL hMp hgap hlogC
      (fun k hcut ↦ Analysis.rational_cutoff_28_15_le_prime_mul_floor_beta hp hlogLower hcut)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only :
        (8666667 / 10000000 : ℝ) < (99999794 / 100000000 : ℝ) * ((186666849 / 100000000 : ℝ) - 1))

/-- Inputs: an odd prime `p≥P(u)` with `u≥17,431,511`.
Claim: a prime `q≤(log p)^(1.866670171)` has nontrivial `(p-1)`-st power
modulo `p²`. The proof tightens the smooth-count exponents in the 28/15
finite-fiber estimate. Role: gives the sharper Fermat witness branch. -/
theorem exists_prime_pow_ne_one_1866670171_d9 {p u : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hu : 17431511 ≤ u) (hlarge : explicitFiniteFiberPrimeThreshold u ≤ p) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log p) ^ (1866670171 / 1000000000 : ℝ) ∧
        (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  have hp := (Fact.out : p.Prime).pos
  have hLp : 0 < Real.log p := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hz := le_log_log_12082601 hu hlarge
  have hlogLower := Analysis.pow_10_12_le_of_log_ge_12082601 hLp hz
  have hL : 2 ≤ Real.log p := by linarith only [hlogLower]
  have hLge : 1 ≤ Real.log p := le_trans (by norm_num only : (1 : ℝ) ≤ 2) hL
  have hB : 64 ^ 4 ≤ Nat.floor ((Real.log p) ^ (1866670171 / 1000000000 : ℝ)) := by
    apply Nat.le_floor
    have hpow :=
      Real.rpow_le_rpow_of_exponent_le hLge
        (by norm_num only : (1 : ℝ) ≤ (1866670171 / 1000000000 : ℝ))
    have hpow' : Real.log p ≤ (Real.log p) ^ (1866670171 / 1000000000 : ℝ) := by
      simpa only [Real.rpow_one] using hpow
    norm_num only [Nat.cast_pow]
    nlinarith only [hlogLower, hpow']
  have hC : 0 < Nat.floor ((p : ℝ) ^ (8666667 / 10000000 : ℝ)) :=
    Nat.lt_of_lt_of_le (by decide : 0 < 1)
      (Nat.le_floor
        (by
          simpa only [Nat.cast_one] using
            Real.one_le_rpow (Nat.one_le_cast.mpr (Nat.succ_le_of_lt hp))
              (by norm_num only : (0 : ℝ) ≤ 8666667 / 10000000)))
  have hcL : 2 * (999997957 / 1000000000 : ℝ) ≤ Real.log (Real.log p) := by nlinarith only [hz]
  have hpowergap :
    32 * Real.log (Real.log p) ≤
      (Real.log p) ^ ((1866670171 / 1000000000 : ℝ) - (1866668471 / 1000000000 : ℝ)) := by
    rw [Real.rpow_def_of_pos hLp]
    calc
      _ ≤ Real.exp (Real.log (Real.log p) * (17 / 10000000 : ℝ)) :=
        Analysis.mul_32_le_exp_gap_17_d7 hz
      _ ≤
          Real.exp
            (Real.log (Real.log p) *
              ((1866670171 / 1000000000 : ℝ) - (1866668471 / 1000000000 : ℝ))) :=
        by
        apply Real.exp_le_exp.mpr
        nlinarith only
      _ = _ := by congr 1
  have hMp :=
    NumberTheory.two_mul_rpow_le_primeCounting_floor_of_gap (L := Real.log p) (A :=
      1866670171 / 1000000000) (b := 1866668471 / 1000000000) (by linarith only [hlogLower])
      (by norm_num only) (by norm_num only) hB hpowergap
  have hgap :=
    Analysis.smooth_scale_gap_of_log_lower_bound hlogLower hz
      (by norm_num only : (0 : ℝ) < 12082601) (by norm_num only : (0 : ℝ) ≤ 1866670171 / 1000000000)
      (by norm_num only :
        (999997957 / 1000000000 : ℝ) * (1866670171 / 1000000000) +
            (1866670171 / 1000000000 : ℝ) * (2 / 12082601 : ℝ) <
          28 / 15)
  have hlogC :
    Real.log (Nat.floor ((p : ℝ) ^ (8666667 / 10000000 : ℝ))) ≤
      (8666667 / 10000000 : ℝ) * Real.log p := by
    have h :=
      Real.log_le_log (Nat.cast_pos.mpr hC) (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg p) _))
    rw [Real.log_rpow (Nat.cast_pos.mpr hp)] at h
    exact h
  exact
    exists_prime_pow_ne_one_fiber_28_15 (u := u) hodd hu hlarge hL
      (Nat.lt_of_lt_of_le (by decide : 0 < 64 ^ 4) hB) hC hcL hMp hgap hlogC
      (fun k hcut ↦ Analysis.rational_cutoff_28_15_le_prime_mul_floor_beta hp hlogLower hcut)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only :
        (8666667 / 10000000 : ℝ) <
          (999997957 / 1000000000 : ℝ) * ((1866668471 / 1000000000 : ℝ) - 1))

/-- Inputs: an odd prime `p≥P(u)` with `u≥17,431,511`.
Claim: a prime `q≤(log p)^(1.86667011)` has nontrivial `(p-1)`-st power
modulo `p²`. The smooth-number exponent is reduced to `13/15+10^-11` while
retaining the 28/15 cutoff. Role: improves the finite-fiber Fermat bound. -/
theorem exists_prime_pow_ne_one_186667011_d8 {p u : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hu : 17431511 ≤ u) (hlarge : explicitFiniteFiberPrimeThreshold u ≤ p) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log p) ^ (186667011 / 100000000 : ℝ) ∧
        (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  have hp := (Fact.out : p.Prime).pos
  have hLp : 0 < Real.log p := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hz := le_log_log_12082601 hu hlarge
  have hlogLower := Analysis.pow_10_12_le_of_log_ge_12082601 hLp hz
  have hL : 2 ≤ Real.log p := by linarith only [hlogLower]
  have hLge : 1 ≤ Real.log p := le_trans (by norm_num only : (1 : ℝ) ≤ 2) hL
  have hB : 64 ^ 4 ≤ Nat.floor ((Real.log p) ^ (186667011 / 100000000 : ℝ)) := by
    apply Nat.le_floor
    have hpow :=
      Real.rpow_le_rpow_of_exponent_le hLge
        (by norm_num only : (1 : ℝ) ≤ (186667011 / 100000000 : ℝ))
    have hpow' : Real.log p ≤ (Real.log p) ^ (186667011 / 100000000 : ℝ) := by
      simpa only [Real.rpow_one] using hpow
    norm_num only [Nat.cast_pow]
    nlinarith only [hlogLower, hpow']
  have hC : 0 < Nat.floor ((p : ℝ) ^ (260000000003 / 300000000000 : ℝ)) :=
    Nat.lt_of_lt_of_le (by decide : 0 < 1)
      (Nat.le_floor
        (by
          simpa only [Nat.cast_one] using
            Real.one_le_rpow (Nat.one_le_cast.mpr (Nat.succ_le_of_lt hp))
              (by norm_num only : (0 : ℝ) ≤ 260000000003 / 300000000000)))
  have hcL : 2 * (9999979892 / 10000000000 : ℝ) ≤ Real.log (Real.log p) := by nlinarith only [hz]
  have hpowergap :
    32 * Real.log (Real.log p) ≤
      (Real.log p) ^ ((186667011 / 100000000 : ℝ) - (186666841 / 100000000 : ℝ)) := by
    rw [Real.rpow_def_of_pos hLp]
    calc
      _ ≤ Real.exp (Real.log (Real.log p) * (17 / 10000000 : ℝ)) :=
        Analysis.mul_32_le_exp_gap_17_d7 hz
      _ ≤
          Real.exp
            (Real.log (Real.log p) * ((186667011 / 100000000 : ℝ) - (186666841 / 100000000 : ℝ))) :=
        by
        apply Real.exp_le_exp.mpr
        nlinarith only
      _ = _ := by congr 1
  have hMp :=
    NumberTheory.two_mul_rpow_le_primeCounting_floor_of_gap (L := Real.log p) (A :=
      186667011 / 100000000) (b := 186666841 / 100000000) (by linarith only [hlogLower])
      (by norm_num only) (by norm_num only) hB hpowergap
  have hgap :=
    Analysis.smooth_scale_gap_of_log_lower_bound hlogLower hz
      (by norm_num only : (0 : ℝ) < 12082601) (by norm_num only : (0 : ℝ) ≤ 186667011 / 100000000)
      (by norm_num only :
        (9999979892 / 10000000000 : ℝ) * (186667011 / 100000000) +
            (186667011 / 100000000 : ℝ) * (2 / 12082601 : ℝ) <
          28 / 15)
  have hlogC :
    Real.log (Nat.floor ((p : ℝ) ^ (260000000003 / 300000000000 : ℝ))) ≤
      (260000000003 / 300000000000 : ℝ) * Real.log p := by
    have h :=
      Real.log_le_log (Nat.cast_pos.mpr hC) (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg p) _))
    rw [Real.log_rpow (Nat.cast_pos.mpr hp)] at h
    exact h
  exact
    exists_prime_pow_ne_one_fiber_28_15 (u := u) hodd hu hlarge hL
      (Nat.lt_of_lt_of_le (by decide : 0 < 64 ^ 4) hB) hC hcL hMp hgap hlogC
      (fun k hcut ↦
        Analysis.rational_cutoff_28_15_le_prime_mul_floor_of_beta hp hlogLower (by norm_num only)
          hcut)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only :
        (260000000003 / 300000000000 : ℝ) <
          (9999979892 / 10000000000 : ℝ) * ((186666841 / 100000000 : ℝ) - 1))

/-- Inputs: an odd prime `p≥P(u)` with `u≥17,431,511`.
Claim: a prime `q≤(log p)^(1.866670047)` has nontrivial `(p-1)`-st power
modulo `p²`. The smooth-number exponent is reduced to `13/15+10^-11` while
retaining the 28/15 cutoff. Role: improves the finite-fiber Fermat bound. -/
theorem exists_prime_pow_ne_one_1866670047_d9 {p u : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hu : 17431511 ≤ u) (hlarge : explicitFiniteFiberPrimeThreshold u ≤ p) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log p) ^ (1866670047 / 1000000000 : ℝ) ∧
        (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 := by
  have hp := (Fact.out : p.Prime).pos
  have hLp : 0 < Real.log p := Real.log_pos (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have hz := le_log_log_12082601 hu hlarge
  have hlogLower := Analysis.pow_10_12_le_of_log_ge_12082601 hLp hz
  have hL : 2 ≤ Real.log p := by linarith only [hlogLower]
  have hLge : 1 ≤ Real.log p := le_trans (by norm_num only : (1 : ℝ) ≤ 2) hL
  have hB : 64 ^ 4 ≤ Nat.floor ((Real.log p) ^ (1866670047 / 1000000000 : ℝ)) := by
    apply Nat.le_floor
    have hpow :=
      Real.rpow_le_rpow_of_exponent_le hLge
        (by norm_num only : (1 : ℝ) ≤ (1866670047 / 1000000000 : ℝ))
    have hpow' : Real.log p ≤ (Real.log p) ^ (1866670047 / 1000000000 : ℝ) := by
      simpa only [Real.rpow_one] using hpow
    norm_num only [Nat.cast_pow]
    nlinarith only [hlogLower, hpow']
  have hC : 0 < Nat.floor ((p : ℝ) ^ (260000000003 / 300000000000 : ℝ)) :=
    Nat.lt_of_lt_of_le (by decide : 0 < 1)
      (Nat.le_floor
        (by
          simpa only [Nat.cast_one] using
            Real.one_le_rpow (Nat.one_le_cast.mpr (Nat.succ_le_of_lt hp))
              (by norm_num only : (0 : ℝ) ≤ 260000000003 / 300000000000)))
  have hcL : 2 * (9999979892 / 10000000000 : ℝ) ≤ Real.log (Real.log p) := by nlinarith only [hz]
  have hpowergap :
    32 * Real.log (Real.log p) ≤
      (Real.log p) ^ ((1866670047 / 1000000000 : ℝ) - (186666841 / 100000000 : ℝ)) := by
    rw [Real.rpow_def_of_pos hLp]
    calc
      _ ≤ Real.exp (Real.log (Real.log p) * (1637 / 1000000000 : ℝ)) :=
        Analysis.thirty_two_mul_le_exp_gap_1637_over_billion hz
      _ ≤
          Real.exp
            (Real.log (Real.log p) *
              ((1866670047 / 1000000000 : ℝ) - (186666841 / 100000000 : ℝ))) :=
        by
        apply Real.exp_le_exp.mpr
        nlinarith only
      _ = _ := by congr 1
  have hMp :=
    NumberTheory.two_mul_rpow_le_primeCounting_floor_of_gap (L := Real.log p) (A :=
      1866670047 / 1000000000) (b := 186666841 / 100000000) (by linarith only [hlogLower])
      (by norm_num only) (by norm_num only) hB hpowergap
  have hgap :=
    Analysis.smooth_scale_gap_of_log_lower_bound hlogLower hz
      (by norm_num only : (0 : ℝ) < 12082601) (by norm_num only : (0 : ℝ) ≤ 1866670047 / 1000000000)
      (by norm_num only :
        (9999979892 / 10000000000 : ℝ) * (1866670047 / 1000000000) +
            (1866670047 / 1000000000 : ℝ) * (2 / 12082601 : ℝ) <
          28 / 15)
  have hlogC :
    Real.log (Nat.floor ((p : ℝ) ^ (260000000003 / 300000000000 : ℝ))) ≤
      (260000000003 / 300000000000 : ℝ) * Real.log p := by
    have h :=
      Real.log_le_log (Nat.cast_pos.mpr hC) (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg p) _))
    rw [Real.log_rpow (Nat.cast_pos.mpr hp)] at h
    exact h
  exact
    exists_prime_pow_ne_one_fiber_28_15 (u := u) hodd hu hlarge hL
      (Nat.lt_of_lt_of_le (by decide : 0 < 64 ^ 4) hB) hC hcL hMp hgap hlogC
      (fun k hcut ↦
        Analysis.rational_cutoff_28_15_le_prime_mul_floor_of_beta hp hlogLower (by norm_num only)
          hcut)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only :
        (260000000003 / 300000000000 : ℝ) <
          (9999979892 / 10000000000 : ℝ) * ((186666841 / 100000000 : ℝ) - 1))

end PseudoPrime.NumberTheory.Heilbronn
