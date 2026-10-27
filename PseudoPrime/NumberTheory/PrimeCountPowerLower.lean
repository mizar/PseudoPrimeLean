/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.ChebyshevPrimeCountLower
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Unconditional power lower bounds for prime counts -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- The logarithm of n+1 divided by n tends to zero on natural inputs.
Compose the shifted real logarithm limit with natural casts and simplify the denominator.
Used to absorb the first Chebyshev error without a finite starting certificate. -/
theorem tendsto_log_nat_add_one_div_self :
    Filter.Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ) + 1) / (n : ℝ)) Filter.atTop (nhds 0) := by
  have hs : Filter.Tendsto (fun n : ℕ ↦ 1 + (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hs
  convert h using 1
  ext n
  congr 1
  · rw [pow_one, add_comm]
  · ring

/-- The logarithm of n divided by sqrt n tends to zero on natural inputs.
Apply log(x)=o(x^(1/2)) and compose with natural casts. This absorbs the second
Chebyshev error in the unconditional prime-count lower bound. -/
theorem tendsto_log_nat_div_sqrt :
    Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / Real.sqrt (n : ℝ)) Filter.atTop (nhds 0) := by
  have hl := isLittleO_log_rpow_atTop (by norm_num only : (0 : ℝ) < 1 / 2)
  have h := hl.tendsto_div_nhds_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Real.sqrt_eq_rpow, Function.comp_def] using h

/-- Eventually pi(B)*log B is at least (log 2)/2 times B.
Absorb both errors in the elementary Chebyshev lower bound using their vanishing
normalized limits. This supplies the main term needed for power lower bounds. -/
theorem eventually_half_log_two_mul_le_primeCounting_mul_log :
    Filter.Eventually (fun B : ℕ ↦ (Real.log 2 / 2) * B ≤ (B.primeCounting : ℝ) * Real.log B)
      Filter.atTop := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have he1 :=
    tendsto_log_nat_add_one_div_self.eventually_lt_const
      (div_pos hlog2 (by norm_num only : (0 : ℝ) < 4))
  have he2 :=
    tendsto_log_nat_div_sqrt.eventually_lt_const (div_pos hlog2 (by norm_num only : (0 : ℝ) < 8))
  filter_upwards [he1, he2, Filter.eventually_gt_atTop (0 : ℕ)] with B h1 h2 hB
  have hp : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hs : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.mpr hp
  have hfirst := (div_lt_iff₀ hp).mp h1
  have hsecond := (div_lt_iff₀ hs).mp h2
  have hm := mul_le_mul_of_nonneg_left hsecond.le hs.le
  have he := chebyshev_lower_le_primeCounting_mul_log B
  have hsq := Real.sq_sqrt hp.le
  rw [mul_left_comm, ← pow_two, hsq] at hm
  nlinarith only [hfirst, hm, he]

/-- For every real t<1, pi(B) is eventually at least B^t on natural B.
Combine the linear-log lower bound with log(B)=o(B^(1-t)). No RH or GRH is used.
This avoids explicit prime lists in the subgroup witness argument. -/
theorem eventually_rpow_le_primeCounting {t : ℝ} (ht : t < 1) :
    Filter.Eventually (fun B : ℕ ↦ (B : ℝ) ^ t ≤ (B.primeCounting : ℝ)) Filter.atTop := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hlim := (isLittleO_log_rpow_atTop (sub_pos.mpr ht)).tendsto_div_nhds_zero
  have hnat := hlim.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have he := hnat.eventually_lt_const (div_pos hlog2 (by norm_num only : (0 : ℝ) < 2))
  filter_upwards [he, eventually_half_log_two_mul_le_primeCounting_mul_log,
    Filter.eventually_gt_atTop (1 : ℕ)] with B hsmall hlower hB
  have hp : (0 : ℝ) < B := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hB)
  have hlog : 0 < Real.log (B : ℝ) := Real.log_pos (Nat.one_lt_cast.mpr hB)
  have hr := (div_lt_iff₀ (Real.rpow_pos_of_pos hp (1 - t))).mp hsmall
  have hm := mul_le_mul_of_nonneg_left hr.le (Real.rpow_nonneg hp.le t)
  have hid : (B : ℝ) ^ t * (B : ℝ) ^ (1 - t) = B := by
    rw [← Real.rpow_add hp]
    simp only [add_sub_cancel, Real.rpow_one]
  have hx : (B : ℝ) ^ t * Real.log B ≤ (Real.log 2 / 2) * B := by
    rw [mul_left_comm, hid] at hm
    exact hm
  exact (mul_le_mul_iff_left₀ hlog).mp (hx.trans hlower)

/-- If b<A, every fixed multiple C*x^b is eventually at most x^A.
Multiply the eventual lower bound for x^(A-b) by x^b. Used to absorb constants
and floor losses in the prime-count parameter selection. -/
theorem eventually_const_mul_rpow_le_rpow {b A C : ℝ} (h : b < A) :
    Filter.Eventually (fun x : ℝ ↦ C * x ^ b ≤ x ^ A) Filter.atTop := by
  have he := (tendsto_rpow_atTop (sub_pos.mpr h)).eventually_ge_atTop C
  filter_upwards [he, Filter.eventually_gt_atTop (0 : ℝ)] with x hx hp
  calc
    C * x ^ b ≤ x ^ (A - b) * x ^ b := mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hp.le b)
    _ = x ^ A := by rw [← Real.rpow_add hp, sub_add_cancel]

/-- For 0<=b<A, x^b is eventually at most floor(x^A).
Use x^A>=2*x^b and x^b>=1 to absorb the unit floor error. This supplies a natural
cutoff below the desired real log-power bound. -/
theorem eventually_rpow_le_nat_floor_rpow {b A : ℝ} (hb : 0 ≤ b) (h : b < A) :
    Filter.Eventually (fun x : ℝ ↦ x ^ b ≤ (Nat.floor (x ^ A) : ℝ)) Filter.atTop := by
  filter_upwards [eventually_const_mul_rpow_le_rpow (C := 2) h,
    Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hb1 := Real.one_le_rpow hx1 hb
  have hf := Nat.lt_floor_add_one (x ^ A)
  nlinarith only [hx, hb1, hf]

/-- For 0<b<A and any C, pi(floor(x^A)) is eventually at least C*x^b.
Choose intermediate powers, combine the floor lower bound with pi(B)>=B^t,
and absorb the remaining constant. This is the prime supply for MR product counting. -/
theorem eventually_const_mul_rpow_le_primeCounting_floor_rpow {b A C : ℝ} (hb : 0 < b) (h : b < A) :
    Filter.Eventually (fun x : ℝ ↦ C * x ^ b ≤ ((Nat.floor (x ^ A)).primeCounting : ℝ))
      Filter.atTop := by
  obtain ⟨d, hbd, hdA⟩ := exists_between h
  have hd : 0 < d := hb.trans hbd
  obtain ⟨t, hbt, ht1⟩ := exists_between ((div_lt_one hd).mpr hbd)
  have ht : 0 < t := (div_pos hb hd).trans hbt
  have hdt : b < d * t := by
    have hm := (div_lt_iff₀ hd).mp hbt
    simpa only [mul_comm] using hm
  have hB := tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop (hd.trans hdA))
  have hpi := hB.eventually (eventually_rpow_le_primeCounting ht1)
  filter_upwards [hpi, eventually_rpow_le_nat_floor_rpow hd.le hdA,
    eventually_const_mul_rpow_le_rpow (C := C) hdt, Filter.eventually_ge_atTop (0 : ℝ)] with x hpx
    hfx hg hx
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hx d) hfx ht.le
  rw [← Real.rpow_mul hx] at hpow
  exact hg.trans (hpow.trans hpx)

end PseudoPrime.NumberTheory
