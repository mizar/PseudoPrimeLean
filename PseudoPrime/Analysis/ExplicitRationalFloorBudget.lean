/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalHeilbronnSmoothBudget
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # An explicit floor budget at the rational cutoff 125/68 -/

public section

namespace PseudoPrime.Analysis

/-- If log p≥10^20, every k with k^80≤2^80 p^147 satisfies
256k≤p floor(p^(1047/1250)). Absorb the constant using the exact
exponent gap 1/10000 and keep the unit floor error. -/
theorem fixed_rational_cutoff_le_prime_mul_floor {p k : ℕ} (hp : 0 < p)
    (hL : (10 : ℝ) ^ 20 ≤ Real.log p) (hcut : k ^ 80 ≤ 2 ^ 80 * p ^ 147) :
    256 * k ≤ p * Nat.floor ((p : ℝ) ^ (1047 / 1250 : ℝ)) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hg : (1024 : ℝ) ≤ (p : ℝ) ^ (1 / 10000 : ℝ) := by
    rw [Real.rpow_def_of_pos hpR]
    have he := Real.add_one_le_exp (Real.log p * (1 / 10000))
    linarith only [he, hL]
  have htwo : (2 : ℝ) ≤ (p : ℝ) ^ (1047 / 1250 : ℝ) := by
    rw [Real.rpow_def_of_pos hpR]
    have he := Real.add_one_le_exp (Real.log p * (1047 / 1250))
    linarith only [he, hL]
  have hf := Nat.lt_floor_add_one ((p : ℝ) ^ (1047 / 1250 : ℝ))
  have hhalf : (p : ℝ) ^ (1047 / 1250 : ℝ) ≤ 2 * (Nat.floor ((p : ℝ) ^ (1047 / 1250 : ℝ)) : ℝ) := by
    linarith only [hf, htwo]
  have hm := mul_le_mul_of_nonneg_left hhalf hpR.le
  have hgap := mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg hpR.le (147 / 80 : ℝ))
  rw [← Real.rpow_add hpR, show (147 / 80 : ℝ) + 1 / 10000 = 1 + 1047 / 1250 by norm_num only,
    Real.rpow_add hpR, Real.rpow_one] at hgap
  have hk := rational_cutoff_le_two_rpow (by decide : 0 < 80) hcut
  apply (Nat.cast_le (α := ℝ)).mp
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  norm_num only [Nat.cast_ofNat] at hk
  nlinarith only [hm, hgap, hk]

/-- At scale 125/68, the exponent 8382354/10000000 exceeds 125/68−1 by
9/85000000. If log p≥10^20, this gap absorbs the cutoff constant and the
floor error, giving the prime-times-floor count budget. -/
theorem rational_cutoff_125_68_le_prime_mul_floor {p k : ℕ} (hp : 0 < p)
    (hL : (10 : ℝ) ^ 20 ≤ Real.log p) (hcut : k ^ 68 ≤ 2 ^ 68 * p ^ 125) :
    256 * k ≤ p * Nat.floor ((p : ℝ) ^ (8382354 / 10000000 : ℝ)) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hbeta :
    (p : ℝ) ^ (8382354 / 10000000 : ℝ) ≤
      2 * (Nat.floor ((p : ℝ) ^ (8382354 / 10000000 : ℝ)) : ℝ) := by
    have hf := Nat.lt_floor_add_one ((p : ℝ) ^ (8382354 / 10000000 : ℝ))
    have htwo : (2 : ℝ) ≤ (p : ℝ) ^ (8382354 / 10000000 : ℝ) := by
      rw [Real.rpow_def_of_pos hpR]
      have he := Real.add_one_le_exp (Real.log p * (8382354 / 10000000))
      nlinarith only [he, hL]
    nlinarith only [hf, htwo]
  have hpow : (1024 : ℝ) ≤ (p : ℝ) ^ (9 / 85000000 : ℝ) := by
    rw [Real.rpow_def_of_pos hpR]
    have he := Real.add_one_le_exp (Real.log p * (9 / 85000000))
    nlinarith only [he, hL]
  have hk := rational_cutoff_le_two_rpow (a := 68) (b := 125) (by decide) hcut
  have hpower := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hpR.le (125 / 68 : ℝ))
  have hscale :
    (512 : ℝ) * (p : ℝ) ^ (125 / 68 : ℝ) ≤ (p : ℝ) ^ (1 + 8382354 / 10000000 : ℝ) / 2 := by
    apply (le_div_iff₀ (by norm_num only : (0 : ℝ) < 2)).2
    calc
      512 * (p : ℝ) ^ (125 / 68 : ℝ) * 2 = 1024 * (p : ℝ) ^ (125 / 68 : ℝ) := by ring
      _ ≤ (p : ℝ) ^ (9 / 85000000 : ℝ) * (p : ℝ) ^ (125 / 68 : ℝ) := by
        calc
          _ = (1024 : ℝ) * (p : ℝ) ^ (125 / 68 : ℝ) := by ring
          _ ≤ _ := hpower
      _ = (p : ℝ) ^ (1 + 8382354 / 10000000 : ℝ) := by
        rw [← Real.rpow_add hpR]
        congr 1
        norm_num only
  have hfloor :
    (p : ℝ) * (p : ℝ) ^ (8382354 / 10000000 : ℝ) / 2 ≤
      (p : ℝ) * (Nat.floor ((p : ℝ) ^ (8382354 / 10000000 : ℝ)) : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hbeta hpR.le
    have hd := div_le_div_of_nonneg_right hm (by norm_num only : (0 : ℝ) ≤ 2)
    calc
      _ ≤ (p : ℝ) * (2 * (Nat.floor ((p : ℝ) ^ (8382354 / 10000000 : ℝ)) : ℝ)) / 2 := hd
      _ = _ := by ring
  have hexp :
    (p : ℝ) ^ (1 + 8382354 / 10000000 : ℝ) = (p : ℝ) * (p : ℝ) ^ (8382354 / 10000000 : ℝ) := by
    rw [Real.rpow_add hpR, Real.rpow_one]
  have hk' : (256 : ℝ) * k ≤ 512 * (p : ℝ) ^ (125 / 68 : ℝ) := by
    calc
      _ ≤ 256 * (2 * (p : ℝ) ^ (125 / 68 : ℝ)) := mul_le_mul_of_nonneg_left hk (by norm_num only)
      _ = _ := by ring
  have hbound := hk'.trans (hscale.trans_eq (congrArg (fun x : ℝ ↦ x / 2) hexp))
  have hresult := hbound.trans hfloor
  exact (Nat.cast_le (α := ℝ)).mp (by exact_mod_cast hresult)

/-- At scale 74/40, the floor exponent 8500002/10000000 exceeds
74/40−1 by 1/5000000. If log p≥10^20, this margin absorbs the cutoff
constant and floor error in the prime-times-floor count. -/
theorem rational_cutoff_74_40_le_prime_mul_floor {p k : ℕ} (hp : 0 < p)
    (hL : (10 : ℝ) ^ 20 ≤ Real.log p) (hcut : k ^ 40 ≤ 2 ^ 40 * p ^ 74) :
    256 * k ≤ p * Nat.floor ((p : ℝ) ^ (8500002 / 10000000 : ℝ)) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hbeta :
    (p : ℝ) ^ (8500002 / 10000000 : ℝ) ≤
      2 * (Nat.floor ((p : ℝ) ^ (8500002 / 10000000 : ℝ)) : ℝ) := by
    have hf := Nat.lt_floor_add_one ((p : ℝ) ^ (8500002 / 10000000 : ℝ))
    have htwo : (2 : ℝ) ≤ (p : ℝ) ^ (8500002 / 10000000 : ℝ) := by
      rw [Real.rpow_def_of_pos hpR]
      have he := Real.add_one_le_exp (Real.log p * (8500002 / 10000000))
      nlinarith only [he, hL]
    nlinarith only [hf, htwo]
  have hpow : (1024 : ℝ) ≤ (p : ℝ) ^ (1 / 5000000 : ℝ) := by
    rw [Real.rpow_def_of_pos hpR]
    have he := Real.add_one_le_exp (Real.log p * (1 / 5000000))
    nlinarith only [he, hL]
  have hk := rational_cutoff_le_two_rpow (a := 40) (b := 74) (by decide) hcut
  have hpower := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hpR.le (74 / 40 : ℝ))
  have hscale :
    (512 : ℝ) * (p : ℝ) ^ (74 / 40 : ℝ) ≤ (p : ℝ) ^ (1 + 8500002 / 10000000 : ℝ) / 2 := by
    apply (le_div_iff₀ (by norm_num only : (0 : ℝ) < 2)).2
    calc
      512 * (p : ℝ) ^ (74 / 40 : ℝ) * 2 = 1024 * (p : ℝ) ^ (74 / 40 : ℝ) := by ring
      _ ≤ (p : ℝ) ^ (1 / 5000000 : ℝ) * (p : ℝ) ^ (74 / 40 : ℝ) := by
        calc
          _ = (1024 : ℝ) * (p : ℝ) ^ (74 / 40 : ℝ) := by ring
          _ ≤ _ := hpower
      _ = (p : ℝ) ^ (1 + 8500002 / 10000000 : ℝ) := by
        rw [← Real.rpow_add hpR]
        congr 1
        norm_num only
  have hfloor :
    (p : ℝ) * (p : ℝ) ^ (8500002 / 10000000 : ℝ) / 2 ≤
      (p : ℝ) * (Nat.floor ((p : ℝ) ^ (8500002 / 10000000 : ℝ)) : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hbeta hpR.le
    have hd := div_le_div_of_nonneg_right hm (by norm_num only : (0 : ℝ) ≤ 2)
    calc
      _ ≤ (p : ℝ) * (2 * (Nat.floor ((p : ℝ) ^ (8500002 / 10000000 : ℝ)) : ℝ)) / 2 := hd
      _ = _ := by ring
  have hexp :
    (p : ℝ) ^ (1 + 8500002 / 10000000 : ℝ) = (p : ℝ) * (p : ℝ) ^ (8500002 / 10000000 : ℝ) := by
    rw [Real.rpow_add hpR, Real.rpow_one]
  have hk' : (256 : ℝ) * k ≤ 512 * (p : ℝ) ^ (74 / 40 : ℝ) := by
    calc
      _ ≤ 256 * (2 * (p : ℝ) ^ (74 / 40 : ℝ)) := mul_le_mul_of_nonneg_left hk (by norm_num only)
      _ = _ := by ring
  have hbound := hk'.trans (hscale.trans_eq (congrArg (fun x : ℝ ↦ x / 2) hexp))
  have hresult := hbound.trans hfloor
  exact (Nat.cast_le (α := ℝ)).mp (by exact_mod_cast hresult)

/-- At scale 70/38, the floor exponent 160000019/190000000 exceeds
70/38−1 by 1/10000000. If log p≥10^20, this margin absorbs the cutoff
constant and floor error in the prime-times-floor count. -/
theorem rational_cutoff_70_38_le_prime_mul_floor {p k : ℕ} (hp : 0 < p)
    (hL : (10 : ℝ) ^ 20 ≤ Real.log p) (hcut : k ^ 38 ≤ 2 ^ 38 * p ^ 70) :
    256 * k ≤ p * Nat.floor ((p : ℝ) ^ (160000019 / 190000000 : ℝ)) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hbeta :
    (p : ℝ) ^ (160000019 / 190000000 : ℝ) ≤
      2 * (Nat.floor ((p : ℝ) ^ (160000019 / 190000000 : ℝ)) : ℝ) := by
    have hf := Nat.lt_floor_add_one ((p : ℝ) ^ (160000019 / 190000000 : ℝ))
    have htwo : (2 : ℝ) ≤ (p : ℝ) ^ (160000019 / 190000000 : ℝ) := by
      rw [Real.rpow_def_of_pos hpR]
      have he := Real.add_one_le_exp (Real.log p * (160000019 / 190000000))
      nlinarith only [he, hL]
    nlinarith only [hf, htwo]
  have hpow : (1024 : ℝ) ≤ (p : ℝ) ^ (1 / 10000000 : ℝ) := by
    rw [Real.rpow_def_of_pos hpR]
    have he := Real.add_one_le_exp (Real.log p * (1 / 10000000))
    nlinarith only [he, hL]
  have hk := rational_cutoff_le_two_rpow (a := 38) (b := 70) (by decide) hcut
  have hpower := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hpR.le (70 / 38 : ℝ))
  have hscale :
    (512 : ℝ) * (p : ℝ) ^ (70 / 38 : ℝ) ≤ (p : ℝ) ^ (1 + 160000019 / 190000000 : ℝ) / 2 := by
    apply (le_div_iff₀ (by norm_num only : (0 : ℝ) < 2)).2
    calc
      512 * (p : ℝ) ^ (70 / 38 : ℝ) * 2 = 1024 * (p : ℝ) ^ (70 / 38 : ℝ) := by ring
      _ ≤ (p : ℝ) ^ (1 / 10000000 : ℝ) * (p : ℝ) ^ (70 / 38 : ℝ) := by
        calc
          _ = (1024 : ℝ) * (p : ℝ) ^ (70 / 38 : ℝ) := by ring
          _ ≤ _ := hpower
      _ = (p : ℝ) ^ (1 + 160000019 / 190000000 : ℝ) := by
        rw [← Real.rpow_add hpR]
        congr 1
        norm_num only
  have hfloor :
    (p : ℝ) * (p : ℝ) ^ (160000019 / 190000000 : ℝ) / 2 ≤
      (p : ℝ) * (Nat.floor ((p : ℝ) ^ (160000019 / 190000000 : ℝ)) : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hbeta hpR.le
    have hd := div_le_div_of_nonneg_right hm (by norm_num only : (0 : ℝ) ≤ 2)
    calc
      _ ≤ (p : ℝ) * (2 * (Nat.floor ((p : ℝ) ^ (160000019 / 190000000 : ℝ)) : ℝ)) / 2 := hd
      _ = _ := by ring
  have hexp :
    (p : ℝ) ^ (1 + 160000019 / 190000000 : ℝ) =
      (p : ℝ) * (p : ℝ) ^ (160000019 / 190000000 : ℝ) := by
    rw [Real.rpow_add hpR, Real.rpow_one]
  have hk' : (256 : ℝ) * k ≤ 512 * (p : ℝ) ^ (70 / 38 : ℝ) := by
    calc
      _ ≤ 256 * (2 * (p : ℝ) ^ (70 / 38 : ℝ)) := mul_le_mul_of_nonneg_left hk (by norm_num only)
      _ = _ := by ring
  have hbound := hk'.trans (hscale.trans_eq (congrArg (fun x : ℝ ↦ x / 2) hexp))
  have hresult := hbound.trans hfloor
  exact (Nat.cast_le (α := ℝ)).mp (by exact_mod_cast hresult)

/-- At scale 59/32, the floor exponent 8437505/10000000 exceeds
59/32−1 by 1/2000000. For log p≥10^20, this absorbs the cutoff and floor errors. -/
theorem rational_cutoff_59_32_le_prime_mul_floor {p k : ℕ} (hp : 0 < p)
    (hL : (10 : ℝ) ^ 20 ≤ Real.log p) (hcut : k ^ 32 ≤ 2 ^ 32 * p ^ 59) :
    256 * k ≤ p * Nat.floor ((p : ℝ) ^ (8437505 / 10000000 : ℝ)) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hbeta :
    (p : ℝ) ^ (8437505 / 10000000 : ℝ) ≤
      2 * (Nat.floor ((p : ℝ) ^ (8437505 / 10000000 : ℝ)) : ℝ) := by
    have hf := Nat.lt_floor_add_one ((p : ℝ) ^ (8437505 / 10000000 : ℝ))
    have htwo : (2 : ℝ) ≤ (p : ℝ) ^ (8437505 / 10000000 : ℝ) := by
      rw [Real.rpow_def_of_pos hpR]
      have he := Real.add_one_le_exp (Real.log p * (8437505 / 10000000))
      nlinarith only [he, hL]
    nlinarith only [hf, htwo]
  have hpow : (1024 : ℝ) ≤ (p : ℝ) ^ (1 / 2000000 : ℝ) := by
    rw [Real.rpow_def_of_pos hpR]
    have he := Real.add_one_le_exp (Real.log p * (1 / 2000000))
    nlinarith only [he, hL]
  have hk := rational_cutoff_le_two_rpow (a := 32) (b := 59) (by decide) hcut
  have hpower := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hpR.le (59 / 32 : ℝ))
  have hscale :
    (512 : ℝ) * (p : ℝ) ^ (59 / 32 : ℝ) ≤ (p : ℝ) ^ (1 + 8437505 / 10000000 : ℝ) / 2 := by
    apply (le_div_iff₀ (by norm_num only : (0 : ℝ) < 2)).2
    calc
      512 * (p : ℝ) ^ (59 / 32 : ℝ) * 2 = 1024 * (p : ℝ) ^ (59 / 32 : ℝ) := by ring
      _ ≤ (p : ℝ) ^ (1 / 2000000 : ℝ) * (p : ℝ) ^ (59 / 32 : ℝ) := by
        calc
          _ = (1024 : ℝ) * (p : ℝ) ^ (59 / 32 : ℝ) := by ring
          _ ≤ _ := hpower
      _ = (p : ℝ) ^ (1 + 8437505 / 10000000 : ℝ) := by
        rw [← Real.rpow_add hpR]
        congr 1
        norm_num only
  have hfloor :
    (p : ℝ) * (p : ℝ) ^ (8437505 / 10000000 : ℝ) / 2 ≤
      (p : ℝ) * (Nat.floor ((p : ℝ) ^ (8437505 / 10000000 : ℝ)) : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hbeta hpR.le
    have hd := div_le_div_of_nonneg_right hm (by norm_num only : (0 : ℝ) ≤ 2)
    calc
      _ ≤ (p : ℝ) * (2 * (Nat.floor ((p : ℝ) ^ (8437505 / 10000000 : ℝ)) : ℝ)) / 2 := hd
      _ = _ := by ring
  have hexp :
    (p : ℝ) ^ (1 + 8437505 / 10000000 : ℝ) = (p : ℝ) * (p : ℝ) ^ (8437505 / 10000000 : ℝ) := by
    rw [Real.rpow_add hpR, Real.rpow_one]
  have hk' : (256 : ℝ) * k ≤ 512 * (p : ℝ) ^ (59 / 32 : ℝ) := by
    calc
      _ ≤ 256 * (2 * (p : ℝ) ^ (59 / 32 : ℝ)) := mul_le_mul_of_nonneg_left hk (by norm_num only)
      _ = _ := by ring
  have hbound := hk'.trans (hscale.trans_eq (congrArg (fun x : ℝ ↦ x / 2) hexp))
  have hresult := hbound.trans hfloor
  exact (Nat.cast_le (α := ℝ)).mp (by exact_mod_cast hresult)

/-- The floor exponent exceeds 19/10−1 by 10^-18. At log p≥10^20 this
absorbs the cutoff and floor errors in the rational 19/10 bound. -/
theorem rational_cutoff_19_10_le_prime_mul_floor {p k : ℕ} (hp : 0 < p)
    (hL : (10 : ℝ) ^ 20 ≤ Real.log p) (hcut : k ^ 10 ≤ 2 ^ 10 * p ^ 19) :
    256 * k ≤ p * Nat.floor ((p : ℝ) ^ (900000000000000001 / 1000000000000000000 : ℝ)) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hbeta :
    (p : ℝ) ^ (900000000000000001 / 1000000000000000000 : ℝ) ≤
      2 * (Nat.floor ((p : ℝ) ^ (900000000000000001 / 1000000000000000000 : ℝ)) : ℝ) := by
    have hf := Nat.lt_floor_add_one ((p : ℝ) ^ (900000000000000001 / 1000000000000000000 : ℝ))
    have htwo : (2 : ℝ) ≤ (p : ℝ) ^ (900000000000000001 / 1000000000000000000 : ℝ) := by
      rw [Real.rpow_def_of_pos hpR]
      have he := Real.add_one_le_exp (Real.log p * (900000000000000001 / 1000000000000000000))
      nlinarith only [he, hL]
    nlinarith only [hf, htwo]
  have hpow : (1024 : ℝ) ≤ (p : ℝ) ^ (1 / 1000000000000000000 : ℝ) := by
    rw [Real.rpow_def_of_pos hpR]
    have hx : (100 : ℝ) ≤ Real.log p * (1 / 1000000000000000000 : ℝ) := by
      have hmul :=
        mul_le_mul_of_nonneg_right hL (by norm_num only : (0 : ℝ) ≤ 1 / 1000000000000000000)
      nlinarith only [hmul]
    have hx0 : 0 ≤ Real.log p * (1 / 1000000000000000000 : ℝ) := le_trans (by norm_num only) hx
    have he := Real.quadratic_le_exp_of_nonneg hx0
    nlinarith only [hx, he]
  have hk := rational_cutoff_le_two_rpow (a := 10) (b := 19) (by decide) hcut
  have hpower := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hpR.le (19 / 10 : ℝ))
  have hscale :
    (512 : ℝ) * (p : ℝ) ^ (19 / 10 : ℝ) ≤
      (p : ℝ) ^ (1 + 900000000000000001 / 1000000000000000000 : ℝ) / 2 := by
    apply (le_div_iff₀ (by norm_num only : (0 : ℝ) < 2)).2
    calc
      512 * (p : ℝ) ^ (19 / 10 : ℝ) * 2 = 1024 * (p : ℝ) ^ (19 / 10 : ℝ) := by ring
      _ ≤ (p : ℝ) ^ (1 / 1000000000000000000 : ℝ) * (p : ℝ) ^ (19 / 10 : ℝ) := by
        calc
          _ = (1024 : ℝ) * (p : ℝ) ^ (19 / 10 : ℝ) := by ring
          _ ≤ _ := hpower
      _ = (p : ℝ) ^ (1 + 900000000000000001 / 1000000000000000000 : ℝ) := by
        rw [← Real.rpow_add hpR]
        congr 1
        norm_num only
  have hfloor :
    (p : ℝ) * (p : ℝ) ^ (900000000000000001 / 1000000000000000000 : ℝ) / 2 ≤
      (p : ℝ) * (Nat.floor ((p : ℝ) ^ (900000000000000001 / 1000000000000000000 : ℝ)) : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hbeta hpR.le
    have hd := div_le_div_of_nonneg_right hm (by norm_num only : (0 : ℝ) ≤ 2)
    calc
      _ ≤
          (p : ℝ) *
              (2 * (Nat.floor ((p : ℝ) ^ (900000000000000001 / 1000000000000000000 : ℝ)) : ℝ)) /
            2 :=
        hd
      _ = _ := by ring
  have hexp :
    (p : ℝ) ^ (1 + 900000000000000001 / 1000000000000000000 : ℝ) =
      (p : ℝ) * (p : ℝ) ^ (900000000000000001 / 1000000000000000000 : ℝ) := by
    rw [Real.rpow_add hpR, Real.rpow_one]
  have hk' : (256 : ℝ) * k ≤ 512 * (p : ℝ) ^ (19 / 10 : ℝ) := by
    calc
      _ ≤ 256 * (2 * (p : ℝ) ^ (19 / 10 : ℝ)) := mul_le_mul_of_nonneg_left hk (by norm_num only)
      _ = _ := by ring
  have hbound := hk'.trans (hscale.trans_eq (congrArg (fun x : ℝ ↦ x / 2) hexp))
  have hresult := hbound.trans hfloor
  exact (Nat.cast_le (α := ℝ)).mp (by exact_mod_cast hresult)

/-- At the rational cutoff 150/82, the exponent 4147/5000 exceeds
150/82−1 by more than 1/10000. The resulting power margin absorbs the
cutoff constant and the floor loss when log p≥10^12. -/
theorem rational_cutoff_150_82_le_prime_mul_floor {p k : ℕ} (hp : 0 < p)
    (hL : (10 : ℝ) ^ 12 ≤ Real.log p) (hcut : k ^ 82 ≤ 2 ^ 82 * p ^ 150) :
    256 * k ≤ p * Nat.floor ((p : ℝ) ^ (4147 / 5000 : ℝ)) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hbeta : (p : ℝ) ^ (4147 / 5000 : ℝ) ≤ 2 * (Nat.floor ((p : ℝ) ^ (4147 / 5000 : ℝ)) : ℝ) := by
    have hf := Nat.lt_floor_add_one ((p : ℝ) ^ (4147 / 5000 : ℝ))
    have htwo : (2 : ℝ) ≤ (p : ℝ) ^ (4147 / 5000 : ℝ) := by
      rw [Real.rpow_def_of_pos hpR]
      have he := Real.add_one_le_exp (Real.log p * (4147 / 5000 : ℝ))
      nlinarith only [hL, he]
    nlinarith only [hf, htwo]
  have hdelta : (1 / 10000 : ℝ) ≤ 1 + 4147 / 5000 - 150 / 82 := by norm_num only
  have hdeltaPos : (0 : ℝ) < 1 + 4147 / 5000 - 150 / 82 := lt_of_lt_of_le (by norm_num only) hdelta
  have hmul := mul_le_mul hL hdelta (by norm_num only : (0 : ℝ) ≤ 1 / 10000) (by linarith only [hL])
  have hgap : (1024 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) + 4147 / 5000 - 150 / 82) := by
    have he := Real.add_one_le_exp (Real.log p * ((1 : ℝ) + 4147 / 5000 - 150 / 82))
    have hexp :
      Real.exp (Real.log p * (1 + 4147 / 5000 - 150 / 82)) =
        (p : ℝ) ^ ((1 : ℝ) + 4147 / 5000 - 150 / 82) :=
      (Real.rpow_def_of_pos hpR ((1 : ℝ) + 4147 / 5000 - 150 / 82)).symm
    exact
      (show (1024 : ℝ) ≤ Real.exp (Real.log p * ((1 : ℝ) + 4147 / 5000 - 150 / 82)) by
            nlinarith only [hmul, he]).trans_eq
        hexp
  have hpower : 1024 * (p : ℝ) ^ (150 / 82 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) + 4147 / 5000) := by
    calc
      _ ≤ (p : ℝ) ^ ((1 : ℝ) + 4147 / 5000 - 150 / 82) * (p : ℝ) ^ (150 / 82 : ℝ) :=
        mul_le_mul_of_nonneg_right hgap (Real.rpow_nonneg hpR.le _)
      _ = (p : ℝ) ^ ((1 + 4147 / 5000 - 150 / 82) + (150 / 82 : ℝ)) :=
        (Real.rpow_add hpR ((1 : ℝ) + 4147 / 5000 - 150 / 82) (150 / 82 : ℝ)).symm
      _ = _ := by
        congr 1; norm_num only
  have hscale : 512 * (p : ℝ) ^ (150 / 82 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) + 4147 / 5000) / 2 := by
    apply (le_div_iff₀ (by norm_num only : (0 : ℝ) < 2)).2
    calc
      512 * (p : ℝ) ^ (150 / 82 : ℝ) * 2 = 1024 * (p : ℝ) ^ (150 / 82 : ℝ) := by ring
      _ ≤ _ := hpower
  have hfloor :
    (p : ℝ) * (p : ℝ) ^ (4147 / 5000 : ℝ) / 2 ≤
      (p : ℝ) * (Nat.floor ((p : ℝ) ^ (4147 / 5000 : ℝ)) : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hbeta hpR.le
    have hd := div_le_div_of_nonneg_right hm (by norm_num only : (0 : ℝ) ≤ 2)
    calc
      _ ≤ (p : ℝ) * (2 * (Nat.floor ((p : ℝ) ^ (4147 / 5000 : ℝ)) : ℝ)) / 2 := hd
      _ = _ := by ring
  have hexp : (p : ℝ) ^ ((1 : ℝ) + 4147 / 5000) = (p : ℝ) * (p : ℝ) ^ (4147 / 5000 : ℝ) := by
    rw [Real.rpow_add hpR, Real.rpow_one]
  have hk := rational_cutoff_le_two_rpow (a := 82) (b := 150) (by decide) hcut
  have hk' : (256 : ℝ) * k ≤ 512 * (p : ℝ) ^ (150 / 82 : ℝ) := by
    have hkReal : (k : ℝ) ≤ 2 * (p : ℝ) ^ (150 / 82 : ℝ) := by exact_mod_cast hk
    calc
      _ ≤ 256 * (2 * (p : ℝ) ^ (150 / 82 : ℝ)) :=
        mul_le_mul_of_nonneg_left hkReal (by norm_num only)
      _ = _ := by ring
  have hbound := hk'.trans (hscale.trans_eq (congrArg (fun x : ℝ ↦ x / 2) hexp))
  have hresult := hbound.trans hfloor
  exact (Nat.cast_le (α := ℝ)).mp (by exact_mod_cast hresult)

/-- At the rational cutoff 150/82, any exponent at least 8292684/10000000
absorbs the cutoff constant and floor loss when log p≥10^12. -/
theorem rational_cutoff_150_82_le_prime_mul_floor_of_beta {p k : ℕ} {beta : ℝ} (hp : 0 < p)
    (hL : (10 : ℝ) ^ 12 ≤ Real.log p) (hbeta : 8292684 / 10000000 ≤ beta)
    (hcut : k ^ 82 ≤ 2 ^ 82 * p ^ 150) : 256 * k ≤ p * Nat.floor ((p : ℝ) ^ beta) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hbetamin : (1 / 2 : ℝ) ≤ beta := by linarith only [hbeta]
  have hfloor : (p : ℝ) ^ beta ≤ 2 * (Nat.floor ((p : ℝ) ^ beta) : ℝ) := by
    have hf := Nat.lt_floor_add_one ((p : ℝ) ^ beta)
    have htwo : (2 : ℝ) ≤ (p : ℝ) ^ beta := by
      rw [Real.rpow_def_of_pos hpR]
      have he := Real.add_one_le_exp (Real.log p * beta)
      have hm :=
        mul_le_mul hL hbetamin (by norm_num only : (0 : ℝ) ≤ (1 / 2 : ℝ)) (by linarith only [hL])
      have hbig : (10 : ℝ) ^ 12 * (1 / 2 : ℝ) ≤ Real.log p * beta := by nlinarith only [hm]
      nlinarith only [hbig, he]
    nlinarith only [hf, htwo]
  have hdelta : (1 / 10000000 : ℝ) ≤ 1 + beta - 150 / 82 := by nlinarith only [hbeta]
  have hmul :=
    mul_le_mul hL hdelta (by norm_num only : (0 : ℝ) ≤ 1 / 10000000) (by linarith only [hL])
  have hgap : (1024 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) + beta - 150 / 82) := by
    have he := Real.add_one_le_exp (Real.log p * ((1 : ℝ) + beta - 150 / 82))
    have hexp :
      Real.exp (Real.log p * (1 + beta - 150 / 82)) = (p : ℝ) ^ ((1 : ℝ) + beta - 150 / 82) :=
      (Real.rpow_def_of_pos hpR ((1 : ℝ) + beta - 150 / 82)).symm
    exact
      (show (1024 : ℝ) ≤ Real.exp (Real.log p * ((1 : ℝ) + beta - 150 / 82)) by
            nlinarith only [hmul, he]).trans_eq
        hexp
  have hpower : 1024 * (p : ℝ) ^ (150 / 82 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) + beta) := by
    calc
      _ ≤ (p : ℝ) ^ ((1 : ℝ) + beta - 150 / 82) * (p : ℝ) ^ (150 / 82 : ℝ) :=
        mul_le_mul_of_nonneg_right hgap (Real.rpow_nonneg hpR.le _)
      _ = (p : ℝ) ^ ((1 + beta - 150 / 82) + (150 / 82 : ℝ)) :=
        (Real.rpow_add hpR ((1 : ℝ) + beta - 150 / 82) (150 / 82 : ℝ)).symm
      _ = _ := by
        congr 1; ring
  have hscale : 512 * (p : ℝ) ^ (150 / 82 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) + beta) / 2 := by
    apply (le_div_iff₀ (by norm_num only : (0 : ℝ) < 2)).2
    calc
      512 * (p : ℝ) ^ (150 / 82 : ℝ) * 2 = 1024 * (p : ℝ) ^ (150 / 82 : ℝ) := by ring
      _ ≤ _ := hpower
  have hfloor' : (p : ℝ) * (p : ℝ) ^ beta / 2 ≤ (p : ℝ) * (Nat.floor ((p : ℝ) ^ beta) : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hfloor hpR.le
    have hd := div_le_div_of_nonneg_right hm (by norm_num only : (0 : ℝ) ≤ 2)
    calc
      _ ≤ (p : ℝ) * (2 * (Nat.floor ((p : ℝ) ^ beta) : ℝ)) / 2 := hd
      _ = _ := by ring
  have hexp : (p : ℝ) ^ ((1 : ℝ) + beta) = (p : ℝ) * (p : ℝ) ^ beta := by
    rw [Real.rpow_add hpR, Real.rpow_one]
  have hk := rational_cutoff_le_two_rpow (a := 82) (b := 150) (by decide) hcut
  have hk' : (256 : ℝ) * k ≤ 512 * (p : ℝ) ^ (150 / 82 : ℝ) := by
    have hkReal : (k : ℝ) ≤ 2 * (p : ℝ) ^ (150 / 82 : ℝ) := by exact_mod_cast hk
    calc
      _ ≤ 256 * (2 * (p : ℝ) ^ (150 / 82 : ℝ)) :=
        mul_le_mul_of_nonneg_left hkReal (by norm_num only)
      _ = _ := by ring
  have hbound := hk'.trans (hscale.trans_eq (congrArg (fun x : ℝ ↦ x / 2) hexp))
  have hresult := hbound.trans hfloor'
  exact (Nat.cast_le (α := ℝ)).mp (by exact_mod_cast hresult)

/-- Inputs: `p > 0`, `log p ≥ 10^12`, and `k^16 ≤ 2^16 * p^30`.
Claim: `256 * k ≤ p * floor(p^(87501/100000))`.
Content: The cutoff bounds `k` by `2 * p^(15/8)`; the remaining exponent
gap absorbs the constant and floor loss. Proof: Use real-power monotonicity
and the exponential lower bound at `log p / 100000`. Role: Supplies the
smooth-number count required by the 30/16 finite-fiber branch. -/
theorem rational_cutoff_30_16_le_prime_mul_floor {p k : ℕ} (hp : 0 < p)
    (hL : (10 : ℝ) ^ 12 ≤ Real.log p) (hcut : k ^ 16 ≤ 2 ^ 16 * p ^ 30) :
    256 * k ≤ p * Nat.floor ((p : ℝ) ^ (87501 / 100000 : ℝ)) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hfloor :
    (p : ℝ) ^ (87501 / 100000 : ℝ) ≤ 2 * (Nat.floor ((p : ℝ) ^ (87501 / 100000 : ℝ)) : ℝ) := by
    have hf := Nat.lt_floor_add_one ((p : ℝ) ^ (87501 / 100000 : ℝ))
    have htwo : (2 : ℝ) ≤ (p : ℝ) ^ (87501 / 100000 : ℝ) := by
      rw [Real.rpow_def_of_pos hpR]
      have he := Real.add_one_le_exp (Real.log p * (87501 / 100000 : ℝ))
      nlinarith only [hL, he]
    nlinarith only [hf, htwo]
  have hroot : (k : ℝ) ≤ 2 * (p : ℝ) ^ (15 / 8 : ℝ) := by
    have hcutR : (k : ℝ) ^ 16 ≤ 2 ^ 16 * (p : ℝ) ^ (30 : ℕ) := by exact_mod_cast hcut
    have heq : (2 * (p : ℝ) ^ (15 / 8 : ℝ)) ^ (16 : ℕ) = 2 ^ 16 * (p : ℝ) ^ (30 : ℕ) := by
      rw [mul_pow]
      calc
        2 ^ 16 * ((p : ℝ) ^ (15 / 8 : ℝ)) ^ (16 : ℕ) = 2 ^ 16 * (p : ℝ) ^ ((15 / 8 : ℝ) * 16) := by
          rw [← Real.rpow_mul_natCast hpR.le]
          norm_num only
        _ = 2 ^ 16 * (p : ℝ) ^ (30 : ℕ) := by
          rw [← Real.rpow_natCast (p : ℝ) 30]
          norm_num only
    have hpow : (k : ℝ) ^ (16 : ℝ) ≤ (2 * (p : ℝ) ^ (15 / 8 : ℝ)) ^ (16 : ℝ) := by
      calc
        _ = (k : ℝ) ^ (16 : ℕ) := Real.rpow_natCast _ _
        _ ≤ 2 ^ 16 * (p : ℝ) ^ (30 : ℕ) := hcutR
        _ = (2 * (p : ℝ) ^ (15 / 8 : ℝ)) ^ (16 : ℕ) := heq.symm
        _ = _ := (Real.rpow_natCast _ _).symm
    exact
      (Real.rpow_le_rpow_iff (Nat.cast_nonneg k) (by positivity)
            (by norm_num only : (0 : ℝ) < 16)).mp
        hpow
  have hmul : 10 ^ 12 * (1 / 100000 : ℝ) ≤ Real.log p * (1 / 100000 : ℝ) := by nlinarith only [hL]
  have hgap : (2 ^ 10 : ℝ) ≤ (p : ℝ) ^ (1 / 100000 : ℝ) := by
    rw [Real.rpow_def_of_pos hpR]
    have he := Real.add_one_le_exp (Real.log p * (1 / 100000 : ℝ))
    norm_num only at he ⊢
    nlinarith only [hmul, he]
  have hpower : 512 * (p : ℝ) ^ (15 / 8 : ℝ) ≤ (p : ℝ) ^ (1 + 87501 / 100000 : ℝ) / 2 := by
    apply (le_div_iff₀ (by norm_num only : (0 : ℝ) < 2)).2
    calc
      512 * (p : ℝ) ^ (15 / 8 : ℝ) * 2 = 2 ^ 10 * (p : ℝ) ^ (15 / 8 : ℝ) := by ring_nf
      _ ≤ (p : ℝ) ^ (1 / 100000 : ℝ) * (p : ℝ) ^ (15 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right hgap (Real.rpow_nonneg hpR.le _)
      _ = (p : ℝ) ^ (1 + 87501 / 100000 : ℝ) := by
        rw [← Real.rpow_add hpR]
        congr 1
        ring
  have hexp : (p : ℝ) ^ (1 + 87501 / 100000 : ℝ) = (p : ℝ) * (p : ℝ) ^ (87501 / 100000 : ℝ) := by
    rw [Real.rpow_add hpR, Real.rpow_one]
  have hbound : (256 : ℝ) * k ≤ 512 * (p : ℝ) ^ (15 / 8 : ℝ) := by
    calc
      _ ≤ 256 * (2 * (p : ℝ) ^ (15 / 8 : ℝ)) := mul_le_mul_of_nonneg_left hroot (by norm_num only)
      _ = _ := by ring
  have hresult := hbound.trans hpower
  rw [hexp] at hresult
  have hfloor' := mul_le_mul_of_nonneg_left hfloor hpR.le
  have hdivide :
    (p : ℝ) * (p : ℝ) ^ (87501 / 100000 : ℝ) / 2 ≤
      (p : ℝ) * (Nat.floor ((p : ℝ) ^ (87501 / 100000 : ℝ)) : ℝ) := by
    apply (div_le_iff₀ (by norm_num only : (0 : ℝ) < 2)).2
    nlinarith only [hfloor']
  have hreal : (256 : ℝ) * k ≤ (p : ℝ) * (Nat.floor ((p : ℝ) ^ (87501 / 100000 : ℝ)) : ℝ) :=
    hresult.trans hdivide
  exact_mod_cast hreal

/-- Inputs: `p > 0`, `log p ≥ 10^12`, and `k^15 ≤ 2^15 p^28`.
Claim: `256 k ≤ p floor(p^(8668/10000))`. The cutoff root gives
`k ≤ 2 p^(28/15)`; the exponent gap `1/7500` absorbs the factor and floor
loss. This supplies the smooth-count estimate for the 28/15 finite-fiber
branch. -/
theorem rational_cutoff_28_15_le_prime_mul_floor {p k : ℕ} (hp : 0 < p)
    (hL : (10 : ℝ) ^ 12 ≤ Real.log p) (hcut : k ^ 15 ≤ 2 ^ 15 * p ^ 28) :
    256 * k ≤ p * Nat.floor ((p : ℝ) ^ (8668 / 10000 : ℝ)) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hfloor :
    (p : ℝ) ^ (8668 / 10000 : ℝ) ≤ 2 * (Nat.floor ((p : ℝ) ^ (8668 / 10000 : ℝ)) : ℝ) := by
    have hf := Nat.lt_floor_add_one ((p : ℝ) ^ (8668 / 10000 : ℝ))
    have htwo : (2 : ℝ) ≤ (p : ℝ) ^ (8668 / 10000 : ℝ) := by
      rw [Real.rpow_def_of_pos hpR]
      have he := Real.add_one_le_exp (Real.log p * (8668 / 10000 : ℝ))
      nlinarith only [hL, he]
    nlinarith only [hf, htwo]
  have hroot := rational_cutoff_le_two_rpow (a := 15) (b := 28) (by norm_num only) hcut
  have hmul : 10 ^ 12 * (1 / 7500 : ℝ) ≤ Real.log p * (1 / 7500 : ℝ) := by nlinarith only [hL]
  have hgap : (2 ^ 10 : ℝ) ≤ (p : ℝ) ^ (1 / 7500 : ℝ) := by
    rw [Real.rpow_def_of_pos hpR]
    have he := Real.add_one_le_exp (Real.log p * (1 / 7500 : ℝ))
    norm_num only at he ⊢
    nlinarith only [hmul, he]
  have hpower : 512 * (p : ℝ) ^ (28 / 15 : ℝ) ≤ (p : ℝ) ^ (1 + 8668 / 10000 : ℝ) / 2 := by
    apply (le_div_iff₀ (by norm_num only : (0 : ℝ) < 2)).2
    calc
      512 * (p : ℝ) ^ (28 / 15 : ℝ) * 2 = 2 ^ 10 * (p : ℝ) ^ (28 / 15 : ℝ) := by ring_nf
      _ ≤ (p : ℝ) ^ (1 / 7500 : ℝ) * (p : ℝ) ^ (28 / 15 : ℝ) :=
        mul_le_mul_of_nonneg_right hgap (Real.rpow_nonneg hpR.le _)
      _ = (p : ℝ) ^ (1 + 8668 / 10000 : ℝ) := by
        rw [← Real.rpow_add hpR]
        congr 1
        ring
  have hexp : (p : ℝ) ^ (1 + 8668 / 10000 : ℝ) = (p : ℝ) * (p : ℝ) ^ (8668 / 10000 : ℝ) := by
    rw [Real.rpow_add hpR, Real.rpow_one]
  have hbound : (256 : ℝ) * k ≤ 512 * (p : ℝ) ^ (28 / 15 : ℝ) := by
    calc
      _ ≤ 256 * (2 * (p : ℝ) ^ (28 / 15 : ℝ)) := mul_le_mul_of_nonneg_left hroot (by norm_num only)
      _ = _ := by ring
  have hresult := hbound.trans hpower
  rw [hexp] at hresult
  have hfloor' := mul_le_mul_of_nonneg_left hfloor hpR.le
  have hdivide :
    (p : ℝ) * (p : ℝ) ^ (8668 / 10000 : ℝ) / 2 ≤
      (p : ℝ) * (Nat.floor ((p : ℝ) ^ (8668 / 10000 : ℝ)) : ℝ) := by
    apply (div_le_iff₀ (by norm_num only : (0 : ℝ) < 2)).2
    nlinarith only [hfloor']
  have hreal : (256 : ℝ) * k ≤ (p : ℝ) * (Nat.floor ((p : ℝ) ^ (8668 / 10000 : ℝ)) : ℝ) :=
    hresult.trans hdivide
  exact_mod_cast hreal

/-- Inputs: `p > 0`, `log p ≥ 10^12`, and `k^15 ≤ 2^15 p^28`.
Claim: `256 k ≤ p floor(p^(8666667/10000000))`. The cutoff root is bounded
by `2 p^(28/15)`, and the exponent gap `1/30000000` absorbs the factor and
floor loss. -/
theorem rational_cutoff_28_15_le_prime_mul_floor_beta {p k : ℕ} (hp : 0 < p)
    (hL : (10 : ℝ) ^ 12 ≤ Real.log p) (hcut : k ^ 15 ≤ 2 ^ 15 * p ^ 28) :
    256 * k ≤ p * Nat.floor ((p : ℝ) ^ (8666667 / 10000000 : ℝ)) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hfloor :
    (p : ℝ) ^ (8666667 / 10000000 : ℝ) ≤
      2 * (Nat.floor ((p : ℝ) ^ (8666667 / 10000000 : ℝ)) : ℝ) := by
    have hf := Nat.lt_floor_add_one ((p : ℝ) ^ (8666667 / 10000000 : ℝ))
    have htwo : (2 : ℝ) ≤ (p : ℝ) ^ (8666667 / 10000000 : ℝ) := by
      rw [Real.rpow_def_of_pos hpR]
      have he := Real.add_one_le_exp (Real.log p * (8666667 / 10000000 : ℝ))
      nlinarith only [hL, he]
    nlinarith only [hf, htwo]
  have hroot := rational_cutoff_le_two_rpow (a := 15) (b := 28) (by norm_num only) hcut
  have hmul : 10 ^ 12 * (1 / 30000000 : ℝ) ≤ Real.log p * (1 / 30000000 : ℝ) := by
    nlinarith only [hL]
  have hgap : (2 ^ 10 : ℝ) ≤ (p : ℝ) ^ (1 / 30000000 : ℝ) := by
    rw [Real.rpow_def_of_pos hpR]
    have he := Real.add_one_le_exp (Real.log p * (1 / 30000000 : ℝ))
    norm_num only at he ⊢
    nlinarith only [hmul, he]
  have hpower : 512 * (p : ℝ) ^ (28 / 15 : ℝ) ≤ (p : ℝ) ^ (1 + 8666667 / 10000000 : ℝ) / 2 := by
    apply (le_div_iff₀ (by norm_num only : (0 : ℝ) < 2)).2
    calc
      512 * (p : ℝ) ^ (28 / 15 : ℝ) * 2 = 2 ^ 10 * (p : ℝ) ^ (28 / 15 : ℝ) := by ring_nf
      _ ≤ (p : ℝ) ^ (1 / 30000000 : ℝ) * (p : ℝ) ^ (28 / 15 : ℝ) :=
        mul_le_mul_of_nonneg_right hgap (Real.rpow_nonneg hpR.le _)
      _ = (p : ℝ) ^ (1 + 8666667 / 10000000 : ℝ) := by
        rw [← Real.rpow_add hpR]
        congr 1
        ring
  have hexp :
    (p : ℝ) ^ (1 + 8666667 / 10000000 : ℝ) = (p : ℝ) * (p : ℝ) ^ (8666667 / 10000000 : ℝ) := by
    rw [Real.rpow_add hpR, Real.rpow_one]
  have hbound : (256 : ℝ) * k ≤ 512 * (p : ℝ) ^ (28 / 15 : ℝ) := by
    calc
      _ ≤ 256 * (2 * (p : ℝ) ^ (28 / 15 : ℝ)) := mul_le_mul_of_nonneg_left hroot (by norm_num only)
      _ = _ := by ring
  have hresult := hbound.trans hpower
  rw [hexp] at hresult
  have hfloor' := mul_le_mul_of_nonneg_left hfloor hpR.le
  have hdivide :
    (p : ℝ) * (p : ℝ) ^ (8666667 / 10000000 : ℝ) / 2 ≤
      (p : ℝ) * (Nat.floor ((p : ℝ) ^ (8666667 / 10000000 : ℝ)) : ℝ) := by
    apply (div_le_iff₀ (by norm_num only : (0 : ℝ) < 2)).2
    nlinarith only [hfloor']
  have hreal : (256 : ℝ) * k ≤ (p : ℝ) * (Nat.floor ((p : ℝ) ^ (8666667 / 10000000 : ℝ)) : ℝ) :=
    hresult.trans hdivide
  exact_mod_cast hreal

/-- Inputs: `p>0`, `log p≥10^12`, a cutoff `k^15≤2^15 p^28`, and
`beta≥13/15+10^-11`. Claim: `256k≤p floor(p^beta)`. The proof uses the
small exponent gap to absorb the fixed cutoff and the floor loss. Role:
supports 28/15 finite-fiber bounds with a sharper smooth-number exponent. -/
theorem rational_cutoff_28_15_le_prime_mul_floor_of_beta {p k : ℕ} {beta : ℝ} (hp : 0 < p)
    (hL : (10 : ℝ) ^ 12 ≤ Real.log p) (hbeta : 13 / 15 + 1 / 100000000000 ≤ beta)
    (hcut : k ^ 15 ≤ 2 ^ 15 * p ^ 28) : 256 * k ≤ p * Nat.floor ((p : ℝ) ^ beta) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hfloor : (p : ℝ) ^ beta ≤ 2 * (Nat.floor ((p : ℝ) ^ beta) : ℝ) := by
    have hf := Nat.lt_floor_add_one ((p : ℝ) ^ beta)
    have htwo : (2 : ℝ) ≤ (p : ℝ) ^ beta := by
      rw [Real.rpow_def_of_pos hpR]
      have he := Real.add_one_le_exp (Real.log p * beta)
      have hbetamin : (1 / 2 : ℝ) ≤ beta := by linarith only [hbeta]
      have hLnonneg : 0 ≤ Real.log p := by linarith only [hL]
      have hprod : 1 ≤ Real.log p * beta := by
        calc
          1 ≤ Real.log p * (1 / 2 : ℝ) := by nlinarith only [hL]
          _ ≤ Real.log p * beta := mul_le_mul_of_nonneg_left hbetamin hLnonneg
      nlinarith only [he, hprod]
    nlinarith only [hf, htwo]
  have hroot := rational_cutoff_le_two_rpow (a := 15) (b := 28) (by norm_num only) hcut
  have hmul : 10 ≤ Real.log p * (1 / 100000000000 : ℝ) := by nlinarith only [hL]
  have hgap : (2 ^ 10 : ℝ) ≤ (p : ℝ) ^ (1 / 100000000000 : ℝ) := by
    rw [Real.rpow_def_of_pos hpR]
    have hE1 : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
    have hEpow : (2 : ℝ) ^ 10 ≤ Real.exp 1 ^ 10 := pow_le_pow_left₀ (by norm_num only) hE1 10
    have hexp10 : Real.exp 1 ^ 10 = Real.exp 10 := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num only
    calc
      _ ≤ Real.exp 1 ^ 10 := hEpow
      _ = Real.exp 10 := hexp10
      _ ≤ Real.exp (Real.log p * (1 / 100000000000 : ℝ)) := Real.exp_le_exp.mpr hmul
  have hpOne : (1 : ℝ) ≤ p := by
    by_contra h
    have hp_lt : (p : ℝ) < 1 := lt_of_not_ge h
    have hlog := Real.log_le_log hpR hp_lt.le
    rw [Real.log_one] at hlog
    linarith only [hL, hlog]
  have hbetaGap : (1 / 100000000000 : ℝ) ≤ beta - 13 / 15 := by linarith only [hbeta]
  have hpower : 512 * (p : ℝ) ^ (28 / 15 : ℝ) ≤ (p : ℝ) ^ (1 + beta) / 2 := by
    apply (le_div_iff₀ (by norm_num only : (0 : ℝ) < 2)).2
    calc
      512 * (p : ℝ) ^ (28 / 15 : ℝ) * 2 = 2 ^ 10 * (p : ℝ) ^ (28 / 15 : ℝ) := by ring_nf
      _ ≤ (p : ℝ) ^ (1 / 100000000000 : ℝ) * (p : ℝ) ^ (28 / 15 : ℝ) :=
        mul_le_mul_of_nonneg_right hgap (Real.rpow_nonneg hpR.le _)
      _ = (p : ℝ) ^ ((1 / 100000000000 : ℝ) + 28 / 15) := by rw [← Real.rpow_add hpR]
      _ ≤ (p : ℝ) ^ (1 + beta) :=
        Real.rpow_le_rpow_of_exponent_le hpOne (by nlinarith only [hbetaGap])
  have hexp : (p : ℝ) ^ (1 + beta) = (p : ℝ) * (p : ℝ) ^ beta := by
    rw [Real.rpow_add hpR, Real.rpow_one]
  have hbound : (256 : ℝ) * k ≤ 512 * (p : ℝ) ^ (28 / 15 : ℝ) := by
    calc
      _ ≤ 256 * (2 * (p : ℝ) ^ (28 / 15 : ℝ)) := mul_le_mul_of_nonneg_left hroot (by norm_num only)
      _ = _ := by ring
  have hresult := hbound.trans hpower
  rw [hexp] at hresult
  have hfloor' := mul_le_mul_of_nonneg_left hfloor hpR.le
  have hdivide : (p : ℝ) * (p : ℝ) ^ beta / 2 ≤ (p : ℝ) * (Nat.floor ((p : ℝ) ^ beta) : ℝ) := by
    apply (div_le_iff₀ (by norm_num only : (0 : ℝ) < 2)).2
    nlinarith only [hfloor']
  have hreal : (256 : ℝ) * k ≤ (p : ℝ) * (Nat.floor ((p : ℝ) ^ beta) : ℝ) := hresult.trans hdivide
  exact_mod_cast hreal

/-- For the rational scale 192/105, a smooth exponent at least
`87/105 + 1/200000` absorbs the cutoff factor and floor loss once
`ln p ≥ 10^12`. -/
theorem rational_cutoff_192_105_le_prime_mul_floor_of_beta {p k : ℕ} {beta : ℝ} (hp : 0 < p)
    (hL : (10 : ℝ) ^ 12 ≤ Real.log p) (hbeta : 87 / 105 + 1 / 200000 ≤ beta)
    (hcut : k ^ 105 ≤ 2 ^ 105 * p ^ 192) : 256 * k ≤ p * Nat.floor ((p : ℝ) ^ beta) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hfloor : (p : ℝ) ^ beta ≤ 2 * (Nat.floor ((p : ℝ) ^ beta) : ℝ) := by
    have hf := Nat.lt_floor_add_one ((p : ℝ) ^ beta)
    have htwo : (2 : ℝ) ≤ (p : ℝ) ^ beta := by
      rw [Real.rpow_def_of_pos hpR]
      have he := Real.add_one_le_exp (Real.log p * beta)
      have hbetamin : (1 / 2 : ℝ) ≤ beta := by linarith only [hbeta]
      have hLnonneg : 0 ≤ Real.log p := by linarith only [hL]
      have hprod : 1 ≤ Real.log p * beta := by
        calc
          1 ≤ Real.log p * (1 / 2 : ℝ) := by nlinarith only [hL]
          _ ≤ Real.log p * beta := mul_le_mul_of_nonneg_left hbetamin hLnonneg
      nlinarith only [he, hprod]
    nlinarith only [hf, htwo]
  have hroot := rational_cutoff_le_two_rpow (a := 105) (b := 192) (by norm_num only) hcut
  have hmul : 10 ≤ Real.log p * (1 / 200000 : ℝ) := by nlinarith only [hL]
  have hgap : (2 ^ 10 : ℝ) ≤ (p : ℝ) ^ (1 / 200000 : ℝ) := by
    rw [Real.rpow_def_of_pos hpR]
    have hE1 : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
    have hEpow : (2 : ℝ) ^ 10 ≤ Real.exp 1 ^ 10 := pow_le_pow_left₀ (by norm_num only) hE1 10
    have hexp10 : Real.exp 1 ^ 10 = Real.exp 10 := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num only
    calc
      _ ≤ Real.exp 1 ^ 10 := hEpow
      _ = Real.exp 10 := hexp10
      _ ≤ Real.exp (Real.log p * (1 / 200000 : ℝ)) := Real.exp_le_exp.mpr hmul
  have hpOne : (1 : ℝ) ≤ p := by
    by_contra h
    have hp_lt : (p : ℝ) < 1 := lt_of_not_ge h
    have hlog := Real.log_le_log hpR hp_lt.le
    rw [Real.log_one] at hlog
    linarith only [hL, hlog]
  have hbetaGap : (1 / 200000 : ℝ) ≤ beta - 87 / 105 := by linarith only [hbeta]
  have hpower : 512 * (p : ℝ) ^ (192 / 105 : ℝ) ≤ (p : ℝ) ^ (1 + beta) / 2 := by
    apply (le_div_iff₀ (by norm_num only : (0 : ℝ) < 2)).2
    calc
      512 * (p : ℝ) ^ (192 / 105 : ℝ) * 2 = 2 ^ 10 * (p : ℝ) ^ (192 / 105 : ℝ) := by ring_nf
      _ ≤ (p : ℝ) ^ (1 / 200000 : ℝ) * (p : ℝ) ^ (192 / 105 : ℝ) :=
        mul_le_mul_of_nonneg_right hgap (Real.rpow_nonneg hpR.le _)
      _ = (p : ℝ) ^ ((1 / 200000 : ℝ) + 192 / 105) := by rw [← Real.rpow_add hpR]
      _ ≤ (p : ℝ) ^ (1 + beta) :=
        Real.rpow_le_rpow_of_exponent_le hpOne (by nlinarith only [hbetaGap])
  have hexp : (p : ℝ) ^ (1 + beta) = (p : ℝ) * (p : ℝ) ^ beta := by
    rw [Real.rpow_add hpR, Real.rpow_one]
  have hbound : (256 : ℝ) * k ≤ 512 * (p : ℝ) ^ (192 / 105 : ℝ) := by
    calc
      _ ≤ 256 * (2 * (p : ℝ) ^ (192 / 105 : ℝ)) :=
        mul_le_mul_of_nonneg_left hroot (by norm_num only)
      _ = _ := by ring
  have hresult := hbound.trans hpower
  rw [hexp] at hresult
  have hfloor' := mul_le_mul_of_nonneg_left hfloor hpR.le
  have hdivide : (p : ℝ) * (p : ℝ) ^ beta / 2 ≤ (p : ℝ) * (Nat.floor ((p : ℝ) ^ beta) : ℝ) := by
    apply (div_le_iff₀ (by norm_num only : (0 : ℝ) < 2)).2
    nlinarith only [hfloor']
  have hreal : (256 : ℝ) * k ≤ (p : ℝ) * (Nat.floor ((p : ℝ) ^ beta) : ℝ) := hresult.trans hdivide
  exact_mod_cast hreal

/-- For the equivalent scale 2048/1120, the same smooth exponent and floor
loss bound the cutoff by the prime-weighted floor. The generic rational-power
estimate converts the integer cutoff to the reduced ratio 192/105. -/
theorem rational_cutoff_2048_1120_le_prime_mul_floor_of_beta {p k : ℕ} {beta : ℝ} (hp : 0 < p)
    (hL : (10 : ℝ) ^ 12 ≤ Real.log p) (hbeta : 87 / 105 + 1 / 200000 ≤ beta)
    (hcut : k ^ 1120 ≤ 2 ^ 1120 * p ^ 2048) : 256 * k ≤ p * Nat.floor ((p : ℝ) ^ beta) := by
  have hroot := rational_cutoff_le_two_rpow (a := 1120) (b := 2048) (by norm_num only) hcut
  have hcast : (↑(2048 : ℕ) : ℝ) / ↑(1120 : ℕ) = 192 / 105 := by norm_num only
  rw [hcast] at hroot
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hfloor : (p : ℝ) ^ beta ≤ 2 * (Nat.floor ((p : ℝ) ^ beta) : ℝ) := by
    have hf := Nat.lt_floor_add_one ((p : ℝ) ^ beta)
    have htwo : (2 : ℝ) ≤ (p : ℝ) ^ beta := by
      rw [Real.rpow_def_of_pos hpR]
      have he := Real.add_one_le_exp (Real.log p * beta)
      have hbetamin : (1 / 2 : ℝ) ≤ beta := by linarith only [hbeta]
      have hLnonneg : 0 ≤ Real.log p := by linarith only [hL]
      have hprod : 1 ≤ Real.log p * beta := by
        calc
          1 ≤ Real.log p * (1 / 2 : ℝ) := by nlinarith only [hL]
          _ ≤ Real.log p * beta := mul_le_mul_of_nonneg_left hbetamin hLnonneg
      nlinarith only [he, hprod]
    nlinarith only [hf, htwo]
  have hmul : 10 ≤ Real.log p * (1 / 200000 : ℝ) := by nlinarith only [hL]
  have hgap : (2 ^ 10 : ℝ) ≤ (p : ℝ) ^ (1 / 200000 : ℝ) := by
    rw [Real.rpow_def_of_pos hpR]
    have hE1 : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
    have hEpow : (2 : ℝ) ^ 10 ≤ Real.exp 1 ^ 10 := pow_le_pow_left₀ (by norm_num only) hE1 10
    have hexp10 : Real.exp 1 ^ 10 = Real.exp 10 := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num only
    calc
      _ ≤ Real.exp 1 ^ 10 := hEpow
      _ = Real.exp 10 := hexp10
      _ ≤ Real.exp (Real.log p * (1 / 200000 : ℝ)) := Real.exp_le_exp.mpr hmul
  have hpOne : (1 : ℝ) ≤ p := by
    by_contra h
    have hp_lt : (p : ℝ) < 1 := lt_of_not_ge h
    have hlog := Real.log_le_log hpR hp_lt.le
    rw [Real.log_one] at hlog
    linarith only [hL, hlog]
  have hbetaGap : (1 / 200000 : ℝ) ≤ beta - 87 / 105 := by linarith only [hbeta]
  have hpower : 512 * (p : ℝ) ^ (192 / 105 : ℝ) ≤ (p : ℝ) ^ (1 + beta) / 2 := by
    apply (le_div_iff₀ (by norm_num only : (0 : ℝ) < 2)).2
    calc
      512 * (p : ℝ) ^ (192 / 105 : ℝ) * 2 = 2 ^ 10 * (p : ℝ) ^ (192 / 105 : ℝ) := by ring_nf
      _ ≤ (p : ℝ) ^ (1 / 200000 : ℝ) * (p : ℝ) ^ (192 / 105 : ℝ) :=
        mul_le_mul_of_nonneg_right hgap (Real.rpow_nonneg hpR.le _)
      _ = (p : ℝ) ^ ((1 / 200000 : ℝ) + 192 / 105) := by rw [← Real.rpow_add hpR]
      _ ≤ (p : ℝ) ^ (1 + beta) :=
        Real.rpow_le_rpow_of_exponent_le hpOne (by nlinarith only [hbetaGap])
  have hexp : (p : ℝ) ^ (1 + beta) = (p : ℝ) * (p : ℝ) ^ beta := by
    rw [Real.rpow_add hpR, Real.rpow_one]
  have hbound : (256 : ℝ) * k ≤ 512 * (p : ℝ) ^ (192 / 105 : ℝ) := by
    calc
      _ ≤ 256 * (2 * (p : ℝ) ^ (192 / 105 : ℝ)) :=
        mul_le_mul_of_nonneg_left hroot (by norm_num only)
      _ = _ := by ring
  have hresult := hbound.trans hpower
  rw [hexp] at hresult
  have hfloor' := mul_le_mul_of_nonneg_left hfloor hpR.le
  have hdivide : (p : ℝ) * (p : ℝ) ^ beta / 2 ≤ (p : ℝ) * (Nat.floor ((p : ℝ) ^ beta) : ℝ) := by
    apply (div_le_iff₀ (by norm_num only : (0 : ℝ) < 2)).2
    nlinarith only [hfloor']
  have hreal : (256 : ℝ) * k ≤ (p : ℝ) * (Nat.floor ((p : ℝ) ^ beta) : ℝ) := hresult.trans hdivide
  exact_mod_cast hreal

end PseudoPrime.Analysis
