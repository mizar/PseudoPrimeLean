/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SmallSubgroupLogarithmicBudget
public import PseudoPrime.NumberTheory.PrimeCountPowerLower

/-! # Logarithmic budgets for smooth products at the Heilbronn cutoff -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A strict product logarithm below (28/15)log p lies below any cutoff k with p^28<=k^15.
The bound retains the ceiling error in the number of prime factors. -/
theorem product_lt_cutoff_of_log_scale {p B s k : ℕ} {A c : ℝ} (hp : 0 < p) (hB : 0 < B)
    (hk : 0 < k) (hL : 1 < Real.log p) (hA : 0 < A) (hBL : (B : ℝ) ≤ (Real.log p) ^ A)
    (hs : (s : ℝ) ≤ c * Real.log p / Real.log (Real.log p) + 1)
    (hgap : c * A * Real.log p + A * Real.log (Real.log p) < (28 / 15 : ℝ) * Real.log p)
    (hcut : p ^ 28 ≤ k ^ 15) : B ^ s < k := by
  have hLp : 0 < Real.log p := zero_lt_one.trans hL
  have hll : 0 < Real.log (Real.log p) := Real.log_pos hL
  have hlogB := Real.log_le_log (Nat.cast_pos.mpr hB) hBL
  rw [Real.log_rpow hLp A] at hlogB
  have hm1 := mul_le_mul_of_nonneg_left hlogB (Nat.cast_nonneg s : (0 : ℝ) ≤ s)
  have hm2 := mul_le_mul_of_nonneg_right hs (mul_pos hA hll).le
  have hid :
    (c * Real.log p / Real.log (Real.log p) + 1) * (A * Real.log (Real.log p)) =
      c * A * Real.log p + A * Real.log (Real.log p) := by
    field_simp [hll.ne']
  rw [hid] at hm2
  have hcutR : (p : ℝ) ^ 28 ≤ (k : ℝ) ^ 15 := by exact_mod_cast hcut
  have hlcut := Real.log_le_log (pow_pos (Nat.cast_pos.mpr hp) 28) hcutR
  rw [Real.log_pow, Real.log_pow] at hlcut
  norm_num only [Nat.cast_ofNat] at hlcut
  have hlog : (s : ℝ) * Real.log B < Real.log k := by nlinarith only [hm1, hm2, hgap, hlcut]
  apply (Nat.cast_lt (α := ℝ)).mp
  rw [Nat.cast_pow]
  apply (Real.log_lt_log_iff (pow_pos (Nat.cast_pos.mpr hB) s) (Nat.cast_pos.mpr hk)).mp
  rw [Real.log_pow]
  exact hlog

/-- The cutoff upper bound k^15<=32768p^28 implies k<=2p^(28/15).
Take fifteenth powers in the nonnegative real numbers. -/
theorem cutoff_le_two_rpow {p k : ℕ} (hcut : k ^ 15 ≤ 32768 * p ^ 28) :
    (k : ℝ) ≤ 2 * (p : ℝ) ^ (28 / 15 : ℝ) := by
  have hp0 := Nat.cast_nonneg (α := ℝ) p
  have he : ((p : ℝ) ^ (28 / 15 : ℝ)) ^ 15 = (p : ℝ) ^ 28 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0]
    rw [show (28 / 15 : ℝ) * (15 : ℕ) = (28 : ℕ) by norm_num only, Real.rpow_natCast]
  apply
    (pow_le_pow_iff_left₀ (Nat.cast_nonneg k)
        (mul_nonneg (by norm_num only) (Real.rpow_nonneg hp0 _)) (by decide : 15 ≠ 0)).mp
  rw [mul_pow, he]
  norm_num only
  exact_mod_cast hcut

/-- Uniformly for every cutoff with k^15<=32768p^28, eventually 256k is at most
p times floor(p^(217/250)). Absorb the constant using the strict exponent gap
217/250>13/15 and an intermediate exponent 1301/1500. -/
theorem eventually_cutoff_le_prime_mul_floor_power :
    Filter.Eventually
      (fun p : ℕ ↦
        ∀ k : ℕ, k ^ 15 ≤ 32768 * p ^ 28 → 256 * k ≤ p * Nat.floor ((p : ℝ) ^ (217 / 250 : ℝ)))
      Filter.atTop := by
  have h₁ :=
    NumberTheory.eventually_const_mul_rpow_le_rpow (C := 512) (b := (13 / 15 : ℝ)) (A :=
      (1301 / 1500 : ℝ)) (by norm_num only)
  have h₂ :=
    NumberTheory.eventually_rpow_le_nat_floor_rpow (b := (1301 / 1500 : ℝ)) (A := (217 / 250 : ℝ))
      (by norm_num only) (by norm_num only)
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually h₁,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h₂, Filter.eventually_gt_atTop (0 : ℕ)] with p
    h₁p h₂p hp
  intro k hcut
  have hk := cutoff_le_two_rpow hcut
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hm := mul_le_mul_of_nonneg_left (h₁p.trans h₂p) hpR.le
  have he : (p : ℝ) * (p : ℝ) ^ (13 / 15 : ℝ) = (p : ℝ) ^ (28 / 15 : ℝ) := by
    calc
      _ = (p : ℝ) ^ (1 : ℝ) * (p : ℝ) ^ (13 / 15 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hpR]; congr 1; norm_num only
  have hm' :
    (512 : ℝ) * (p : ℝ) ^ (28 / 15 : ℝ) ≤
      (p : ℝ) * (Nat.floor ((p : ℝ) ^ (217 / 250 : ℝ)) : ℝ) := by
    calc
      _ = (p : ℝ) * (512 * (p : ℝ) ^ (13 / 15 : ℝ)) := by
        rw [← he]; ring
      _ ≤ _ := hm
  apply (Nat.cast_le (α := ℝ)).mp
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  nlinarith only [hk, hm']

end PseudoPrime.Analysis
