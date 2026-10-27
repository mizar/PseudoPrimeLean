/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ParameterizedHeilbronnSmoothBudget

/-! # Smooth-product margins for arbitrary rational Heilbronn cutoff scales -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For 1<kappa<A, select smooth-product parameters whose product height is
below p^kappa and whose count exceeds p^(kappa-1). Rescale the established
small-subgroup parameter theorem. This separates the cutoff from its old value 28/15. -/
theorem choose_smooth_parameters_of_cutoff {κ A : ℝ} (hκ : 1 < κ) (hA : κ < A) :
    ∃ b c beta : ℝ, 1 < b ∧ b < A ∧ 0 < c ∧ c * A < κ ∧ κ - 1 < beta ∧ beta < c * (b - 1) := by
  have hκp : 0 < κ := zero_lt_one.trans hκ
  have hb0 : 0 < (κ - 1) / κ := div_pos (sub_pos.mpr hκ) hκp
  have hb1 : (κ - 1) / κ < 1 := (div_lt_one hκp).mpr (by linarith only)
  have he : 1 / (1 - (κ - 1) / κ) = κ := by
    apply (div_eq_iff (sub_pos.mpr hb1).ne').mpr
    have hm := div_mul_cancel₀ (κ - 1) hκp.ne'
    nlinarith only [hm]
  obtain ⟨b, c₀, hb, hbA, hc₀, hcA, hcb⟩ :=
    choose_subgroup_count_parameters hb0 hb1
      (by
        rw [he]; exact hA)
  have hc : 0 < κ * c₀ := mul_pos hκp hc₀
  have hsize : κ * c₀ * A < κ := by
    have hm := mul_lt_mul_of_pos_left hcA hκp
    nlinarith only [hm]
  have hcount : κ - 1 < κ * c₀ * (b - 1) := by
    have hm := mul_lt_mul_of_pos_left hcb hκp
    rw [mul_div_cancel₀ _ hκp.ne'] at hm
    nlinarith only [hm]
  obtain ⟨beta, hlo, hhi⟩ := exists_between hcount
  exact ⟨b, κ * c₀, beta, hb, hbA, hc, hsize, hlo, hhi⟩

/-- For positive natural a, a cutoff k^a<=2^a*p^b is at most 2p^(b/a).
Take a-th powers in the nonnegative reals and cancel the denominator in
the real exponent. This avoids a fixed cutoff denominator. -/
theorem rational_cutoff_le_two_rpow {p k a b : ℕ} (ha : 0 < a) (hcut : k ^ a ≤ 2 ^ a * p ^ b) :
    (k : ℝ) ≤ 2 * (p : ℝ) ^ ((b : ℝ) / a) := by
  have hp0 := Nat.cast_nonneg (α := ℝ) p
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have he : ((p : ℝ) ^ ((b : ℝ) / a)) ^ a = (p : ℝ) ^ b := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0, div_mul_cancel₀ _ haR.ne', Real.rpow_natCast]
  apply
    (pow_le_pow_iff_left₀ (Nat.cast_nonneg k)
        (mul_nonneg (by norm_num only) (Real.rpow_nonneg hp0 _)) (ne_of_gt ha)).mp
  rw [mul_pow, he]
  exact_mod_cast hcut

/-- For a positive and 1<b/a<beta+1, the fixed cutoff constant is eventually
absorbed in p floor(p^beta), uniformly over all rational cutoffs. Retain the
floor error through an intermediate real exponent. This is the count budget. -/
theorem eventually_rational_cutoff_le_prime_mul_floor_power {a b : ℕ} {beta : ℝ} (ha : 0 < a)
    (hκ : 1 < (b : ℝ) / a) (hbeta : (b : ℝ) / a - 1 < beta) :
    Filter.Eventually
      (fun p : ℕ ↦ ∀ k : ℕ, k ^ a ≤ 2 ^ a * p ^ b → 256 * k ≤ p * Nat.floor ((p : ℝ) ^ beta))
      Filter.atTop := by
  obtain ⟨d, hd, hdb⟩ := exists_between hbeta
  have hd0 : 0 ≤ d := (lt_trans (sub_pos.mpr hκ) hd).le
  have h₁ :=
    NumberTheory.eventually_const_mul_rpow_le_rpow (C := 512) (b := (b : ℝ) / a - 1) (A := d) hd
  have h₂ := NumberTheory.eventually_rpow_le_nat_floor_rpow hd0 hdb
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually h₁,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h₂, Filter.eventually_gt_atTop (0 : ℕ)] with p
    h₁p h₂p hp
  intro k hcut
  have hk := rational_cutoff_le_two_rpow ha hcut
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hm := mul_le_mul_of_nonneg_left (h₁p.trans h₂p) hpR.le
  have he : (p : ℝ) * (p : ℝ) ^ ((b : ℝ) / a - 1) = (p : ℝ) ^ ((b : ℝ) / a) := by
    calc
      _ = (p : ℝ) ^ (1 : ℝ) * (p : ℝ) ^ ((b : ℝ) / a - 1) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hpR]; congr 1; ring
  have hm' : (512 : ℝ) * (p : ℝ) ^ ((b : ℝ) / a) ≤ (p : ℝ) * (Nat.floor ((p : ℝ) ^ beta) : ℝ) := by
    calc
      _ = (p : ℝ) * (512 * (p : ℝ) ^ ((b : ℝ) / a - 1)) := by
        rw [← he]; ring
      _ ≤ _ := hm
  apply (Nat.cast_le (α := ℝ)).mp
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  nlinarith only [hk, hm']

/-- A smooth product whose logarithm is below (b/a)log p lies below every
cutoff satisfying p^b<=k^a, for a positive. Preserve the ceiling error in its
factor count and compare logarithms. This is the height budget for rational scales. -/
theorem product_lt_rational_cutoff_of_log_scale {p B s k a b : ℕ} {A c : ℝ} (ha : 0 < a)
    (hp : 0 < p) (hB : 0 < B) (hk : 0 < k) (hL : 1 < Real.log p) (hA : 0 < A)
    (hBL : (B : ℝ) ≤ (Real.log p) ^ A) (hs : (s : ℝ) ≤ c * Real.log p / Real.log (Real.log p) + 1)
    (hgap : c * A * Real.log p + A * Real.log (Real.log p) < ((b : ℝ) / a) * Real.log p)
    (hcut : p ^ b ≤ k ^ a) : B ^ s < k := by
  have hLp : 0 < Real.log p := zero_lt_one.trans hL
  have hll : 0 < Real.log (Real.log p) := Real.log_pos hL
  have hlogB := Real.log_le_log (Nat.cast_pos.mpr hB) hBL
  rw [Real.log_rpow hLp A] at hlogB
  have hm1 := mul_le_mul_of_nonneg_left hlogB (Nat.cast_nonneg s : (0 : ℝ) ≤ s)
  have hm2 := mul_le_mul_of_nonneg_right hs (mul_pos hA hll).le
  have hid :
    (c * Real.log p / Real.log (Real.log p) + 1) * (A * Real.log (Real.log p)) =
      c * A * Real.log p + A * Real.log (Real.log p) := by
    have hc := div_mul_cancel₀ (c * Real.log p) hll.ne'
    have hm := congrArg (fun x : ℝ ↦ A * x) hc
    nlinarith only [hm]
  rw [hid] at hm2
  have hcutR : (p : ℝ) ^ b ≤ (k : ℝ) ^ a := by exact_mod_cast hcut
  have hlcut := Real.log_le_log (pow_pos (Nat.cast_pos.mpr hp) b) hcutR
  rw [Real.log_pow, Real.log_pow] at hlcut
  have hlo : ((b : ℝ) / a) * Real.log p ≤ Real.log k := by
    have h : (b : ℝ) * Real.log p / a ≤ Real.log k :=
      (div_le_iff₀ (Nat.cast_pos.mpr ha : (0 : ℝ) < a)).mpr (by simpa only [mul_comm] using hlcut)
    convert h using 1
    ring
  have hlog : (s : ℝ) * Real.log B < Real.log k := by nlinarith only [hm1, hm2, hgap, hlo]
  apply (Nat.cast_lt (α := ℝ)).mp
  rw [Nat.cast_pow]
  apply (Real.log_lt_log_iff (pow_pos (Nat.cast_pos.mpr hB) s) (Nat.cast_pos.mpr hk)).mp
  rw [Real.log_pow]
  exact hlog

end PseudoPrime.Analysis
