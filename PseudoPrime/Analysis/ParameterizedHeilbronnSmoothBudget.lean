/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.HeilbronnSmoothLogarithmicBudget

/-! # Variable exponents for the Heilbronn smooth-number comparison -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Any beta>13/15 absorbs the cutoff constant: eventually 256k<=p floor(p^beta)
for every k with k^15<=32768p^28. Choose an intermediate exponent and keep the floor error. -/
theorem eventually_cutoff_le_prime_mul_floor_power_of_exponent {beta : ℝ}
    (hbeta : (13 / 15 : ℝ) < beta) :
    Filter.Eventually
      (fun p : ℕ ↦ ∀ k : ℕ, k ^ 15 ≤ 32768 * p ^ 28 → 256 * k ≤ p * Nat.floor ((p : ℝ) ^ beta))
      Filter.atTop := by
  obtain ⟨d, hd, hdb⟩ := exists_between hbeta
  have hd0 : 0 ≤ d := (lt_trans (by norm_num only : (0 : ℝ) < 13 / 15) hd).le
  have h₁ :=
    NumberTheory.eventually_const_mul_rpow_le_rpow (C := 512) (b := (13 / 15 : ℝ)) (A := d) hd
  have h₂ := NumberTheory.eventually_rpow_le_nat_floor_rpow hd0 hdb
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
  have hm' : (512 : ℝ) * (p : ℝ) ^ (28 / 15 : ℝ) ≤ (p : ℝ) * (Nat.floor ((p : ℝ) ^ beta) : ℝ) := by
    calc
      _ = (p : ℝ) * (512 * (p : ℝ) ^ (13 / 15 : ℝ)) := by
        rw [← he]; ring
      _ ≤ _ := hm
  apply (Nat.cast_le (α := ℝ)).mp
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  nlinarith only [hk, hm']

/-- Every A>28/15 admits smooth-product parameters with simultaneous strict margins.
Rescale the small-subgroup parameter theorem and choose beta above 13/15. -/
theorem choose_heilbronn_smooth_parameters {A : ℝ} (hA : (28 / 15 : ℝ) < A) :
    ∃ b c beta : ℝ,
      1 < b ∧
        b < A ∧ 0 < c ∧ c * A < (28 / 15 : ℝ) ∧ (13 / 15 : ℝ) < beta ∧ beta < c * (b - 1) := by
  have hA' : 1 / (1 - (13 / 28 : ℝ)) < A := by
    norm_num only
    exact hA
  obtain ⟨b, c₀, hb, hbA, hc₀, hcA, hcb⟩ :=
    choose_subgroup_count_parameters (beta := (13 / 28 : ℝ)) (by norm_num only) (by norm_num only)
      hA'
  let c := (28 / 15 : ℝ) * c₀
  have hc : 0 < c := mul_pos (by norm_num only) hc₀
  have hsize : c * A < (28 / 15 : ℝ) := by
    have hm := mul_lt_mul_of_pos_left hcA (by norm_num only : (0 : ℝ) < 28 / 15)
    dsimp only [c]
    nlinarith only [hm]
  have hcount : (13 / 15 : ℝ) < c * (b - 1) := by
    have hm := mul_lt_mul_of_pos_left hcb (by norm_num only : (0 : ℝ) < 28 / 15)
    dsimp only [c]
    nlinarith only [hm]
  obtain ⟨beta, hlo, hhi⟩ := exists_between hcount
  exact ⟨b, c, beta, hb, hbA, hc, hsize, hlo, hhi⟩

end PseudoPrime.Analysis
