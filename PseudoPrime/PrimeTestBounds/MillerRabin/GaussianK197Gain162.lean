/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Gain148
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowerGain663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowerSupport656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquareGain570

/-! # Retained prime powers for compressed cell 162 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The six squares in the top K197 support. -/
@[expose]
def lateSquares : Finset ℕ :=
  {1352569, 1371241, 1394761, 1408969, 1423249, 1442401}

/-- The six retained squares and one cube above the cutoff in cell 162. -/
@[expose]
def retainedPowers162 : Finset ℕ :=
  insert (113 ^ 3) lateSquares

private theorem late_square_data {n : ℕ} (hn : n ∈ lateSquares) :
    ∃ p : ℕ, 1163 ≤ p ∧ p ≤ 1207 ∧ p.Prime ∧ n = p ^ 2 := by
  have h : ∀ n ∈ lateSquares, 1163 ≤ n.sqrt ∧ n.sqrt ≤ 1207 ∧ n.sqrt.Prime ∧ n = n.sqrt ^ 2 := by
    decide +kernel
  exact ⟨n.sqrt, h _ hn⟩

/-- The selected powers lie in the support already certified for K197. -/
theorem retainedPowers162_subset : retainedPowers162 ⊆ fixedPowers663.erase (337 ^ 2) := by
  intro n hn
  rcases Finset.mem_insert.mp hn with rfl | hn
  · apply Finset.mem_erase.mpr
    refine ⟨by decide, Finset.mem_erase.mpr ⟨by decide, ?_⟩⟩
    exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
  obtain ⟨p, hpl, hpu, hprime, rfl⟩ := late_square_data hn
  have hnot (j : ℕ) (hj : j < 1163) : p ^ 2 ≠ j ^ 2 :=
    ne_of_gt (pow_lt_pow_left₀ (hj.trans_le hpl) (Nat.zero_le j) (by decide : 2 ≠ 0))
  apply Finset.mem_erase.mpr
  refine ⟨hnot 337 (by decide), Finset.mem_erase.mpr ⟨hnot 331 (by decide), ?_⟩⟩
  apply Finset.mem_union_left
  exact
    Finset.mem_image.mpr
      ⟨p,
        Finset.mem_filter.mpr
          ⟨Finset.mem_Ioc.mpr ⟨(by decide : 328 < 1163).trans_le hpl, hpu⟩, hprime.isPrimePow⟩,
        rfl⟩

/-- Every selected power exceeds the squared radius for all radii from 1157 to 1162.1. -/
theorem retainedPowers162_above {r : ℝ} (hr : r ∈ Set.Icc 1157 1162.1) {n : ℕ}
    (hn : n ∈ retainedPowers162) : r ^ 2 < (n : ℝ) := by
  have h : ∀ n ∈ retainedPowers162, 1352569 ≤ n := by decide +kernel
  exact
    ((pow_le_pow_left₀ ((by norm_num only : (0 : ℝ) ≤ 1157).trans hr.1) hr.2 2).trans_lt
          (by norm_num only : (1162.1 : ℝ) ^ 2 < 1352569)).trans_le
      (by exact_mod_cast h n hn)

private theorem late_shape_floor {v : ℝ} (hv : v ∈ Set.Icc 2.805 5) :
    (2.805 : ℝ) ^ 5 * 0.0604 ≤ v ^ 5 * Real.exp (-v) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 10000 / 604) (j := 4) (n := 27) (lo := 2.806)
        (hi := 2.9) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at h
  have he : (0.0604 : ℝ) ≤ Real.exp (-2.805) := by
    apply (Real.log_le_iff_le_exp (by norm_num only)).mp
    have hi : (2.806 : ℝ) ≤ Real.log (0.0604 : ℝ)⁻¹ := by
      norm_num only at h ⊢; exact h
    rw [Real.log_inv] at hi
    linarith only [hi]
  exact
    (mul_le_mul_of_nonneg_left he (by norm_num only)).trans
      (fifth_increasing ⟨by norm_num only, by norm_num only⟩
        ⟨(by norm_num only : (0 : ℝ) ≤ 2.805).trans hv.1, hv.2⟩ hv.1)

private theorem late_weight_floor {r : ℝ} (hr : r ∈ Set.Icc 1157 1162.1) {n : ℕ}
    (hn : n ∈ retainedPowers162) :
    (1 / 1202 : ℝ) * (2.805 ^ 5 * 0.0604 / 120) ≤ quarterWeight656 (r ^ 2) n := by
  have hcut := retainedPowers162_above hr hn
  have hr₀ := (by norm_num only : (0 : ℝ) < 1157).trans_le hr.1
  have hn₀ := (sq_nonneg r).trans_lt hcut
  have hN : ∀ n ∈ retainedPowers162, n ≤ 1442897 := by decide +kernel
  have hu : (n : ℝ) ≤ 1442897 := by exact_mod_cast hN n hn
  have hd : (n : ℝ) / r ^ 2 ≤ 1442897 / 1157 ^ 2 :=
    (div_le_div_of_nonneg_left hn₀.le (by norm_num only)
          (pow_le_pow_left₀ (by norm_num only) hr.1 2)).trans
      (div_le_div_of_nonneg_right hu (by norm_num only))
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1442897 / 1157 ^ 2) (j := 0) (n := 27) (lo :=
        0.07) (hi := 0.075) (by decide +kernel)).2
  norm_num only [Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at h
  have hL :=
    (Real.log_le_log (div_pos hn₀ (sq_pos_of_pos hr₀)) hd).trans
      (by
        norm_num only at h ⊢; exact h)
  have hN₀ := Real.log_nonneg ((one_le_div (sq_pos_of_pos hr₀)).mpr hcut.le)
  have hv :=
    late_shape_floor (v := (11 / 10) * (21 / 8 - Real.log ((n : ℝ) / r ^ 2)))
      ⟨by linarith only [hL], by linarith only [hN₀]⟩
  have hs : Real.sqrt (n : ℝ) ≤ 1202 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num only, hu.trans (by norm_num only)⟩
  change _ ≤ (1 / Real.sqrt (n : ℝ)) * _
  exact
    mul_le_mul (one_div_le_one_div_of_le (Real.sqrt_pos.2 hn₀) hs)
      (div_le_div_of_nonneg_right hv (by norm_num only : (0 : ℝ) ≤ 120)) (by norm_num only)
      (one_div_nonneg.mpr (Real.sqrt_nonneg _))

private theorem late_atom_gain {r : ℝ} (hr : r ∈ Set.Icc 1157 1162.1) {p k : ℕ} (hp : p.Prime)
    (hk : k ≠ 0) (hm : p ^ k ∈ retainedPowers162) {J A : ℝ} (hJ : J ≤ Real.log p) (hJ₀ : 0 ≤ J)
    (hA : A ≤ 4 * (J * ((1 / 1202) * (2.805 ^ 5 * 0.0604 / 120)))) :
    A ≤ 4 * (ArithmeticFunction.vonMangoldt (p ^ k) * quarterWeight656 (r ^ 2) (p ^ k : ℕ)) := by
  have hw := late_weight_floor hr hm
  rw [ArithmeticFunction.vonMangoldt_apply_pow hk, ArithmeticFunction.vonMangoldt_apply_prime hp]
  exact
    hA.trans
      (mul_le_mul_of_nonneg_left (mul_le_mul hJ hw (by norm_num only) (hJ₀.trans hJ))
        (by norm_num only))

private theorem late_square_gain {r : ℝ} (hr : r ∈ Set.Icc 1157 1162.1) {n : ℕ}
    (hn : n ∈ lateSquares) :
    (0.00204 : ℝ) ≤ 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n) := by
  obtain ⟨p, hl, _, hp, rfl⟩ := late_square_data hn
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1163) (j := 10) (n := 27) (lo := 7.05) (hi :=
        7.1) (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at h
  have hpl : (1163 : ℝ) ≤ p := by exact_mod_cast hl
  apply late_atom_gain hr hp (by decide) (Finset.mem_insert_of_mem hn) (J := 7.05)
  · linarith only [h, Real.log_le_log (by norm_num only : (0 : ℝ) < 1163) hpl]
  · norm_num only
  · norm_num only

private theorem late_cube_gain {r : ℝ} (hr : r ∈ Set.Icc 1157 1162.1) :
    (0.00136 : ℝ) ≤
      4 * (ArithmeticFunction.vonMangoldt (113 ^ 3) * quarterWeight656 (r ^ 2) (113 ^ 3 : ℕ)) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 113) (j := 7) (n := 27) (lo := 4.72) (hi := 4.75)
        (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at h
  apply late_atom_gain hr (by decide) (by decide) (Finset.mem_insert_self _ _) (J := 4.72)
  · linarith only [h]
  · norm_num only
  · norm_num only

/-- The fixed powers contribute at least 0.0136 throughout compressed cell 162. -/
theorem retained_powers_gain162 {r : ℝ} (hr : r ∈ Set.Icc 1157 1162.1) :
    (0.0136 : ℝ) ≤
      ∑ n ∈ retainedPowers162,
        4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n) := by
  have h := Finset.sum_le_sum (fun n hn ↦ late_square_gain hr (n := n) hn)
  have hc : lateSquares.card = 6 := by decide +kernel
  rw [Finset.sum_const, hc, nsmul_eq_mul] at h
  rw [retainedPowers162, Finset.sum_insert (by decide : 113 ^ 3 ∉ lateSquares)]
  linarith only [h, late_cube_gain hr]

end PseudoPrime.PrimeTestBounds.MillerRabin
