/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.QuadraticDecaySeries
public import Mathlib.Data.Nat.Log

/-! # Inverse quadratic weights from finite linear height counts -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For a real height, take the binary logarithm of one plus its absolute floor.
The resulting natural index selects a dyadic height bin, including height zero.
It is used to sum inverse quadratic weights from cumulative height counts. -/
noncomputable def quadraticHeightBin (t : ℝ) : ℕ :=
  Nat.log 2 (⌊|t|⌋₊ + 1)

/-- Every real height is below the dyadic upper endpoint of its selected bin.
Combine the strict floor bound and the successor binary-log bound. This places
all finite bin elements below a common integer counting endpoint. -/
theorem abs_lt_quadraticHeightBin_upper (t : ℝ) :
    |t| < ((2 ^ (quadraticHeightBin t + 1) : ℕ) : ℝ) := by
  have ht := Nat.lt_floor_add_one |t|
  have hn := Nat.lt_pow_succ_log_self (by norm_num only : 1 < 2) (⌊|t|⌋₊ + 1)
  have hnreal : (⌊|t|⌋₊ : ℝ) + 1 < ((2 ^ (quadraticHeightBin t + 1) : ℕ) : ℝ) := by
    exact_mod_cast hn
  exact lt_trans ht hnreal

/-- In each dyadic height bin, the inverse quadratic weight is at most four
times the inverse square of the bin scale. Treat bin zero directly and use the
floor lower bound for positive bins. This retains summable height decay. -/
theorem quadraticHeightBin_inverse_weight_le (t : ℝ) :
    1 / (1 + t ^ 2) ≤ 4 / ((2 : ℝ) ^ quadraticHeightBin t) ^ 2 := by
  have hp : 0 < (2 : ℝ) ^ quadraticHeightBin t := pow_pos (by norm_num only) _
  have hden : 0 < 1 + t ^ 2 := by nlinarith only [sq_nonneg t]
  by_cases hj : quadraticHeightBin t = 0
  · rw [hj, pow_zero, one_pow, div_one]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [sq_nonneg t]
  · have hjpos : 1 ≤ quadraticHeightBin t := Nat.one_le_iff_ne_zero.mpr hj
    have hp2 : (2 : ℝ) ≤ (2 : ℝ) ^ quadraticHeightBin t := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num only : 0 < 2) hjpos
    have hlow := Nat.pow_log_le_self 2 (Nat.succ_ne_zero ⌊|t|⌋₊)
    have hlowreal : (2 : ℝ) ^ quadraticHeightBin t ≤ (⌊|t|⌋₊ : ℝ) + 1 := by exact_mod_cast hlow
    have hf := Nat.floor_le (abs_nonneg t)
    have hbound : (2 : ℝ) ^ quadraticHeightBin t / 2 ≤ |t| := by linarith only [hlowreal, hf, hp2]
    have hs := (sq_le_sq₀ (div_nonneg hp.le (by norm_num only)) (abs_nonneg t)).mpr hbound
    rw [div_le_div_iff₀ hden (pow_pos hp 2)]
    nlinarith only [hs, sq_abs t]

/-- For finite nonnegative weights whose cumulative mass up to every integer
height at least two is at most `C` times height, their inverse quadratic weighted
sum is at most `16C`. Partition into dyadic bins and sum a geometric majorant.
This transforms a linear height count into a uniform summable zero-weight bound. -/
theorem sum_inverse_quadratic_of_linear_height_count {ι : Type*} (S : Finset ι) (γ w : ι → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hcount : ∀ n : ℕ, 2 ≤ n → ∑ i ∈ S.filter (fun i ↦ |γ i| ≤ n), w i ≤ C * n) :
    ∑ i ∈ S, w i / (1 + (γ i) ^ 2) ≤ 16 * C := by
  classical
  let J := S.image (fun i ↦ quadraticHeightBin (γ i))
  have hbin (j : ℕ) :
    ∑ i ∈ S.filter (fun i ↦ quadraticHeightBin (γ i) = j), w i / (1 + (γ i) ^ 2) ≤
      8 * C * (1 / 2 : ℝ) ^ j := by
    let B := S.filter (fun i ↦ quadraticHeightBin (γ i) = j)
    have hn : 2 ≤ 2 ^ (j + 1) := by
      exact Nat.pow_le_pow_right (by norm_num only : 0 < 2) (Nat.succ_le_succ (Nat.zero_le j))
    have hsub : B ⊆ S.filter (fun i ↦ |γ i| ≤ (2 ^ (j + 1) : ℕ)) := by
      intro i hi
      have hb := abs_lt_quadraticHeightBin_upper (γ i)
      rw [(Finset.mem_filter.mp hi).2] at hb
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, hb.le⟩
    have hc : ∑ i ∈ B, w i ≤ C * ((2 ^ (j + 1) : ℕ) : ℝ) :=
      (Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun i hi _ ↦ hw i (Finset.mem_filter.mp hi).1)).trans
        (hcount _ hn)
    have hp : 0 < (2 : ℝ) ^ j := pow_pos (by norm_num only) _
    calc
      _ ≤ ∑ i ∈ B, (4 / ((2 : ℝ) ^ j) ^ 2) * w i := by
        apply Finset.sum_le_sum
        intro i hi
        have hb := quadraticHeightBin_inverse_weight_le (γ i)
        rw [(Finset.mem_filter.mp hi).2] at hb
        have hm := mul_le_mul_of_nonneg_right hb (hw i (Finset.mem_filter.mp hi).1)
        convert hm using 1
        ring
      _ = (4 / ((2 : ℝ) ^ j) ^ 2) * ∑ i ∈ B, w i := by rw [Finset.mul_sum]
      _ ≤ (4 / ((2 : ℝ) ^ j) ^ 2) * (C * ((2 ^ (j + 1) : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hc (div_nonneg (by norm_num only) (sq_nonneg _))
      _ = _ := by
        rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ, one_div_pow]
        calc
          _ = (8 * C * (2 : ℝ) ^ j) / ((2 : ℝ) ^ j * (2 : ℝ) ^ j) := by ring
          _ = 8 * C / (2 : ℝ) ^ j := mul_div_mul_right _ _ hp.ne'
          _ = _ := by ring
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to (s := S) (t := J) (g := fun i ↦ quadraticHeightBin (γ i))
      (fun i hi ↦ Finset.mem_image_of_mem _ hi) (fun i ↦ w i / (1 + (γ i) ^ 2))
  have hg : HasSum (fun j : ℕ ↦ (1 / 2 : ℝ) ^ j) 2 := by
    convert
      hasSum_geometric_of_lt_one (by norm_num only : (0 : ℝ) ≤ 1 / 2)
        (by norm_num only : (1 / 2 : ℝ) < 1) using
      1
    norm_num only
  have hsum : ∑ j ∈ J, (1 / 2 : ℝ) ^ j ≤ 2 := by
    exact
      (hg.summable.sum_le_tsum J (fun j _ ↦ pow_nonneg (by norm_num only) j)).trans_eq hg.tsum_eq
  rw [← hfiber]
  calc
    _ ≤ ∑ j ∈ J, 8 * C * (1 / 2 : ℝ) ^ j := Finset.sum_le_sum (fun j _ ↦ hbin j)
    _ = 8 * C * ∑ j ∈ J, (1 / 2 : ℝ) ^ j := by rw [Finset.mul_sum]
    _ ≤ 8 * C * 2 := mul_le_mul_of_nonneg_left hsum (by linarith only [hC])
    _ = _ := by ring

end PseudoPrime.Analysis
