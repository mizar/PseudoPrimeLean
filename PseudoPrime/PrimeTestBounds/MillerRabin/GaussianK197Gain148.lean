/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197PowerBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowerGain663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowerGain663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowerSupport656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquareGain570

/-! # Shared prime-square contribution for compressed cells 147 and 148 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The 22 retained prime squares above both cells and below the fixed support cap. -/
@[expose]
def retainedSquares148 : Finset ℕ :=
  {1100401, 1104601, 1125721, 1129969, 1142761, 1181569, 1190281,
   1194649, 1203409, 1216609, 1229881, 1247689, 1261129, 1274641,
   1324801, 1329409, 1352569, 1371241, 1394761, 1408969, 1423249,
   1442401}

private theorem square148_mem {n : ℕ} (hn : n ∈ retainedSquares148) :
    ∃ p : ℕ, p ∈ Finset.Icc 1049 1207 ∧ p.Prime ∧ n = p ^ 2 := by
  have h :
    ∀ n ∈ retainedSquares148, n.sqrt ∈ Finset.Icc 1049 1207 ∧ n.sqrt.Prime ∧ n = n.sqrt ^ 2 := by
    decide +kernel
  exact ⟨n.sqrt, h _ hn⟩

/-- All selected squares belong to the retained support of the K197 comparison. -/
theorem retainedSquares148_subset : retainedSquares148 ⊆ fixedPowers663.erase (337 ^ 2) := by
  intro n hn
  obtain ⟨p, hp, hprime, rfl⟩ := square148_mem hn
  have hb := Finset.mem_Icc.mp hp
  have hnot (j : ℕ) (hj : j < 1049) : p ^ 2 ≠ j ^ 2 :=
    ne_of_gt (pow_lt_pow_left₀ (hj.trans_le hb.1) (Nat.zero_le j) (by decide : 2 ≠ 0))
  apply Finset.mem_erase.mpr
  refine ⟨hnot 337 (by decide), Finset.mem_erase.mpr ⟨hnot 331 (by decide), ?_⟩⟩
  apply Finset.mem_union_left
  exact
    Finset.mem_image.mpr
      ⟨p,
        Finset.mem_filter.mpr
          ⟨Finset.mem_Ioc.mpr ⟨(by decide : 328 < 1049).trans_le hb.1, hb.2⟩, hprime.isPrimePow⟩,
        rfl⟩

/-- Below radius 1046 each selected square is strictly beyond the squared cutoff. -/
theorem retainedSquares148_above {r : ℝ} (hr : r ∈ Set.Icc 1028 1046) {n : ℕ}
    (hn : n ∈ retainedSquares148) : r ^ 2 < (n : ℝ) := by
  obtain ⟨p, hp, _, rfl⟩ := square148_mem hn
  have hlo : (1049 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_Icc.mp hp).1
  rw [Nat.cast_pow]
  exact
    pow_lt_pow_left₀ (hr.2.trans_lt ((by norm_num only : (1046 : ℝ) < 1049).trans_le hlo))
      ((by norm_num only : (0 : ℝ) ≤ 1028).trans hr.1) (by decide : 2 ≠ 0)

private theorem lower_log_square_ratio {r p : ℝ} (hr : 1028 ≤ r) (hp : 0 < p) (hpu : p ≤ 1207) :
    Real.log (p ^ 2 / r ^ 2) ≤ 0.32106 := by
  have hr₀ := (by norm_num only : (0 : ℝ) < 1028).trans_le hr
  have hd : p ^ 2 / r ^ 2 ≤ (1207 : ℝ) ^ 2 / 1028 ^ 2 :=
    (div_le_div_of_nonneg_left (sq_nonneg p) (by norm_num only)
          (pow_le_pow_left₀ (by norm_num only) hr 2)).trans
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ hp.le hpu 2) (by norm_num only))
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := (1207 : ℚ) ^ 2 / 1028 ^ 2) (j := 0) (n := 27)
        (lo := 0.3) (hi := 0.32106) (by decide +kernel)).2
  norm_num only [Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at h
  exact
    (Real.log_le_log (div_pos (sq_pos_of_pos hp) (sq_pos_of_pos hr₀)) hd).trans
      (by
        norm_num only at h ⊢; exact h)

private theorem retained_shape_floor {v : ℝ} (hv : v ∈ Set.Icc 2.534 5) :
    (2.534 : ℝ) ^ 5 * 0.0793 ≤ v ^ 5 * Real.exp (-v) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 10000 / 793) (j := 4) (n := 27) (lo := 2.5341)
        (hi := 2.6) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at h
  have he : (0.0793 : ℝ) ≤ Real.exp (-2.534) := by
    apply (Real.log_le_iff_le_exp (by norm_num only)).mp
    have hi : (2.5341 : ℝ) ≤ Real.log (0.0793 : ℝ)⁻¹ := by
      norm_num only at h ⊢; exact h
    rw [Real.log_inv] at hi
    linarith only [hi]
  exact
    (mul_le_mul_of_nonneg_left he (by norm_num only)).trans
      (fifth_increasing ⟨by norm_num only, by norm_num only⟩
        ⟨(by norm_num only : (0 : ℝ) ≤ 2.534).trans hv.1, hv.2⟩ hv.1)

private theorem retained_square_atom {r : ℝ} (hr : r ∈ Set.Icc 1028 1046) {n : ℕ}
    (hn : n ∈ retainedSquares148) :
    (0.00157 : ℝ) ≤ 4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n) := by
  have hcut := retainedSquares148_above hr hn
  obtain ⟨p, hp, hprime, rfl⟩ := square148_mem hn
  have hb := Finset.mem_Icc.mp hp
  have hp₀ : (0 : ℝ) < p := Nat.cast_pos.mpr hprime.pos
  have hpU : (p : ℝ) ≤ 1207 := by exact_mod_cast hb.2
  have h₁ : (1049 : ℝ) ≤ p := by exact_mod_cast hb.1
  have hL := lower_log_square_ratio hr.1 hp₀ hpU
  have hN : 0 ≤ Real.log ((p : ℝ) ^ 2 / r ^ 2) := by
    rw [Nat.cast_pow] at hcut
    exact
      Real.log_nonneg
        ((one_le_div (sq_pos_of_pos ((by norm_num only : (0 : ℝ) < 1028).trans_le hr.1))).mpr
          hcut.le)
  have hshape :=
    retained_shape_floor (v := (11 / 10) * (21 / 8 - Real.log ((p : ℝ) ^ 2 / r ^ 2)))
      ⟨by linarith only [hL], by linarith only [hN]⟩
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1049) (j := 10) (n := 27) (lo := 6.9) (hi := 7)
        (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hlp : (6.9 : ℝ) ≤ Real.log p := by
    linarith only [hl, Real.log_le_log (by norm_num only : (0 : ℝ) < 1049) h₁]
  have hi : (1 / 1207 : ℝ) ≤ 1 / p := one_div_le_one_div_of_le hp₀ hpU
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by decide : 2 ≠ 0),
    ArithmeticFunction.vonMangoldt_apply_prime hprime, quarterWeight656, Nat.cast_pow,
    Real.sqrt_sq hp₀.le]
  dsimp only
  have hh :=
    mul_le_mul hi (div_le_div_of_nonneg_right hshape (by norm_num only : (0 : ℝ) ≤ 120))
      (by norm_num only) (one_div_nonneg.mpr hp₀.le)
  have hm :=
    mul_le_mul hlp hh (by norm_num only) ((by norm_num only : (0 : ℝ) ≤ (6.9 : ℝ)).trans hlp)
  linarith only [hm]

/-- Between radii 1028 and 1046 the selected squares contribute at least 0.03454. -/
theorem retained_squares_gain148 {r : ℝ} (hr : r ∈ Set.Icc 1028 1046) :
    (0.03454 : ℝ) ≤
      ∑ n ∈ retainedSquares148,
        4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n) := by
  have h := Finset.sum_le_sum (fun n hn ↦ retained_square_atom hr (n := n) hn)
  have hcard : retainedSquares148.card = 22 := by decide +kernel
  rw [Finset.sum_const, hcard, nsmul_eq_mul] at h
  norm_num only at h ⊢
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
