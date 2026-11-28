/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianRemainderBernstein
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceMoment
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # The large-cutoff remainder charge at the K186 entry -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The outside normalization and the large-cutoff weight cancel the kernel pole. -/
public theorem h27_finite_weight (a l : ℝ) :
    Real.exp (-(5 * a)) * (5 / 4 * Real.exp ((a - 1 / 2 - 2) * 5) * Real.exp (-(5 / 2 : ℝ) * l)) =
      5 / 4 * Real.exp (-(5 / 2 : ℝ) * (5 + l)) := by
  rw [← mul_assoc, mul_left_comm (Real.exp (-(5 * a))), mul_assoc (5 / 4 : ℝ), ← Real.exp_add, ←
    Real.exp_add]
  congr 2
  ring

/-- For log cutoff at least eleven, the entry budget contributes at most one ten-thousandth. -/
public theorem h27_finite_entry_le {l M : ℝ} (hl : 11 ≤ l) (hM : M ≤ 6000000000000) :
    5 / 4 * Real.exp (-(5 / 2 : ℝ) * (5 + l)) * M ≤ 1 / 10000 := by
  have he : Real.exp (-(5 / 2 : ℝ) * (5 + l)) ≤ Real.exp (-40) :=
    Real.exp_le_exp.mpr (by linarith only [hl])
  have hq : headExpUpper 40 72 ≤ (1 / 100000000000000000 : ℚ) := by decide +kernel
  have hc :=
    (head_exp_upper_sound (by norm_num only : (0 : ℚ) ≤ 40) 72).trans
      ((Rat.cast_le (K := ℝ)).mpr hq)
  have h : Real.exp (-(5 / 2 : ℝ) * (5 + l)) ≤ 1 / 100000000000000000 := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_neg] using he.trans hc
  calc
    _ ≤ 5 / 4 * Real.exp (-(5 / 2 : ℝ) * (5 + l)) * 6000000000000 :=
      mul_le_mul_of_nonneg_left hM (mul_nonneg (by norm_num only) (Real.exp_nonneg _))
    _ ≤ 5 / 4 * (1 / 100000000000000000) * 6000000000000 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (by norm_num only)) (by norm_num only)
    _ ≤ _ := by norm_num only

/-- Use a unit partition budget in the large-cutoff term, with the pole canceled. -/
private theorem h27_finite_unit_grid (K : HighGaussianKernel) (N m : ℕ) {s : ℚ} (hs : 0 < s)
    {l u : ℝ} (hu₀ : 0 ≤ 5 + u) (hu : 5 + u ≤ (N : ℝ)) {M : ℤ}
    (hM : highRemainderChargeTicks K N m 1 s (fun j ↦ (j : ℚ)) ≤ M) :
    let D := (highRemainderRatPoly K).map (Rat.castHom ℝ)
    Real.exp (-(5 * (K.pole : ℝ))) *
        ((5 / 4 * Real.exp (((K.pole : ℝ) - 1 / 2 - 2) * 5)) *
          (Real.exp (-(5 / 2 : ℝ) * l) *
            (∫ t in (0 : ℝ)..(5 + u), Real.exp (-(s : ℝ) * t) * |D.eval t|))) ≤
      5 / 4 * Real.exp (-(5 / 2 : ℝ) * (5 + l)) * (M : ℝ) := by
  intro D
  have hpart :=
    high_remainder_integral_le_ticks K N m 1 Nat.one_pos hs.le (fun j ↦ (j : ℚ))
      (fun j _ ↦ Nat.cast_lt.mpr (Nat.lt_succ_self j)) (fun j _ ↦ Nat.cast_nonneg j)
  have hC := (Int.cast_le (R := ℝ)).mpr hM
  have hfull : (∫ t in (0 : ℝ)..(N : ℝ), Real.exp (-(s : ℝ) * t) * |D.eval t|) ≤ (M : ℝ) := by
    have h := hpart.trans (show _ ≤ (M : ℝ) from by simpa only [Nat.cast_one, div_one] using hC)
    simpa only [D, Nat.cast_zero, Rat.cast_natCast, Rat.cast_zero] using h
  have hcut := abs_laplace_interval_mono D (Rat.cast_pos.mpr hs) hu₀ hu
  have hw := h27_finite_weight (K.pole : ℝ) l
  rw [← mul_assoc] at hw
  rw [← mul_assoc, ← mul_assoc, hw]
  exact
    mul_le_mul_of_nonneg_left (hcut.trans hfull) (mul_nonneg (by norm_num only) (Real.exp_nonneg _))

/-- A checked integer integral budget pays the large-cutoff H27 charge at the K186 entry. -/
public theorem h27_k186_finite_entry {l u : ℝ} (hl : 11 ≤ l) (hlu : l ≤ u) (hu : u ≤ 12)
    (hM : highRemainderChargeTicks .k186 17 72 1 (1 / 4) (fun j ↦ (j : ℚ)) ≤ 6000000000000) :
    let D := (highRemainderRatPoly .k186).map (Rat.castHom ℝ)
    Real.exp (-(5 * (HighGaussianKernel.k186.pole : ℝ))) *
        ((5 / 4 * Real.exp (((HighGaussianKernel.k186.pole : ℝ) - 1 / 2 - 2) * 5)) *
          (Real.exp (-(5 / 2 : ℝ) * l) *
            (∫ t in (0 : ℝ)..(5 + u), Real.exp (-(1 / 4 : ℝ) * t) * |D.eval t|))) ≤
      1 / 10000 := by
  have h :=
    h27_finite_unit_grid .k186 17 72 (by norm_num only : (0 : ℚ) < 1 / 4) (l := l)
      (by linarith only [hl, hlu] : 0 ≤ 5 + u) (by linarith only [hu] : 5 + u ≤ (17 : ℝ)) hM
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Int.cast_ofNat] at h
  exact h.trans (h27_finite_entry_le hl le_rfl)

/-- A checked integral budget pays the large-cutoff H27 charge at the K196 entry. -/
public theorem h27_k196_finite_entry {l u : ℝ} (hl : 75 / 2 ≤ l) (hlu : l ≤ u) (hu : u ≤ 38)
    (hM : highRemainderChargeTicks .k196 43 144 1 (3 / 4) (fun j ↦ (j : ℚ)) ≤ 4 * 10 ^ 38) :
    let D := (highRemainderRatPoly .k196).map (Rat.castHom ℝ)
    Real.exp (-(5 * (HighGaussianKernel.k196.pole : ℝ))) *
        ((5 / 4 * Real.exp (((HighGaussianKernel.k196.pole : ℝ) - 1 / 2 - 2) * 5)) *
          (Real.exp (-(5 / 2 : ℝ) * l) *
            (∫ t in (0 : ℝ)..(5 + u), Real.exp (-(3 / 4 : ℝ) * t) * |D.eval t|))) ≤
      1 / 1000000 := by
  have h :=
    h27_finite_unit_grid .k196 43 144 (by norm_num only : (0 : ℚ) < 3 / 4) (l := l)
      (by linarith only [hl, hlu] : 0 ≤ 5 + u) (by linarith only [hu] : 5 + u ≤ (43 : ℝ)) hM
  simp only [Rat.cast_div, Rat.cast_ofNat, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at h
  refine h.trans ?_
  have he : Real.exp (-(5 / 2 : ℝ) * (5 + l)) ≤ Real.exp (-(425 / 4 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith only [hl])
  have hq : headExpUpper (425 / 4) 180 ≤ (1 / 10 ^ 45 : ℚ) := by decide +kernel
  have hc :=
    (head_exp_upper_sound (by norm_num only : (0 : ℚ) ≤ 425 / 4) 180).trans
      ((Rat.cast_le (K := ℝ)).mpr hq)
  have hexp : Real.exp (-(5 / 2 : ℝ) * (5 + l)) ≤ 1 / 10 ^ 45 := by
    exact
      he.trans (by simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_pow] using hc)
  refine
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by norm_num only))
          (by norm_num only : (0 : ℝ) ≤ 4 * 10 ^ 38)).trans
      ?_
  norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
