/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Moments
import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1423toMillion
import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3

/-! # Endpoint checks for the K197 reflection allowance -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private def pRat (d : ℚ) : ℕ → ℚ
  | 0 => 1 / d
  | k + 1 => (k + 1) / d * pRat d k

private theorem cast_pRat (d : ℚ) (k : ℕ) :
    (pRat d k : ℝ) = Analysis.logPowerTailPoly (d : ℝ) k 0 := by
  induction k with
  | zero => simp only [pRat, Analysis.logPowerTailPoly, Rat.cast_div, Rat.cast_one]
  | succ k ih =>
    simp only [pRat, Analysis.logPowerTailPoly, Rat.cast_add, Rat.cast_div, Rat.cast_mul,
      Rat.cast_natCast, Rat.cast_one, ih, Nat.cast_succ, zero_pow (Nat.succ_ne_zero _), zero_div,
      zero_add]

private def momentRat (A B L D : ℚ) (j : Fin 6) : ℚ :=
  let P := pRat (11 / 10)
  let H := fun k ↦ B * (P (k + 2) + 2 * L * P (k + 1) + L ^ 2 * P k)
  A * pRat (3 / 5) j + (if j = 0 then D else 0) + ((j.val : ℚ) * H (j.val - 1) + (8 / 5) * H j) / 24

private theorem cast_momentRat (A B L D : ℚ) (j : Fin 6) :
    (momentRat A B L D j : ℝ) = gaussianMomentBox197 (A : ℝ) (B : ℝ) (L : ℝ) (D : ℝ) j := by
  simp only [momentRat, gaussianMomentBox197, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
    Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast, cast_pRat]
  by_cases hj : j = 0
  · simp only [ite_eq_left hj]
  · simp only [ite_eq_right hj, Rat.cast_zero]

private def earlySum (u L : ℚ) : ℚ :=
  ∑ j : Fin 6, max 0 (jointShiftUpper197 11.722 u j) * momentRat 0.000943 0.00000284 L 0.000002272 j

private theorem cast_earlySum (u L : ℚ) :
    (earlySum u L : ℝ) =
      ∑ j : Fin 6,
        (↑(max 0 (jointShiftUpper197 11.722 u j)) : ℝ) *
          gaussianMomentBox197 0.000943 0.00000284 (L : ℝ) 0.000002272 j := by
  simp only [earlySum, Rat.cast_sum, Rat.cast_mul, cast_momentRat, Rat.cast_ofScientific]

private theorem joint_lower_box (hRH : RiemannHypothesis) {r : ℝ} {u L E : ℚ}
    (hr : r ∈ Set.Icc 332.15 1000) (hlu : Real.log r ≤ (L : ℝ) / 2)
    (hu : (2 * (L : ℝ) - 23 / 2) ≤ (u : ℝ))
    (hcert : 0 ≤ earlySum u L ∧ (4 * ((11 / 10 : ℚ) ^ 5 / 120 * 0.00000284)) * earlySum u L ≤ E)
    (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4)
    (hprefix : ∀ n : ℕ, (n : ℝ) ≤ r ^ 2 → ArithmeticFunction.vonMangoldt n ≠ 0 → α n = 0) :
    -(E : ℝ) ≤
      ∑ i, (gaussianCoeff197 i : ℝ) * quarterAuxReflection656 α r (quarterShift663 i : ℝ) := by
  have hr₁ : 1 ≤ r := (by norm_num only : (1 : ℝ) ≤ 332.15).trans hr.1
  have hx₀ := sq_pos_of_pos (zero_lt_one.trans_le hr₁)
  have hx := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 332.15) hr.1 2
  have hsqU := pow_le_pow_left₀ (zero_le_one.trans hr₁) hr.2 2
  have hx₁ : 1423 ≤ r ^ 2 := (by norm_num only : (1423 : ℝ) ≤ 332.15 ^ 2).trans hx
  have hx₂ : r ^ 2 ≤ 1000000 := hsqU.trans (by norm_num only)
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 6643 / 20) (j := 9) (n := 27) (lo := 5.80555)
        (hi := 6) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hlo
  have hrl : (6643 / 20 : ℝ) ≤ r := by linarith only [hr.1]
  have hll := hlo.trans (Real.log_le_log (by norm_num only : (0 : ℝ) < 6643 / 20) hrl)
  have hlog : 4 * Real.log r - 23 / 2 ∈ Set.Icc (↑(11.722 : ℚ) : ℝ) (↑u : ℝ) := by
    norm_num only [Rat.cast_ofScientific, Set.mem_Icc]
    exact ⟨by linarith only [hll], by linarith only [hlu, hu]⟩
  have hL : 5 ≤ Real.log (r ^ 2) ∧ Real.log (r ^ 2) ≤ (L : ℝ) := by
    rw [Real.log_pow, Nat.cast_ofNat]
    exact ⟨by linarith only [hll], by linarith only [hlu]⟩
  have hbaseA :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (6643 / 20) ^ 2) (p :=
        3) (d := 5) (lo := 0) (hi := 0.000943) (by decide +kernel)).2
  have hbaseB :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (6643 / 20) ^ 2) (p :=
        11) (d := 10) (lo := 0) (hi := 0.00000284) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Rat.cast_pow] at hbaseA hbaseB
  have hA : (r ^ 2) ^ (-(3 / 5) : ℝ) ≤ 0.000943 :=
    (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 332.15 ^ 2) hx
          (by norm_num only : (-(3 / 5) : ℝ) ≤ 0)).trans
      (by
        norm_num only; exact hbaseA)
  have hB : (r ^ 2) ^ (-(11 / 10) : ℝ) ≤ 0.00000284 :=
    (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 332.15 ^ 2) hx
          (by norm_num only : (-(11 / 10) : ℝ) ≤ 0)).trans
      (by
        norm_num only; exact hbaseB)
  have hD : -(Chebyshev.psi (r ^ 2) - r ^ 2) * (r ^ 2) ^ (-(8 / 5) : ℝ) ≤ 0.000002272 := by
    have h :=
      mul_le_mul_of_nonneg_right
        ((neg_le_abs _).trans
          (AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million hx₁ hx₂))
        (Real.rpow_nonneg hx₀.le (-(8 / 5) : ℝ))
    have he : Real.sqrt (r ^ 2) * (r ^ 2) ^ (-(8 / 5) : ℝ) = (r ^ 2) ^ (-(11 / 10) : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx₀]
      norm_num only
    linarith only [h, he, hB]
  have hh := (Rat.cast_nonneg (K := ℝ)).mpr hcert.1
  rw [cast_earlySum] at hh
  have hj :=
    gaussian_joint_endpoint_197 hRH hr₁ hx₁ hL.1 (by norm_num only) hlog hA hB hL.2 hD hh α hα
      hprefix
  have hb := (Rat.cast_le (K := ℝ)).mpr hcert.2
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
    Rat.cast_ofScientific] at hb
  rw [cast_earlySum] at hb
  linarith only [hj, hb]

/-- The combined K197 reflection costs at most 0.00005 on the first
physical radius interval. The common endpoint theorem uses a square-root
Chebyshev bound at degree zero and the exact rational dot product. -/
theorem gaussian_joint_early_lower_197 (hRH : RiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc 332.15 336.9) (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4)
    (hprefix : ∀ n : ℕ, (n : ℝ) ≤ r ^ 2 → ArithmeticFunction.vonMangoldt n ≠ 0 → α n = 0) :
    (-0.00005 : ℝ) ≤
      ∑ i, (gaussianCoeff197 i : ℝ) * quarterAuxReflection656 α r (quarterShift663 i : ℝ) := by
  have hhi :=
    (Analysis.rationalLogIntervalCheck_sound (N := 336.9) (j := 9) (n := 27) (lo := 5) (hi := 5.82)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofScientific] at hhi
  have hrU : r ≤ (3369 / 10 : ℝ) := by linarith only [hr.2]
  have hl := (Real.log_le_log ((by norm_num only : (0 : ℝ) < 332.15).trans_le hr.1) hrU).trans hhi
  have h :=
    joint_lower_box hRH (u := 11.78) (L := 11.64) (E := 0.00005)
      ⟨hr.1, hr.2.trans (by norm_num only)⟩
      (by
        norm_num only [Rat.cast_ofScientific]; linarith only [hl])
      (by norm_num only [Rat.cast_ofScientific]) (by decide +kernel) α hα hprefix
  norm_num only [Rat.cast_ofScientific] at h ⊢
  exact h

/-- The combined K197 reflection costs at most 0.0000555 through radius
342.9, using the same moment calculation as the earlier range. -/
theorem gaussian_joint_mid_lower_197 (hRH : RiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc 332.15 342.9) (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4)
    (hprefix : ∀ n : ℕ, (n : ℝ) ≤ r ^ 2 → ArithmeticFunction.vonMangoldt n ≠ 0 → α n = 0) :
    (-0.000055 : ℝ) ≤
      ∑ i, (gaussianCoeff197 i : ℝ) * quarterAuxReflection656 α r (quarterShift663 i : ℝ) := by
  have hhi :=
    (Analysis.rationalLogIntervalCheck_sound (N := 342.9) (j := 9) (n := 27) (lo := 5) (hi := 5.838)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofScientific] at hhi
  have hrU : r ≤ (3429 / 10 : ℝ) := by linarith only [hr.2]
  have hl := (Real.log_le_log ((by norm_num only : (0 : ℝ) < 332.15).trans_le hr.1) hrU).trans hhi
  have h :=
    joint_lower_box hRH (u := 11.852) (L := 11.676) (E := 0.000055)
      ⟨hr.1, hr.2.trans (by norm_num only)⟩
      (by
        norm_num only [Rat.cast_ofScientific]; linarith only [hl])
      (by norm_num only [Rat.cast_ofScientific]) (by decide +kernel) α hα hprefix
  norm_num only [Rat.cast_ofScientific] at h ⊢
  exact h

/-- For radii from 332.15 to 346.1, the combined K197 reflection
is at least -0.00006 by the common endpoint moment estimate. -/
theorem gaussian_joint_to34610 (hRH : RiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 332.15 346.1)
    (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4)
    (hprefix : ∀ n : ℕ, (n : ℝ) ≤ r ^ 2 → ArithmeticFunction.vonMangoldt n ≠ 0 → α n = 0) :
    (-0.00006 : ℝ) ≤
      ∑ i, (gaussianCoeff197 i : ℝ) * quarterAuxReflection656 α r (quarterShift663 i : ℝ) := by
  have hhi :=
    (Analysis.rationalLogIntervalCheck_sound (N := 346.1) (j := 9) (n := 27) (lo := 5) (hi := 5.847)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofScientific] at hhi
  have hrU : r ≤ (3461 / 10 : ℝ) := by linarith only [hr.2]
  have hl := (Real.log_le_log ((by norm_num only : (0 : ℝ) < 332.15).trans_le hr.1) hrU).trans hhi
  have h :=
    joint_lower_box hRH (u := 11.888) (L := 11.694) (E := 0.00006)
      ⟨hr.1, hr.2.trans (by norm_num only)⟩
      (by
        norm_num only [Rat.cast_ofScientific]; linarith only [hl])
      (by norm_num only [Rat.cast_ofScientific]) (by decide +kernel) α hα hprefix
  norm_num only [Rat.cast_ofScientific] at h ⊢
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
