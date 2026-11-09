/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Rational logarithm checks for interval budgets -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A checked logarithm lower bound for a positive integer `C` also bounds
the logarithm of any integer `D ≥ C`. This allows a compact factorial-product
lower certificate to stand in for a large binomial coefficient. -/
theorem log_lower_of_integer_bound {C D j : ℕ} {lo hi : ℚ} (hC : 0 < C) (hCD : C ≤ D)
    (hlog : Analysis.rationalLogIntervalCheck C j 12 lo hi = true) : (lo : ℝ) ≤ Real.log D := by
  have h := (Analysis.rationalLogIntervalCheck_sound hlog).1
  simp only [Rat.cast_natCast] at h
  exact h.trans (Real.log_le_log (Nat.cast_pos.mpr hC) (Nat.cast_le.mpr hCD))

/-- Checked logarithm intervals and rational endpoint inequalities imply the
two square-cell log budgets. Multiply the radius bound by nonnegative `k`
and cast the exact rational comparisons to the reals. -/
theorem square_cell_checked_logs {B C k jB jC : ℕ} {a b loB hiB loC hiC : ℚ}
    (hB : Analysis.rationalLogIntervalCheck B jB 12 loB hiB = true)
    (hC : Analysis.rationalLogIntervalCheck C jC 12 loC hiC = true) (hsize : (k : ℚ) * hiB < a)
    (hcount : b < 2 * loC) : (k : ℝ) * Real.log B < a ∧ (b : ℝ) < 2 * Real.log C := by
  have hlogB := (Analysis.rationalLogIntervalCheck_sound hB).2
  have hlogC := (Analysis.rationalLogIntervalCheck_sound hC).1
  simp only [Rat.cast_natCast] at hlogB hlogC
  have hsizeR : (k : ℝ) * (hiB : ℝ) < (a : ℝ) := by exact_mod_cast hsize
  have hcountR : (b : ℝ) < 2 * (loC : ℝ) := by exact_mod_cast hcount
  have hmul := mul_le_mul_of_nonneg_left hlogB (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  constructor
  · exact hmul.trans_lt hsizeR
  · linarith only [hlogC, hcountR]

/-- Checked logarithm intervals and rational endpoint inequalities imply the
two semiprime-cell log budgets for the two-thirds split. The non-strict
inequalities suffice because the large-factor branch itself is strict. -/
theorem semiprime_cell_checked_logs {B C k jB jC : ℕ} {a b loB hiB loC hiC : ℚ}
    (hB : Analysis.rationalLogIntervalCheck B jB 12 loB hiB = true)
    (hC : Analysis.rationalLogIntervalCheck C jC 12 loC hiC = true)
    (hsize : 3 * (k : ℚ) * hiB ≤ 2 * a) (hcount : b ≤ 3 * loC) :
    (k : ℝ) * Real.log B ≤ (2 / 3 : ℝ) * a ∧ (b : ℝ) / 3 ≤ Real.log C := by
  have hlogB := (Analysis.rationalLogIntervalCheck_sound hB).2
  have hlogC := (Analysis.rationalLogIntervalCheck_sound hC).1
  simp only [Rat.cast_natCast] at hlogB hlogC
  have hsizeR : 3 * (k : ℝ) * (hiB : ℝ) ≤ 2 * (a : ℝ) := by exact_mod_cast hsize
  have hcountR : (b : ℝ) ≤ 3 * (loC : ℝ) := by exact_mod_cast hcount
  have hmul := mul_le_mul_of_nonneg_left hlogB (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  constructor <;> linarith only [hmul, hsizeR, hlogC, hcountR]

end PseudoPrime.PrimeTestBounds.MillerRabin
