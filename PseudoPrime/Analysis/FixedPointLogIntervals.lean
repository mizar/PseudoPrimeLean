/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Outward fixed-point intervals for logarithms -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The natural floor of scale times the rational Taylor logarithm lower
endpoint. A successful logarithm check ensures this truncation is a lower bound. -/
def logFixedLower (p : ℚ) (j n scale : ℕ) : ℕ :=
  ⌊(scale : ℚ) * rationalLogLower p j n⌋₊

/-- The natural ceiling of scale times the rational Taylor logarithm upper
endpoint. Its soundness follows from the rational interval and upward rounding. -/
def logFixedUpper (p : ℚ) (j n scale : ℕ) : ℕ :=
  ⌈(scale : ℚ) * rationalLogUpper p j n⌉₊

/-- Check positivity, the logarithm Taylor displacement and nonnegativity
of the lower rational endpoint. The final condition makes natural flooring sound. -/
def logFixedCheck (p : ℚ) (j n : ℕ) : Bool :=
  decide (0 < p ∧ |1 - p / 2 ^ j| < 1 ∧ 0 ≤ rationalLogLower p j n)

/-- A successful logarithm check gives both outward scaled natural bounds
for the real logarithm, at every natural scale. Cast rational floor and ceiling bounds
and compose with the existing Taylor interval theorem. -/
theorem logFixed_bounds {p : ℚ} {j n scale : ℕ} (hc : logFixedCheck p j n = true) :
    (logFixedLower p j n scale : ℝ) ≤ (scale : ℝ) * Real.log (p : ℝ) ∧
      (scale : ℝ) * Real.log (p : ℝ) ≤ (logFixedUpper p j n scale : ℝ) := by
  have h : 0 < p ∧ |1 - p / 2 ^ j| < 1 ∧ 0 ≤ rationalLogLower p j n := of_decide_eq_true hc
  have hl := rationalLogBounds_sound h.1 j n h.2.1
  have hfloor := Nat.floor_le (mul_nonneg (Nat.cast_nonneg scale : (0 : ℚ) ≤ scale) h.2.2)
  have hceil := Nat.le_ceil ((scale : ℚ) * rationalLogUpper p j n)
  have hf := (Rat.cast_le (K := ℝ)).mpr hfloor
  have hu := (Rat.cast_le (K := ℝ)).mpr hceil
  simp only [Rat.cast_natCast, Rat.cast_mul] at hf hu
  constructor
  · exact hf.trans (mul_le_mul_of_nonneg_left hl.1 (Nat.cast_nonneg scale))
  · exact (mul_le_mul_of_nonneg_left hl.2 (Nat.cast_nonneg scale)).trans hu

end PseudoPrime.Analysis
