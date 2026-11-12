/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevWalkSound
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Logarithm certificates for fixed-point prime-power walk entries -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A successful rational logarithm check certifies the fixed-point bounds
carried by a prime-power walk entry, provided the scale is positive. The
integer values and the checker data remain independent of any particular walk. -/
theorem psi_walk_power_valid_of_check {S p k lo hi j terms : ℕ} (hS : 0 < S)
    (hc : Analysis.rationalLogIntervalCheck (p : ℚ) j terms ((lo : ℚ) / S) ((hi : ℚ) / S) = true) :
    PsiWalkEntryValid S (.power p k lo hi) := by
  have h := Analysis.rationalLogIntervalCheck_sound hc
  simp only [Rat.cast_div, Rat.cast_natCast] at h
  have hs : (0 : ℝ) < S := Nat.cast_pos.mpr hS
  change (lo : ℝ) ≤ S * Real.log p ∧ (S : ℝ) * Real.log p ≤ hi
  constructor
  · simpa only [mul_comm] using (div_le_iff₀ hs).mp h.1
  · simpa only [mul_comm] using (le_div_iff₀ hs).mp h.2

end PseudoPrime.AnalyticNumberTheory.Arithmetic
