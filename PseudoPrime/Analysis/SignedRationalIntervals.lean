/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order

/-! # Signed rational interval transport -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A real value in a rational interval gives both signed scalar
bounds. Split by the rational coefficient sign and use order preservation
or reversal under multiplication. This is the node interval interface. -/
theorem signed_rational_node_bounds {b l u : ℚ} {v : ℝ} (hl : (l : ℝ) ≤ v) (hu : v ≤ (u : ℝ)) :
    ((b * (if 0 ≤ b then l else u) : ℚ) : ℝ) ≤ (b : ℝ) * v ∧
      (b : ℝ) * v ≤ ((b * (if 0 ≤ b then u else l) : ℚ) : ℝ) := by
  by_cases hb : 0 ≤ b
  · rw [ite_eq_left hb, ite_eq_left hb, Rat.cast_mul, Rat.cast_mul]
    exact
      ⟨mul_le_mul_of_nonneg_left hl ((Rat.cast_nonneg (K := ℝ)).mpr hb),
        mul_le_mul_of_nonneg_left hu ((Rat.cast_nonneg (K := ℝ)).mpr hb)⟩
  · rw [ite_eq_right hb, ite_eq_right hb, Rat.cast_mul, Rat.cast_mul]
    have hbR : (b : ℝ) ≤ 0 := ((Rat.cast_nonpos (K := ℝ)).mpr (le_of_not_ge hb))
    exact ⟨mul_le_mul_of_nonpos_left hu hbR, mul_le_mul_of_nonpos_left hl hbR⟩

end PseudoPrime.Analysis
