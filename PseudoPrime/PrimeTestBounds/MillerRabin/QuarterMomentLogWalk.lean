/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogWalkBounds

/-! # Fixed-point logarithm bounds for the section 137 prime powers -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If the walked index is a positive power of a natural base, the same
fixed-point interval bounds the scaled base logarithm after division by the
exponent. This lets the moment checker reuse the index enclosure. -/
theorem quarter_log_walk_power {S a lo hi steps p k : ℕ} (ha : 0 < a) (hk : 0 < k)
    (hindex : a + steps = p ^ k) (hlo : (lo : ℝ) ≤ S * Real.log a)
    (hhi : (S : ℝ) * Real.log a ≤ hi) :
    let bounds := Analysis.logWalk S a lo hi steps
    (S : ℝ) * Real.log p ∈ Set.Icc ((bounds.1 : ℝ) / k) ((bounds.2 : ℝ) / k) := by
  have h := Analysis.logWalk_bounds S a lo hi steps ha hlo hhi
  rw [hindex, Nat.cast_pow, Real.log_pow, ← mul_assoc, mul_comm (S : ℝ) (k : ℝ), mul_assoc] at h
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  exact
    ⟨(div_le_iff₀ hkR).mpr (by simpa only [mul_comm _ (k : ℝ)] using h.1),
      (le_div_iff₀ hkR).mpr (by simpa only [mul_comm _ (k : ℝ)] using h.2)⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
