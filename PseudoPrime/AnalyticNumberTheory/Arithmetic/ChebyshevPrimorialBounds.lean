/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev

/-! # Chebyshev theta bounds from primorial comparisons -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Consecutive powers of two bounding the primorial through `n` give matching
logarithmic lower and upper bounds for `theta n`. The natural-number inequalities
can be certified independently of the real logarithm calculation. -/
theorem theta_bounds_of_primorial_pow_two {n k : ℕ} (hlower : 2 ^ k ≤ primorial n)
    (hupper : primorial n ≤ 2 ^ (k + 1)) :
    (k : ℝ) * Real.log 2 ≤ Chebyshev.theta n ∧ Chebyshev.theta n ≤ (k + 1 : ℕ) * Real.log 2 := by
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num only) k
  have hl : (2 : ℝ) ^ k ≤ (primorial n : ℝ) := by exact_mod_cast hlower
  have hp : (0 : ℝ) < primorial n := by exact_mod_cast primorial_pos n
  have hu : (primorial n : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by exact_mod_cast hupper
  have h1 := Real.log_le_log hpos hl
  have h2 := Real.log_le_log hp hu
  rw [Real.log_pow] at h1 h2
  exact ⟨h1, h2⟩

end PseudoPrime.AnalyticNumberTheory.Arithmetic
