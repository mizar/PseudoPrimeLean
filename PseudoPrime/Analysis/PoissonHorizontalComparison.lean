/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Tactic

/-! # Horizontal comparisons of positive Poisson kernels -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For positive a<=b, the Poisson kernel at horizontal distance a is at most b/a
times the kernel at b, at every real height. Clear positive denominators and use
(b^2-a^2)*t^2>=0. This compares endpoint zero masses without taking separate norms. -/
theorem poisson_horizontal_kernel_le_scaled {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    a / (a ^ 2 + t ^ 2) ≤ (b / a) * (b / (b ^ 2 + t ^ 2)) := by
  have hb := ha.trans_le hab
  have hA : 0 < a ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t)
  have hB : 0 < b ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hb) (sq_nonneg t)
  have he : (b / a) * (b / (b ^ 2 + t ^ 2)) = b ^ 2 / (a * (b ^ 2 + t ^ 2)) := by
    field_simp [ha.ne', hB.ne']
  rw [he]
  apply (div_le_div_iff₀ hA (mul_pos ha hB)).mpr
  have hsq : 0 ≤ b ^ 2 - a ^ 2 := by nlinarith only [hab, ha, hb]
  nlinarith only [mul_nonneg hsq (sq_nonneg t)]

end PseudoPrime.Analysis
