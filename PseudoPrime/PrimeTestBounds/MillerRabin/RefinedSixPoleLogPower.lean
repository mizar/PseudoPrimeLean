/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleMonotonicity

/-! # Logarithmic power monotonicity for reflected moments -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At a positive argument, differentiate a positive integral power of an
affine logarithm times a real power. The factored derivative makes its sign explicit. -/
theorem refined_log_power_deriv (k : ℕ) {b p x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ ↦ (b + 2 * Real.log t) ^ (k + 1) * t ^ (-p))
      (x ^ (-p - 1) * (b + 2 * Real.log x) ^ k * (2 * (k + 1 : ℕ) - p * (b + 2 * Real.log x)))
      x := by
  have hd :=
    (((Real.hasDerivAt_log hx.ne').const_mul 2).const_add b).pow (k + 1) |>.mul
      (Real.hasDerivAt_rpow_const (Or.inl hx.ne') (p := -p))
  have he :
    (k + 1 : ℕ) * (b + 2 * Real.log x) ^ k * (2 * x⁻¹) * x ^ (-p) +
        (b + 2 * Real.log x) ^ (k + 1) * (-p * x ^ (-p - 1)) =
      x ^ (-p - 1) * (b + 2 * Real.log x) ^ k * (2 * (k + 1 : ℕ) - p * (b + 2 * Real.log x)) := by
    rw [Real.rpow_sub_one hx.ne' (-p), pow_succ]
    ring
  simpa only [Nat.add_sub_cancel] using he ▸ hd

/-- When the derivative is nonpositive at an entrance `E ≥ 1`, the associated
logarithmic power decreases on `[E, ∞)`. Nonnegativity of its logarithmic base
and monotonicity of the logarithm retain the sign beyond the entrance. -/
theorem refined_log_power_antitone (k : ℕ) {b p E : ℝ} (hE : 1 ≤ E) (hp : 0 ≤ p)
    (hb : 0 ≤ b + 2 * Real.log E) (hbound : 2 * (k + 1 : ℕ) ≤ p * (b + 2 * Real.log E)) :
    AntitoneOn (fun t : ℝ ↦ (b + 2 * Real.log t) ^ (k + 1) * t ^ (-p)) (Set.Ici E) := by
  apply
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici E)
      (fun x hx ↦
        (refined_log_power_deriv k (b := b) (p := p)
            (zero_lt_one.trans_le (hE.trans hx))).continuousAt.continuousWithinAt)
      (fun x hx ↦
        (refined_log_power_deriv k (b := b) (p := p)
            (zero_lt_one.trans_le (hE.trans (interior_subset hx)))).hasDerivWithinAt)
  intro x hx
  have hxE : E ≤ x := interior_subset hx
  have hl := Real.log_le_log (zero_lt_one.trans_le hE) hxE
  have hm :=
    mul_le_mul_of_nonneg_left (show b + 2 * Real.log E ≤ b + 2 * Real.log x by linarith only [hl])
      hp
  have hs : 2 * (k + 1 : ℕ) - p * (b + 2 * Real.log x) ≤ 0 := by linarith only [hbound, hm]
  have hz : 0 ≤ b + 2 * Real.log x := by linarith only [hb, hl]
  exact
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (hE.trans hxE)) _) (pow_nonneg hz k)) hs

end PseudoPrime.PrimeTestBounds.MillerRabin
