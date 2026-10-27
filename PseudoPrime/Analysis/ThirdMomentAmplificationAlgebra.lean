/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Algebraic comparisons for third-moment energy amplification -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Eliminate the support size from the squared off-diagonal budget using
sΔ²≤4B. Keep both the main term and the square-root error term. Clear the
positive p² denominator, compare the two support factors separately, and
recombine. This is the first algebraic step toward the E¹³ bound. -/
theorem off_diagonal_budget_le_without_support {p E B D s T J e R : ℝ} (hp : 0 < p) (hE : 0 ≤ E)
    (hs : 0 ≤ s) (hT : 0 ≤ T) (hJ : 0 ≤ J) (he : 0 ≤ e) (hS : s * D ^ 2 ≤ 4 * B)
    (hR : R ^ 2 ≤ D ^ 4 * T * J * (4 * s ^ 2 * E / p ^ 2 + 4096 * s * p * e)) :
    p ^ 2 * R ^ 2 ≤ 64 * T * J * B ^ 2 * E + 16384 * T * J * B * D ^ 2 * p ^ 3 * e := by
  have hscaled := mul_le_mul_of_nonneg_left hR (sq_nonneg p)
  have hid :
    p ^ 2 * (D ^ 4 * T * J * (4 * s ^ 2 * E / p ^ 2 + 4096 * s * p * e)) =
      T * J * (4 * (s * D ^ 2) ^ 2 * E + 4096 * (s * D ^ 2) * D ^ 2 * p ^ 3 * e) := by
    field_simp [hp.ne']
  rw [hid] at hscaled
  have hS2 := pow_le_pow_left₀ (mul_nonneg hs (sq_nonneg D)) hS 2
  have h₁ :=
    mul_le_mul_of_nonneg_left hS2
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hT) hJ) hE)
  have h₂ :=
    mul_le_mul_of_nonneg_left hS
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4096) hT) hJ)
            (sq_nonneg D))
          (pow_nonneg hp.le 3))
        he)
  nlinarith only [hscaled, h₁, h₂]

/-- If the diagonal contribution dominates B²E, the retained-energy and
height constraints force a cubic bound on E. Cancel the positive B and
multiply the proved inequalities. This handles the diagonal alternative
without discarding it from the amplified comparison. -/
theorem energy_cube_le_of_diagonal_dominates {p E B D T J : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hB : 0 < B) (hJ : 0 ≤ J) (hcover : E ≤ 2 * J * B) (hheight : D * E ≤ 10 * T)
    (hdiag : B ^ 2 * E ≤ 2 * p ^ 4 * D * B) : E ^ 3 ≤ 40 * p ^ 4 * T * J := by
  have hBE : B * E ≤ 2 * p ^ 4 * D := (mul_le_mul_iff_left₀ hB).mp (by nlinarith only [hdiag])
  have hc := mul_le_mul_of_nonneg_right hcover hE
  have hb := mul_le_mul_of_nonneg_left hBE (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hJ)
  have hE2 : E ^ 2 ≤ 4 * J * p ^ 4 * D := by nlinarith only [hc, hb]
  have h₁ := mul_le_mul_of_nonneg_right hE2 hE
  have h₂ :=
    mul_le_mul_of_nonneg_left hheight
      (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hJ) (pow_nonneg hp 4))
  nlinarith only [h₁, h₂]

end PseudoPrime.Analysis
