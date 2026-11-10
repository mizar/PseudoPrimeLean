/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterInteriorPrimitive

/-! # Scalar reduction for the interior large-index argument -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At a positive interior scale, combine the Chebyshev boundary expression
with the joint primitive. Power identities expose the main term and two
quarter-power corrections used in the scalar comparison. -/
theorem quarter_interior_endpoint {X : ℝ} (hX : 0 < X) :
    ((48 - 2 * Real.log X) * X ^ (-1 / 2 : ℝ)) *
          (X - (19 / 30 : ℝ) * X ^ (3 / 4 : ℝ) - (63 / 10 : ℝ) * X ^ (1 / 4 : ℝ) - 1839 / 1000) +
        quarterJointPrimitive (12 - Real.log X / 4) X =
      (100 - 4 * Real.log X) * Real.sqrt X -
          (19 / 30 : ℝ) * (156 - 6 * Real.log X) * X ^ (1 / 4 : ℝ) +
        (1386 / 5 - (63 / 5 : ℝ) * Real.log X) * X ^ (-1 / 4 : ℝ) := by
  have h1 : X ^ (-1 / 2 : ℝ) * X = Real.sqrt X := by
    have h := Real.rpow_add hX (-1 / 2) 1
    norm_num only [Real.rpow_one] at h
    simpa only [neg_div, Real.sqrt_eq_rpow] using h.symm
  have h2 : X ^ (-1 / 2 : ℝ) * X ^ (3 / 4 : ℝ) = X ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hX]
    congr 1
    norm_num only
  have h3 : X ^ (-1 / 2 : ℝ) * X ^ (1 / 4 : ℝ) = X ^ (-1 / 4 : ℝ) := by
    rw [← Real.rpow_add hX]
    congr 1
    norm_num only
  dsimp only [quarterJointPrimitive]
  rw [← Real.sqrt_eq_rpow]
  calc
    _ =
        (48 - 2 * Real.log X) * (X ^ (-1 / 2 : ℝ) * X) +
            (4 * (12 - Real.log X / 4) + 4 - Real.log X) * Real.sqrt X -
          (19 / 30 : ℝ) *
            ((48 - 2 * Real.log X) * (X ^ (-1 / 2 : ℝ) * X ^ (3 / 4 : ℝ)) +
              (8 * (12 - Real.log X / 4) + 12 - 2 * Real.log X) * X ^ (1 / 4 : ℝ)) -
          (63 / 10 : ℝ) *
            ((48 - 2 * Real.log X) * (X ^ (-1 / 2 : ℝ) * X ^ (1 / 4 : ℝ)) +
              (-8 * (12 - Real.log X / 4) + 4 + 2 * Real.log X) * X ^ (-1 / 4 : ℝ)) :=
      by ring
    _ = _ := by
      rw [h1, h2, h3]; ring

/-- Under GRH, the no-witness hypothesis and index at least 33000 imply the
displayed elementary inequality. Evaluate both primitive endpoints and discard
the nonnegative inverse-quarter-power term. This reduces witness extraction to
a strict scalar gap. -/
theorem quarter_interior_reduced {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) {r T : ℝ} (hr : 4 ≤ r)
    (hbound : Real.log (r ^ 2) ≤ 16) (hT : 0 ≤ T) (hscale : Real.log n ≤ T)
    (hindex : 33000 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hnone :
      ¬∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    (100 - 4 * Real.log (r ^ 2)) * r - (19 / 30 : ℝ) * (156 - 6 * Real.log (r ^ 2)) * Real.sqrt r -
        ((98717 / 12000 : ℝ) * (48 - Real.log (r ^ 2) - Real.log 16) - 59 / 5) ≤
      (32 - Real.log (r ^ 2)) * T + (137 / 330 : ℝ) * (r + r⁻¹) +
        (4 / 15 : ℝ) * (Real.sqrt r + (Real.sqrt r)⁻¹) +
        15 / 11 := by
  have hr0 : 0 < r := by linarith only [hr]
  have h := quarter_interior_primitive hn ho hr hbound hT hscale hindex hGRH hnone
  rw [← add_sub_assoc, quarter_interior_endpoint (sq_pos_of_pos hr0),
    quarter_joint_primitive_sixteen] at h
  have hquarter : (r ^ 2) ^ (1 / 4 : ℝ) = Real.sqrt r := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr0.le]
    norm_num only [Real.sqrt_eq_rpow]
  have hquarterInv : (r ^ 2) ^ (-1 / 4 : ℝ) = (Real.sqrt r)⁻¹ := by
    rw [neg_div, Real.rpow_neg (sq_nonneg r), hquarter]
  rw [Real.sqrt_sq hr0.le, hquarter, hquarterInv] at h
  have hpos : 0 ≤ (1386 / 5 - (63 / 5 : ℝ) * Real.log (r ^ 2)) * (Real.sqrt r)⁻¹ :=
    mul_nonneg (by linarith only [hbound]) (inv_nonneg.mpr (Real.sqrt_nonneg r))
  linarith only [h, hpos]

end PseudoPrime.PrimeTestBounds.MillerRabin
