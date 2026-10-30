/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RealAxisDifferenceWeights

/-! # Arbitrary-parameter product majorants and Poisson differences -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Positive ordered alpha,beta whose square sum and product lie below the rho
budgets give a whole-height fourth-order product majorant. Compare denominator
polynomials using t^2>=0. No sampled heights or finite zero lists are involved. -/
theorem pole_four_product_majorant {ρ α β t : ℝ} (hr : 0 < ρ) (ha : 0 < α) (hab : α < β)
    (hS : α ^ 2 + β ^ 2 ≤ 2 * ρ ^ 2) (hP : α * β ≤ ρ ^ 2) :
    ρ ^ 3 / (ρ ^ 2 + t ^ 2) ^ 2 ≤ ρ ^ 3 / ((α ^ 2 + t ^ 2) * (β ^ 2 + t ^ 2)) := by
  have hb := ha.trans hab
  have hp := mul_self_le_mul_self (mul_nonneg ha.le hb.le) hP
  have hs := mul_le_mul_of_nonneg_right hS (sq_nonneg t)
  apply
    div_le_div_of_nonneg_left (pow_nonneg hr.le 3)
      (mul_pos (add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t))
        (add_pos_of_pos_of_nonneg (sq_pos_of_pos hb) (sq_nonneg t)))
  nlinarith only [hp, hs]

/-- The rational product majorant is exactly a signed difference of two Poisson
profiles for 0<alpha<beta. Cancel the positive scale factors and combine fractions.
Keeping this difference intact permits the retained paired-Euler zero-mass API. -/
theorem pole_product_eq_poisson_difference {ρ α β t : ℝ} (ha : 0 < α) (hab : α < β) :
    ρ ^ 3 / ((α ^ 2 + t ^ 2) * (β ^ 2 + t ^ 2)) =
      poissonDifferenceWeight α β (ρ ^ 3 / (α * (β ^ 2 - α ^ 2))) (ρ ^ 3 / (β * (β ^ 2 - α ^ 2)))
        t := by
  have hb := ha.trans hab
  have haD : α ^ 2 + t ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t))
  have hbD : β ^ 2 + t ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos hb) (sq_nonneg t))
  have hd : β ^ 2 - α ^ 2 ≠ 0 := ne_of_gt (by nlinarith only [ha, hab])
  unfold poissonDifferenceWeight
  have hu : ρ ^ 3 / (α * (β ^ 2 - α ^ 2)) * α = ρ ^ 3 / (β ^ 2 - α ^ 2) := by
    rw [mul_comm α (β ^ 2 - α ^ 2), div_mul_eq_mul_div, mul_div_mul_right _ _ ha.ne']
  have hv : ρ ^ 3 / (β * (β ^ 2 - α ^ 2)) * β = ρ ^ 3 / (β ^ 2 - α ^ 2) := by
    rw [mul_comm β (β ^ 2 - α ^ 2), div_mul_eq_mul_div, mul_div_mul_right _ _ hb.ne']
  rw [hu, hv, div_sub_div _ _ haD hbD]
  congr 1
  rw [div_mul_eq_mul_div, ← mul_div_assoc, ← sub_div]
  apply (eq_div_iff hd).mpr
  ring

end PseudoPrime.Analysis
