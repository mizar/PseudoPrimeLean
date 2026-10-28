/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMRClippedNumerics

/-! # Quadratic roots for Gaussian budgets -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The positive quadratic root of d*t squared=b*t+C when d and b are positive.
The input C is a scalar budget; nonnegativity of C is required by the root equation.
Gaussian candidates use this definition before applying radius floors. -/
noncomputable def gaussianBudgetRoot (d b C : ℝ) : ℝ :=
  (b + Real.sqrt (b ^ 2 + 4 * d * C)) / (2 * d)

/-- For d>0 and b>0, the root is positive for every real C. Its numerator
contains b and a nonnegative square root. This supplies positive Gaussian radii. -/
theorem gaussianBudgetRoot_pos {d b C : ℝ} (hd : 0 < d) (hb : 0 < b) :
    0 < gaussianBudgetRoot d b C := by
  exact div_pos (add_pos_of_pos_of_nonneg hb (Real.sqrt_nonneg _)) (mul_pos (by norm_num only) hd)

/-- For d>0 and C>=0, the root satisfies d*t squared=b*t+C. An exact
rational identity and the squared discriminant prove the equation before clipping. -/
theorem gaussianBudgetRoot_equation {d b C : ℝ} (hd : 0 < d) (hC : 0 ≤ C) :
    d * gaussianBudgetRoot d b C ^ 2 = b * gaussianBudgetRoot d b C + C := by
  have hz :=
    Real.sq_sqrt
      (add_nonneg (sq_nonneg b) (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hd.le) hC))
  have hid :
    d * gaussianBudgetRoot d b C ^ 2 - b * gaussianBudgetRoot d b C - C =
      ((Real.sqrt (b ^ 2 + 4 * d * C)) ^ 2 - (b ^ 2 + 4 * d * C)) / (4 * d) := by
    dsimp only [gaussianBudgetRoot]
    field_simp [hd.ne']
    ring
  rw [hz] at hid
  simp only [sub_self, zero_div] at hid
  linarith only [hid]

/-- For positive d,b and nonnegative C, a radius r with d*r>b and
d*r squared>=C+b*r bounds the root above. Factor the quadratic difference.
This turns scalar certificates into continuous root upper bounds. -/
theorem gaussianBudgetRoot_le_of_budget {d b C r : ℝ} (hd : 0 < d) (hb : 0 < b) (hC : 0 ≤ C)
    (hr : b < d * r) (hbudget : C + b * r ≤ d * r ^ 2) : gaussianBudgetRoot d b C ≤ r := by
  have ht := gaussianBudgetRoot_pos (C := C) hd hb
  have he := gaussianBudgetRoot_equation (b := b) hd hC
  by_contra hn
  have hrt := lt_of_not_ge hn
  have hdroot := mul_nonneg hd.le ht.le
  have hp :=
    mul_pos (sub_pos.mpr hrt)
      (by linarith only [hr, hdroot] : 0 < d * (gaussianBudgetRoot d b C + r) - b)
  nlinarith only [hp, he, hbudget]

/-- For positive d,b and nonnegative C, every r above the root with
d*r>b satisfies its budget inequality. Factor the quadratic difference to retain
an inequality after a candidate radius is increased by a maximum. -/
theorem gaussianBudget_of_root_le {d b C r : ℝ} (hd : 0 < d) (hb : 0 < b) (hC : 0 ≤ C)
    (hr : b < d * r) (hroot : gaussianBudgetRoot d b C ≤ r) : C + b * r ≤ d * r ^ 2 := by
  have ht := gaussianBudgetRoot_pos (C := C) hd hb
  have he := gaussianBudgetRoot_equation (b := b) hd hC
  have hdroot := mul_nonneg hd.le ht.le
  have hp :=
    mul_nonneg (sub_nonneg.mpr hroot)
      (by linarith only [hr, hdroot] : 0 ≤ d * (r + gaussianBudgetRoot d b C) - b)
  nlinarith only [hp, he]

/-- For d>0, increasing C cannot decrease the quadratic root. Monotonicity
of the square root and division by the positive denominator give the comparison. -/
theorem gaussianBudgetRoot_mono {d b C D : ℝ} (hd : 0 < d) (hCD : C ≤ D) :
    gaussianBudgetRoot d b C ≤ gaussianBudgetRoot d b D := by
  have hc := mul_le_mul_of_nonneg_left hCD (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hd.le)
  exact
    div_le_div_of_nonneg_right
      (add_le_add (le_refl b) (Real.sqrt_le_sqrt (add_le_add (le_refl (b ^ 2)) hc)))
      (mul_nonneg (by norm_num only) hd.le)

/-- For d>0 and 0<=C<D, the root at C is strictly below the root at D.
Use strict monotonicity of the square root on the nonnegative discriminants.
This compares Gaussian residual allowances without numerical crossings. -/
theorem gaussianBudgetRoot_strictMono {d b C D : ℝ} (hd : 0 < d) (hC : 0 ≤ C) (hCD : C < D) :
    gaussianBudgetRoot d b C < gaussianBudgetRoot d b D := by
  have hc := mul_lt_mul_of_pos_left hCD (mul_pos (by norm_num only : (0 : ℝ) < 4) hd)
  have hdisc :=
    add_nonneg (sq_nonneg b) (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hd.le) hC)
  have hrad : b ^ 2 + 4 * d * C < b ^ 2 + 4 * d * D := by linarith only [hc]
  have hsqrt := Real.sqrt_lt_sqrt hdisc hrad
  apply div_lt_div_of_pos_right _ (mul_pos (by norm_num only) hd)
  linarith only [hsqrt]

end PseudoPrime.Analysis
