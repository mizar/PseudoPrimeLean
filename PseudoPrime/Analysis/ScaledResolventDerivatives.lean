/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic

/-! # Derivatives and uniform curvature of scaled Poisson resolvents -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The scaled Poisson resolvent a(1+t²)/(a²+t²). For positive a it is smooth on
all real ordinates. Its derivative bounds control rational Gamma majorants. -/
noncomputable def scaledResolvent (a t : ℝ) : ℝ :=
  a * (1 + t ^ 2) / (a ^ 2 + t ^ 2)

/-- First derivative of the scaled resolvent, written as a rational expression.
The positive-scale derivative theorem identifies it with the derivative of scaledResolvent. -/
noncomputable def scaledResolventDeriv (a t : ℝ) : ℝ :=
  -2 * a * (1 - a ^ 2) * t / (a ^ 2 + t ^ 2) ^ 2

/-- Second derivative of the scaled resolvent. The numerator separates the factor
1-a² from 3t²-a², allowing a uniform bound independent of the ordinate. -/
noncomputable def scaledResolventSecondDeriv (a t : ℝ) : ℝ :=
  2 * a * (1 - a ^ 2) * (3 * t ^ 2 - a ^ 2) / (a ^ 2 + t ^ 2) ^ 3

/-- At positive scale a, the first rational expression is the derivative of
scaledResolvent at every t. Apply the quotient rule and normalize its numerator. -/
theorem hasDerivAt_scaledResolvent {a t : ℝ} (ha : 0 < a) :
    HasDerivAt (scaledResolvent a) (scaledResolventDeriv a t) t := by
  dsimp only [scaledResolvent, scaledResolventDeriv]
  have hd : a ^ 2 + t ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t))
  have h :=
    (((hasDerivAt_const t 1).add ((hasDerivAt_id t).pow 2)).const_mul a).div
      ((hasDerivAt_const t (a ^ 2)).add ((hasDerivAt_id t).pow 2)) hd
  change
    HasDerivAt (fun x : ℝ ↦ a * (1 + x ^ 2) / (a ^ 2 + x ^ 2))
      ((a * (0 + 2 * t ^ (2 - 1) * 1) * (a ^ 2 + t ^ 2) -
          a * (1 + t ^ 2) * (0 + 2 * t ^ (2 - 1) * 1)) /
        (a ^ 2 + t ^ 2) ^ 2)
      t at h
  have he :
    -2 * a * (1 - a ^ 2) * t =
      a * (0 + 2 * t ^ (2 - 1) * 1) * (a ^ 2 + t ^ 2) -
        a * (1 + t ^ 2) * (0 + 2 * t ^ (2 - 1) * 1) := by
    ring
  rw [he]
  exact h

/-- At positive scale a, the second rational expression differentiates
scaledResolventDeriv. The quotient rule and cancellation of a nonzero denominator
supply the curvature needed for interpolation certificates. -/
theorem hasDerivAt_scaledResolventDeriv {a t : ℝ} (ha : 0 < a) :
    HasDerivAt (scaledResolventDeriv a) (scaledResolventSecondDeriv a t) t := by
  dsimp only [scaledResolventDeriv, scaledResolventSecondDeriv]
  have hd : a ^ 2 + t ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t))
  have h :=
    ((hasDerivAt_id t).const_mul (-2 * a * (1 - a ^ 2))).div
      (((hasDerivAt_const t (a ^ 2)).add ((hasDerivAt_id t).pow 2)).pow 2) (pow_ne_zero 2 hd)
  change
    HasDerivAt (fun x : ℝ ↦ -2 * a * (1 - a ^ 2) * x / (a ^ 2 + x ^ 2) ^ 2)
      (((-2 * a * (1 - a ^ 2) * 1) * (a ^ 2 + t ^ 2) ^ 2 -
          (-2 * a * (1 - a ^ 2) * t) *
            (2 * (a ^ 2 + t ^ 2) ^ (2 - 1) * (0 + 2 * t ^ (2 - 1) * 1))) /
        ((a ^ 2 + t ^ 2) ^ 2) ^ 2)
      t at h
  have he :
    2 * a * (1 - a ^ 2) * (3 * t ^ 2 - a ^ 2) / (a ^ 2 + t ^ 2) ^ 3 =
      ((-2 * a * (1 - a ^ 2) * 1) * (a ^ 2 + t ^ 2) ^ 2 -
          (-2 * a * (1 - a ^ 2) * t) *
            (2 * (a ^ 2 + t ^ 2) ^ (2 - 1) * (0 + 2 * t ^ (2 - 1) * 1))) /
        ((a ^ 2 + t ^ 2) ^ 2) ^ 2 := by
    field_simp (discharger := exact hd)
    ring
  rw [he]
  exact h

/-- For positive scale a, the absolute second derivative is at most
6|1-a²|/a³ everywhere. Bound |3t²-a²| by 3(a²+t²), then use a²≤a²+t².
Summing these bounds controls the curvature of a signed resolvent majorant. -/
theorem abs_scaledResolventSecondDeriv_le {a t : ℝ} (ha : 0 < a) :
    |scaledResolventSecondDeriv a t| ≤ 6 * |1 - a ^ 2| / a ^ 3 := by
  dsimp only [scaledResolventSecondDeriv]
  have hd : 0 < a ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t)
  have hnum : |3 * t ^ 2 - a ^ 2| ≤ 3 * (a ^ 2 + t ^ 2) := by
    rw [abs_le]
    constructor <;> nlinarith only [sq_nonneg a, sq_nonneg t]
  have he :
    |2 * a * (1 - a ^ 2) * (3 * t ^ 2 - a ^ 2) / (a ^ 2 + t ^ 2) ^ 3| =
      2 * a * |1 - a ^ 2| * |3 * t ^ 2 - a ^ 2| / (a ^ 2 + t ^ 2) ^ 3 := by
    rw [abs_div, abs_mul, abs_mul, abs_mul, abs_of_pos ha,
      abs_of_pos (by norm_num only : (0 : ℝ) < 2), abs_of_pos (pow_pos hd 3)]
  rw [he]
  have hn :=
    mul_le_mul_of_nonneg_left hnum
      (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) ha.le) (abs_nonneg (1 - a ^ 2)))
  have hs : a ^ 4 ≤ (a ^ 2 + t ^ 2) ^ 2 := by
    nlinarith only [sq_nonneg t, sq_nonneg a, mul_nonneg (sq_nonneg a) (sq_nonneg t),
      sq_nonneg (t ^ 2)]
  have hc : 6 * a * |1 - a ^ 2| / (a ^ 2 + t ^ 2) ^ 2 ≤ 6 * |1 - a ^ 2| / a ^ 3 := by
    rw [div_le_div_iff₀ (pow_pos hd 2) (pow_pos ha 3)]
    nlinarith only [mul_nonneg
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 6) (abs_nonneg (1 - a ^ 2))) (sub_nonneg.mpr hs)]
  calc
    _ ≤ (2 * a * |1 - a ^ 2| * (3 * (a ^ 2 + t ^ 2))) / (a ^ 2 + t ^ 2) ^ 3 :=
      div_le_div_of_nonneg_right hn (pow_nonneg hd.le 3)
    _ = 6 * a * |1 - a ^ 2| / (a ^ 2 + t ^ 2) ^ 2 := by
      field_simp (discharger := exact hd.ne')
      ring
    _ ≤ _ := hc

end PseudoPrime.Analysis
