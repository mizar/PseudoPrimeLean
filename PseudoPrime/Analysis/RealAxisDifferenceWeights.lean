/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith

/-! # Real-axis secant gains and positive signed Poisson differences -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For a positive real base and arbitrary real exponents, the logarithm-weighted
power at the right endpoint is bounded by the difference of inverse powers.
Apply log z<=z-1 to z=a^(tau-sigma) and multiply by the positive denominator.
This is the secant lower bound used before differentiating any Euler series. -/
theorem log_weight_le_rpow_difference {a σ τ : ℝ} (ha : 0 < a) :
    (τ - σ) * Real.log a / a ^ τ ≤ 1 / a ^ σ - 1 / a ^ τ := by
  have ht := Real.rpow_pos_of_pos ha τ
  have hl := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ha (τ - σ))
  rw [Real.log_rpow ha] at hl
  have he : (1 / a ^ σ - 1 / a ^ τ) * a ^ τ = a ^ (τ - σ) - 1 := by
    rw [Real.rpow_sub ha, sub_mul, div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div, one_mul,
      div_self ht.ne']
  apply (div_le_iff₀ ht).mpr
  rw [he]
  exact hl

/-- The signed difference of two centered Poisson profiles, with real scales a,b,
coefficients u,v and height t. Operations are totalized. Positivity is proved under
explicit scale and coefficient constraints; later theorems sum this rational
weight against actual completed-L-function zero multiplicities. -/
noncomputable def poissonDifferenceWeight (a b u v t : ℝ) : ℝ :=
  u * a / (a ^ 2 + t ^ 2) - v * b / (b ^ 2 + t ^ 2)

/-- For 0<a<=b, u>=0 and v*b<=u*a, the signed two-profile weight is nonnegative
at every real height. Multiply positive denominators and split the numerator into
two nonnegative products. This supplies a finite-scale rational-kernel sign test. -/
theorem poissonDifferenceWeight_nonneg {a b u v t : ℝ} (ha : 0 < a) (hab : a ≤ b) (hu : 0 ≤ u)
    (hc : v * b ≤ u * a) : 0 ≤ poissonDifferenceWeight a b u v t := by
  have hb : 0 < b := ha.trans_le hab
  have hdA : 0 < a ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t)
  have hdB : 0 < b ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hb) (sq_nonneg t)
  have hs : 0 ≤ b ^ 2 - a ^ 2 := by nlinarith only [ha, hab]
  have h := add_nonneg (mul_nonneg (sub_nonneg.mpr hc) hdA.le) (mul_nonneg (mul_nonneg hu ha.le) hs)
  unfold poissonDifferenceWeight
  apply sub_nonneg.mpr
  apply (div_le_div_iff₀ hdB hdA).mpr
  nlinarith only [h]

end PseudoPrime.Analysis
