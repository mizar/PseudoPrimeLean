/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.IntegerIntervalChecks
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith

/-! # Square-root interval witnesses -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Check nonnegative square-root endpoints using only integer square comparisons.
The scale is positive, and the input lower bound is nonnegative. -/
def integerSqrtCheck (G a b l u : ℤ) : Bool :=
  decide (0 < G ∧ 0 ≤ a ∧ 0 ≤ l ∧ 0 ≤ u ∧ l * l ≤ a * G ∧ b * G ≤ u * u)

/-- Nonnegative real square comparisons imply containment after taking square roots.
Positive scale allows division; monotonicity of squaring gives both endpoints. -/
theorem scaled_sqrt_bounds {G a b l u x : ℝ} (g : 0 < G) (aa : 0 ≤ a) (ll : 0 ≤ l) (uu : 0 ≤ u)
    (l2 : l * l ≤ a * G) (u2 : b * G ≤ u * u) (hx : a / G ≤ x ∧ x ≤ b / G) :
    l / G ≤ Real.sqrt x ∧ Real.sqrt x ≤ u / G := by
  have xl := (div_le_iff₀ g).1 hx.1
  have xu := (le_div_iff₀ g).1 hx.2
  have x0 : 0 ≤ x := (div_nonneg aa g.le).trans hx.1
  constructor
  · apply (Real.le_sqrt (div_nonneg ll g.le) x0).2
    rw [div_pow]
    apply (div_le_iff₀ (pow_pos g 2)).2
    nlinarith only [l2, mul_le_mul_of_nonneg_right xl g.le]
  · apply Real.sqrt_le_iff.mpr
    constructor
    · exact div_nonneg uu g.le
    · rw [div_pow]
      apply (le_div_iff₀ (pow_pos g 2)).2
      nlinarith only [u2, mul_le_mul_of_nonneg_right xu g.le]

/-- Successful integer square-root checking encloses the real square root of
any input in the source interval, independently of endpoint generation. -/
theorem integerSqrtCheck_sound {G a b l u : ℤ} {x : ℝ} (h : integerSqrtCheck G a b l u = true)
    (hx : (a : ℝ) / G ≤ x ∧ x ≤ (b : ℝ) / G) :
    (l : ℝ) / G ≤ Real.sqrt x ∧ Real.sqrt x ≤ (u : ℝ) / G := by
  have hc := of_decide_eq_true h
  have hg : (0 : ℝ) < G := by exact_mod_cast hc.1
  have ha : (0 : ℝ) ≤ a := by exact_mod_cast hc.2.1
  have hl : (0 : ℝ) ≤ l := by exact_mod_cast hc.2.2.1
  have hu : (0 : ℝ) ≤ u := by exact_mod_cast hc.2.2.2.1
  have hl2 : (l : ℝ) * l ≤ (a : ℝ) * G := by exact_mod_cast hc.2.2.2.2.1
  have hu2 : (b : ℝ) * G ≤ (u : ℝ) * u := by exact_mod_cast hc.2.2.2.2.2
  exact scaled_sqrt_bounds hg ha hl hu hl2 hu2 hx

end PseudoPrime.Analysis
