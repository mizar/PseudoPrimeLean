/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Small Bernstein certificates for quartic positivity on a real interval -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Quartic in Bernstein form with real coefficients and interval coordinate t.
The formula is c0(1-t)^4+4c1*t(1-t)^3+6c2*t²(1-t)²+4c3*t³(1-t)+c4*t⁴.
No domain is built into the definition. Later positivity results use 0<=t<=1.
This keeps interval certificates to five scalar coefficients. -/
noncomputable def bernsteinQuartic (c₀ c₁ c₂ c₃ c₄ t : ℝ) : ℝ :=
  c₀ * (1 - t) ^ 4 + 4 * c₁ * t * (1 - t) ^ 3 + 6 * c₂ * t ^ 2 * (1 - t) ^ 2 +
    4 * c₃ * t ^ 3 * (1 - t) +
    c₄ * t ^ 4

/-- On 0<=t<=1, positive endpoint coefficients and nonnegative interior
coefficients make the quartic strictly positive. At t=0 use c0; otherwise
the final term is positive and all other terms are nonnegative.
This supplies a kernel-checkable real-interval certificate without subdivision. -/
theorem bernsteinQuartic_pos {c₀ c₁ c₂ c₃ c₄ t : ℝ} (h₀ : 0 < c₀) (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂)
    (h₃ : 0 ≤ c₃) (h₄ : 0 < c₄) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    0 < bernsteinQuartic c₀ c₁ c₂ c₃ c₄ t := by
  have hu : 0 ≤ 1 - t := sub_nonneg.mpr ht₁
  by_cases hz : t = 0
  · subst t
    dsimp only [bernsteinQuartic]
    convert h₀ using 1
    ring
  · have hp : 0 < t := lt_of_le_of_ne ht₀ (Ne.symm hz)
    have hlast := mul_pos h₄ (pow_pos hp 4)
    have ha := mul_nonneg h₀.le (pow_nonneg hu 4)
    have hb :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) h₁) ht₀) (pow_nonneg hu 3)
    have hc :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 6) h₂) (sq_nonneg t))
        (sq_nonneg (1 - t))
    have hd :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) h₃) (pow_nonneg ht₀ 3)) hu
    dsimp only [bernsteinQuartic]
    linarith only [ha, hb, hc, hd, hlast]

end PseudoPrime.Analysis
