/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! # Rational bounds for finite reciprocal sums -/

public section

namespace PseudoPrime.Analysis

/-- Positive rational lower bounds for finitely many real numbers turn a
strict rational upper bound on their paired reciprocal sum into the same
real upper bound. This transfers finite zero-bracket certificates without
exposing their numerical data. -/
theorem reciprocal_sum_lt_of_lower {n : ℕ} (a : Fin n → ℚ) (g : Fin n → ℝ) {B : ℚ}
    (ha : ∀ i, 0 < a i) (hg : ∀ i, (a i : ℝ) ≤ g i) (hc : (∑ i, (2 : ℚ) / a i) < B) :
    (∑ i, (2 : ℝ) / g i) < B := by
  have hs : (∑ i, (2 : ℝ) / g i) ≤ ∑ i, (2 : ℝ) / (a i : ℝ) := by
    apply Finset.sum_le_sum
    intro i hi
    exact div_le_div_of_nonneg_left (by norm_num only) (Rat.cast_pos.mpr (ha i)) (hg i)
  have hc' : (∑ i, (2 : ℝ) / (a i : ℝ)) < (B : ℝ) := by
    have h : ((∑ i, (2 : ℚ) / a i : ℚ) : ℝ) < (B : ℝ) := by exact_mod_cast hc
    simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_ofNat] using h
  exact hs.trans_lt hc'

end PseudoPrime.Analysis
