/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Normed

/-! # Exponential majorants and prime-power masses -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The exponential at height (k+1)/x is a geometric power of exp(-1/x).
The exponential multiple formula identifies a summable majorant at positive scale. -/
theorem exp_neg_div_nat_eq_power (x : ℝ) (k : ℕ) :
    Real.exp (-((k + 1 : ℕ) : ℝ) / x) = Real.exp (-1 / x) ^ (k + 1) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- Input: a positive scale and heights above (k+1)/x. Claim: the exponential
series is summable. Compare with a geometric series. Role: separate signed
local corrections into convergent endpoint series. -/
theorem summable_exp_neg_of_linear_lower {x : ℝ} (hx : 0 < x) (u : ℕ → ℝ)
    (hu : ∀ k, ((k + 1 : ℕ) : ℝ) / x ≤ u k) : Summable (fun k ↦ Real.exp (-(u k))) := by
  have hr : ‖Real.exp (-1 / x)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (by norm_num only) hx
  have hs := (summable_geometric_of_norm_lt_one hr).mul_right (Real.exp (-1 / x))
  have hg : Summable (fun k : ℕ ↦ Real.exp (-1 / x) ^ (k + 1)) := by simpa only [pow_succ] using hs
  apply hg.of_nonneg_of_le
  · intro k
    exact (Real.exp_pos _).le
  · intro k
    rw [← exp_neg_div_nat_eq_power]
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    exact neg_le_neg (hu k)

/-- Input: natural base p and scale x. Definition: the full exponential sum
over positive powers of p. Role: retain the negative part of a ramified local
correction in endpoint transport. Summability requires p>1 and x>0. -/
noncomputable def gammaPrimeExponentialMass (p : ℕ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, Real.exp (-((p : ℝ) ^ (k + 1) / x))

end PseudoPrime.Analysis
