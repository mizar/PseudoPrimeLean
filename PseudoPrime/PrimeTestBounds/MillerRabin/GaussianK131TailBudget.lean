/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131EndpointTails
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131EndpointBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Log

/-! # Rational endpoint budget for the raw K131 interval -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Lower budget from a radius upper bound, a doubled-log interval and a
lower bound on the logarithm of the doubled log at the right endpoint. -/
def k131TailBudget (u b c cost : ℚ) : ℚ :=
  12020425 / 1000000 - 228016 / 1000000000 * u - cost - 151 / 25000000 + 3 / 1000 -
    (14411 / 1000000) * (b * (b - c))

/-- The tail budget using the unshifted estimate of the main term cost. -/
def k131RawTailBudget (u a b r c : ℚ) : ℚ :=
  k131TailBudget u b c (k131RawTailCap a b r)

/-- The tail budget using main term coefficients translated to the left endpoint. -/
def k131ShiftedTailBudget (u a b r c : ℚ) : ℚ :=
  k131TailBudget u b c (k131ShiftedTailCap a b r)

private theorem raw_principal_error_lower {u b c : ℝ} (ha : 0 < 2 * Real.log u)
    (hlog : 2 * Real.log u ≤ b) (hc : c ≤ Real.log (2 * Real.log u)) :
    -(14411 / 1000000 : ℝ) * (b * (b - c)) ≤ k131PrincipalError gaussianK131RhCoeff u := by
  let v := 2 * Real.log u
  have hv : 0 ≤ v - Real.log v := by linarith only [Real.log_le_sub_one_of_pos ha]
  have hm := mul_le_mul hlog (sub_le_sub hlog hc) hv (ha.le.trans hlog)
  have hh :=
    mul_le_mul principal_coeff_upper hm (mul_nonneg ha.le hv)
      (by norm_num only : (0 : ℝ) ≤ 14411 / 1000000)
  unfold k131PrincipalError
  linarith only [hh]

/-- A rational strict budget is sufficient for the real endpoint
comparison in the K131 witness theorem. -/
theorem k131_raw_tail_budget_sound {u b c cost : ℚ} (ha : 0 < 2 * Real.log (u : ℝ))
    (hlog : 2 * Real.log (u : ℝ) ≤ (b : ℝ)) (hc : (c : ℝ) ≤ Real.log (2 * Real.log (u : ℝ)))
    (hgap : 27 / 10000 < k131TailBudget u b c cost) :
    27 / 10000 <
      12020425 / 1000000 - 228016 / 1000000000 * (u : ℝ) +
        (-(cost : ℝ) - 151 / 25000000 + 3 / 1000) +
        k131PrincipalError gaussianK131RhCoeff (u : ℝ) := by
  have h := (Rat.cast_lt (K := ℝ)).mpr hgap
  simp only [k131TailBudget, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
    Rat.cast_ofNat] at h
  linarith only [h, raw_principal_error_lower ha hlog hc]

/-- The rational certificate for the interval from log 42409.99 to 42410.
The two radius endpoints are the images under the K131 tail scale. -/
theorem k131_raw_last_box :
    let l : ℚ := 1101568457163 / 50000000
    let u : ℚ := 1101568717 / 50000
    let a : ℚ := 2000044517 / 100000000
    let b : ℚ := 2000044565 / 100000000
    let r : ℚ := 349044 / 100000
    let c : ℚ := 29957 / 10000
    r ^ 8 ≤ l ∧
      (a : ℝ) ≤ 2 * Real.log (l : ℝ) ∧
      2 * Real.log (u : ℝ) ≤ (b : ℝ) ∧ (c : ℝ) ≤ Real.log (2 * Real.log (u : ℝ)) := by
  intro l u a b r c
  refine ⟨by decide +kernel, ?_, ?_, ?_⟩
  · dsimp only [a, l]
    dyadic_interval [prec := 70]
  · dsimp only [b, u]
    dyadic_interval [prec := 70]
  · dsimp only [c, u]
    dyadic_interval [prec := 70]

end PseudoPrime.PrimeTestBounds.MillerRabin
