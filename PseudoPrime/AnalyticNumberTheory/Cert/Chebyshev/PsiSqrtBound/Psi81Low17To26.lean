/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import all PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt81Checker
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLcmBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevIntervalPrefix
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Coefficient-81/100 psi bound on the initial range -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound

/-- A kernel-checked LCM comparison and a lower bound for `log 2` bound `psi 17` below. -/
private theorem psi17_lower : (15942 : ℝ) / 1000 ≤ Chebyshev.psi 17 := by
  have hl : 2 ^ 23 ≤ Nat.lcmUpto 17 := by decide
  have hu : Nat.lcmUpto 17 ≤ 2 ^ (23 + 1) := by decide
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  linarith only [h.1, Real.log_two_gt_d9]

/-- A kernel-checked LCM comparison and an upper bound for `log 2` bound `psi 18` above. -/
private theorem psi18_upper : Chebyshev.psi 18 ≤ (16636 : ℝ) / 1000 := by
  have hl : 2 ^ 23 ≤ Nat.lcmUpto 18 := by decide
  have hu : Nat.lcmUpto 18 ≤ 2 ^ (23 + 1) := by decide
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  linarith only [h.2, Real.log_two_lt_d9]

/-- For every real `x` in `[17, 19)`, the normalized psi error is at most `81 / 100`.
The integer checker verifies the crossing conditions, and internal LCM bounds supply the
endpoint inequalities; no external table is required. -/
theorem psi81_on_17_19 {x : ℝ} (hx : 17 ≤ x) (hx' : x < 19) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (81 / 100 : ℝ) := by
  have hc : Arithmetic.psi81CellCheck ⟨17, 19, 15942, 16636, 3339, 3530⟩ = true := by decide
  have h :=
    Arithmetic.psi81_cell_sound ⟨17, 19, 15942, 16636, 3339, 3530⟩ hc psi17_lower psi18_upper hx hx'
  have hx0 : 0 < x := by linarith only [hx]
  exact (div_le_iff₀ (Real.sqrt_pos.2 hx0)).2 (by simpa only [mul_comm] using h)

/-- A kernel-checked comparison for the sixteenth power of the LCM gives bounds for `psi 19`.
The additional precision is needed by the coefficient-`81 / 100` crossing test. -/
private theorem psi19_bounds :
    (19234 : ℝ) / 1000 ≤ Chebyshev.psi 19 ∧ Chebyshev.psi 19 ≤ (19279 : ℝ) / 1000 := by
  have hl : 2 ^ 444 ≤ (Nat.lcmUpto 19) ^ 16 := by decide +kernel
  have hu : (Nat.lcmUpto 19) ^ 16 ≤ 2 ^ (444 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two_scaled hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor
  · linarith only [h.1, Real.log_two_gt_d9]
  · linarith only [h.2, Real.log_two_lt_d9]

/-- The psi prefix does not change from 19 through 22 because the interval has no prime power. -/
private theorem psi22_eq_psi19 : Chebyshev.psi (22 : ℕ) = Chebyshev.psi (19 : ℕ) := by
  apply Arithmetic.psi_eq_of_no_prime_power (by decide)
  decide +kernel

/-- For every real `x` in `[19, 23)`, the normalized psi error is at most `81 / 100`.
The proof combines the integer cell checker with internal LCM and prime-power calculations. -/
theorem psi81_on_19_23 {x : ℝ} (hx : 19 ≤ x) (hx' : x < 23) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (81 / 100 : ℝ) := by
  have hc : Arithmetic.psi81CellCheck ⟨19, 23, 19234, 19279, 3530, 3884⟩ = true := by decide
  have hu : Chebyshev.psi 22 ≤ (19279 : ℝ) / 1000 := by
    simpa only [Nat.cast_ofNat] using (psi22_eq_psi19 ▸ psi19_bounds.2)
  have h :=
    Arithmetic.psi81_cell_sound ⟨19, 23, 19234, 19279, 3530, 3884⟩ hc psi19_bounds.1 hu hx hx'
  have hx0 : 0 < x := by linarith only [hx]
  exact (div_le_iff₀ (Real.sqrt_pos.2 hx0)).2 (by simpa only [mul_comm] using h)

/-- Integer LCM comparisons bound the psi values at 23 and 25. -/
private theorem psi23_bounds :
    (22397 : ℝ) / 1000 ≤ Chebyshev.psi 23 ∧ Chebyshev.psi 23 ≤ (22441 : ℝ) / 1000 := by
  have hl : 2 ^ 517 ≤ (Nat.lcmUpto 23) ^ 16 := by decide +kernel
  have hu : (Nat.lcmUpto 23) ^ 16 ≤ 2 ^ (517 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two_scaled hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor
  · linarith only [h.1, Real.log_two_gt_d9]
  · linarith only [h.2, Real.log_two_lt_d9]

/-- An integer LCM comparison bounds the psi value at 25. -/
private theorem psi25_bounds :
    (24000 : ℝ) / 1000 ≤ Chebyshev.psi 25 ∧ Chebyshev.psi 25 ≤ (24044 : ℝ) / 1000 := by
  have hl : 2 ^ 554 ≤ (Nat.lcmUpto 25) ^ 16 := by decide +kernel
  have hu : (Nat.lcmUpto 25) ^ 16 ≤ 2 ^ (554 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two_scaled hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor
  · linarith only [h.1, Real.log_two_gt_d9]
  · linarith only [h.2, Real.log_two_lt_d9]

/-- The integer checker and LCM endpoint bounds establish the bound on `[23, 26)`. -/
theorem psi81_on_23_26 {x : ℝ} (hx : 23 ≤ x) (hx' : x < 26) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (81 / 100 : ℝ) := by
  have hc : Arithmetic.psi81CellCheck ⟨23, 26, 22397, 24044, 3884, 4130⟩ = true := by decide
  have h :=
    Arithmetic.psi81_cell_sound ⟨23, 26, 22397, 24044, 3884, 4130⟩ hc psi23_bounds.1 psi25_bounds.2
      hx hx'
  have hx0 : 0 < x := by linarith only [hx]
  exact (div_le_iff₀ (Real.sqrt_pos.2 hx0)).2 (by simpa only [mul_comm] using h)

/-- For every real `x` in `[17, 23)`, the normalized psi error is at most `81 / 100`.
The two independent endpoint certificates cover the half-open interval. -/
theorem psi81_on_17_23 {x : ℝ} (hx : 17 ≤ x) (hx' : x < 23) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (81 / 100 : ℝ) := by
  by_cases h : x < 19
  · exact psi81_on_17_19 hx h
  · exact psi81_on_19_23 (le_of_not_gt h) hx'

/-- For every real `x` in `[17, 26)`, the normalized psi error is at most `81 / 100`.
Three integer cell checks and internally verified LCM bounds cover this range. -/
theorem psi81_on_17_26 {x : ℝ} (hx : 17 ≤ x) (hx' : x < 26) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (81 / 100 : ℝ) := by
  by_cases h : x < 23
  · exact psi81_on_17_23 hx h
  · exact psi81_on_23_26 (le_of_not_gt h) hx'

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound
