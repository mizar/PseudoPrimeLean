/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalLogCheck

/-! # Sharp endpoint estimates at 101 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A kernel-checked lower bound for the least common multiple through 101 gives
`197 / 2 ≤ psi 101`. Powers of 2 and 3 provide a finer estimate than powers of 2 alone. -/
theorem psi_101_lower : (197 / 2 : ℝ) ≤ Chebyshev.psi 101 := by
  have hc : 2 ^ 139 * 3 ^ 2 ≤ Nat.lcmUpto 101 := by decide +kernel
  change (197 / 2 : ℝ) ≤ Chebyshev.psi (↑(101 : ℕ) : ℝ)
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have hp2 : (0 : ℝ) < (2 : ℝ) ^ 139 := pow_pos (by norm_num only) _
  have hp3 : (0 : ℝ) < (3 : ℝ) ^ 2 := pow_pos (by norm_num only) _
  have hc' : (2 : ℝ) ^ 139 * (3 : ℝ) ^ 2 ≤ (Nat.lcmUpto 101 : ℝ) := by exact_mod_cast hc
  have h := Real.log_le_log (mul_pos hp2 hp3) hc'
  rw [Real.log_mul hp2.ne' hp3.ne', Real.log_pow, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_gt_d9, Real.log_three_gt_d9]

/-- Checked rational logarithm intervals and a squared rational comparison show that
the Lee–Nosal envelope at 101 is at least `11 / 2`. -/
theorem lee_nosal_envelope_101_lower :
    (11 / 2 : ℝ) ≤
      Real.sqrt 101 *
        (Real.log 101 * (Real.log 101 - Real.log (Real.log 101)) / (8 * Real.pi)) := by
  have h :=
    lee_nosal_envelope_of_log_checks (N := 101) (lo := 23 / 5) (hi := 47 / 10) (vlo := 3 / 2)
      (vhi := 8 / 5) (c := 11 / 2) (j := 7) (k := 3) (n := 32) (m := 32) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by decide +kernel)
      (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
