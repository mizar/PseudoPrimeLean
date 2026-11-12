/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLcmBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevIntervalPrefix
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSmallDefect
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalChecker
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalLogCheck
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone

/-! # A Lee–Nosal theta certificate at the low endpoint -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

private theorem psi_2657_bounds :
    (263187 / 100 : ℝ) ≤ Chebyshev.psi 2657 ∧ Chebyshev.psi 2657 ≤ (2633 : ℝ) := by
  have hl : 2 ^ 3797 ≤ Nat.lcmUpto 2657 := by decide +kernel
  have hu : Nat.lcmUpto 2657 ≤ 2 ^ (3797 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

private theorem theta_2657_bounds :
    (25659 / 10 : ℝ) ≤ Chebyshev.theta 2657 ∧ Chebyshev.theta 2657 ≤ (2633 : ℝ) := by
  have h := Arithmetic.psi_sub_theta_le_6591 (x := 2657) (by norm_num only) (by norm_num only)
  have htheta := Chebyshev.theta_le_psi 2657
  constructor <;> linarith only [h, htheta, psi_2657_bounds.1, psi_2657_bounds.2]

private theorem envelope_2657 {t : ℝ} (ht : 2657 ≤ t) :
    (94 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    lee_nosal_envelope_of_log_checks (N := 2657) (lo := 7884 / 1000) (hi := 7885 / 1000) (vlo :=
      2064 / 1000) (vhi := 2066 / 1000) (c := 94) (j := 12) (k := 4) (n := 32) (m := 32)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (lee_nosal_envelope_mono (x := 2657) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- The Lee–Nosal theta estimate holds on `[2657, 2659)`. It uses the
Costa-Pereira three-root bound and kernel-checked psi endpoint certificates. -/
theorem theta_lee_nosal_2657_2659 {x : ℝ} (ha : 2657 ≤ x) (hb : x < 2659) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  apply
    lee_nosal_cell_check_sound ⟨2657, 2659, 2565900, 2633000, 94000, 94000⟩ Chebyshev.theta_mono
      Chebyshev.theta_eq_theta_coe_floor (by decide +kernel)
  · norm_num only
    exact theta_2657_bounds.1
  · norm_num only
    have he : Chebyshev.theta 2658 = Chebyshev.theta 2657 := by
      exact Arithmetic.theta_succ_of_not_prime (n := 2657) (by decide +kernel)
    rw [he]
    exact theta_2657_bounds.2
  · norm_num only
    exact envelope_2657 (by norm_num only)
  · norm_num only
    exact envelope_2657 (by norm_num only)
  · exact ha
  · exact hb

private theorem psi_2659_lower : (26395 / 10 : ℝ) ≤ Chebyshev.psi 2659 := by
  have hl : 2 ^ 3808 ≤ Nat.lcmUpto 2659 := by decide +kernel
  have hu : Nat.lcmUpto 2659 ≤ 2 ^ (3808 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  linarith only [h.1, Real.log_two_gt_d9]

private theorem psi_2666_upper : Chebyshev.psi 2666 ≤ (2648 : ℝ) := by
  have hl : 2 ^ 3819 ≤ Nat.lcmUpto 2666 := by decide +kernel
  have hu : Nat.lcmUpto 2666 ≤ 2 ^ (3819 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  linarith only [h.2, Real.log_two_lt_d9]

/-- The Lee–Nosal theta estimate holds on `[2659, 2667)` using the shared
higher-prime-power bound and checked psi prefixes at both endpoints. -/
theorem theta_lee_nosal_2659_2667 {x : ℝ} (ha : 2659 ≤ x) (hb : x < 2667) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  apply
    lee_nosal_cell_check_sound ⟨2659, 2667, 2573000, 2648000, 94000, 94000⟩ Chebyshev.theta_mono
      Chebyshev.theta_eq_theta_coe_floor (by decide +kernel)
  · norm_num only
    have hd := Arithmetic.psi_sub_theta_le_6591 (x := 2659) (by norm_num only) (by norm_num only)
    linarith only [hd, psi_2659_lower]
  · norm_num only
    have ht := Chebyshev.theta_le_psi 2666
    linarith only [ht, psi_2666_upper]
  · norm_num only
    exact envelope_2657 (by norm_num only)
  · norm_num only
    exact envelope_2657 (by norm_num only)
  · exact ha
  · exact hb

/-- The adjacent theta cells yield the Lee–Nosal estimate on `[2657, 2667)`. -/
theorem theta_lee_nosal_2657_2667 {x : ℝ} (ha : 2657 ≤ x) (hb : x < 2667) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h : x < 2659
  · exact theta_lee_nosal_2657_2659 ha h
  · exact theta_lee_nosal_2659_2667 (le_of_not_gt h) hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
