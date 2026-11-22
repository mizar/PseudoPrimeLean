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
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalChecker
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiChecks.LeeNosal101Sharp
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiChecks.LeeNosal101To108

/-! # Lee–Nosal psi certificates for the interval from 108 to 113 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiChecks

private theorem psi_108_lower : (107 : ℝ) ≤ Chebyshev.psi 108 := by
  have hl : 2 ^ 155 ≤ Nat.lcmUpto 108 := by decide +kernel
  have hu : Nat.lcmUpto 108 ≤ 2 ^ (155 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  linarith only [h.1, Real.log_two_gt_d9]

private theorem psi_111_bounds : (112 : ℝ) ≤ Chebyshev.psi 111 ∧ Chebyshev.psi 111 ≤ (113 : ℝ) := by
  have hl : 2 ^ 162 ≤ Nat.lcmUpto 111 := by decide +kernel
  have hu : Nat.lcmUpto 111 ≤ 2 ^ (162 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

private theorem envelope_108_112 {t : ℝ} (ht : 101 ≤ t) :
    (11 / 2 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  exact
    lee_nosal_envelope_101_lower.trans
      (RiemannZeta.lee_nosal_envelope_mono (x := 101) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- The Lee–Nosal psi error estimate holds unconditionally on `[108, 112)`.
The one-cell checker uses the independently certified psi endpoint bounds and the
monotone envelope lower bound. -/
theorem bound_108_112 {x : ℝ} (ha : 108 ≤ x) (hb : x < 112) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  apply
    RiemannZeta.lee_nosal_cell_check_sound ⟨108, 112, 107000, 113000, 5500, 5500⟩ Chebyshev.psi_mono
      Chebyshev.psi_eq_psi_coe_floor (by decide +kernel)
  · norm_num only
    exact psi_108_lower
  · norm_num only
    exact psi_111_bounds.2
  · norm_num only
    exact envelope_108_112 (by norm_num only)
  · norm_num only
    exact envelope_108_112 (by norm_num only)
  · exact ha
  · exact hb

/-- The adjacent low-range certificates give the Lee–Nosal psi error estimate
on the entire half-open interval `[101, 112)`. -/
theorem bound_101_112 {x : ℝ} (ha : 101 ≤ x) (hb : x < 112) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h : x < 108
  · exact bound_101_108 ha h
  · exact bound_108_112 (le_of_not_gt h) hb

private theorem psi_112_bounds : (112 : ℝ) ≤ Chebyshev.psi 112 ∧ Chebyshev.psi 112 ≤ (113 : ℝ) := by
  have heq : Chebyshev.psi 112 = Chebyshev.psi 111 :=
    Arithmetic.psi_succ_of_not_prime_power (n := 111) (by decide +kernel)
  rw [heq]
  exact psi_111_bounds

/-- The Lee–Nosal psi error bound holds unconditionally on `[112, 113)`.
The cell uses the lower and upper certificates for the common integer prefix. -/
theorem bound_112_113 {x : ℝ} (ha : 112 ≤ x) (hb : x < 113) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  apply
    RiemannZeta.lee_nosal_cell_check_sound ⟨112, 113, 112000, 113000, 5500, 5500⟩ Chebyshev.psi_mono
      Chebyshev.psi_eq_psi_coe_floor (by decide +kernel)
  · norm_num only
    exact psi_112_bounds.1
  · norm_num only
    exact psi_112_bounds.2
  · norm_num only
    exact envelope_108_112 (by norm_num only)
  · norm_num only
    exact envelope_108_112 (by norm_num only)
  · exact ha
  · exact hb

/-- The adjacent interval certificates establish the Lee–Nosal psi estimate
throughout `[101, 113)`. -/
theorem bound_101_113 {x : ℝ} (ha : 101 ≤ x) (hb : x < 113) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h : x < 112
  · exact bound_101_112 ha h
  · exact bound_112_113 (le_of_not_gt h) hb

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiChecks
