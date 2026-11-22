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
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiChecks.LeeNosal108To113

/-! # Lee–Nosal psi certificate for the interval from 113 to 121 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiChecks

private theorem psi_113_bounds : (117 : ℝ) ≤ Chebyshev.psi 113 ∧ Chebyshev.psi 113 ≤ (118 : ℝ) := by
  have hl : 2 ^ 169 ≤ Nat.lcmUpto 113 := by decide +kernel
  have hu : Nat.lcmUpto 113 ≤ 2 ^ (169 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

private theorem psi_120_eq_113 : Chebyshev.psi 120 = Chebyshev.psi 113 := by
  exact Arithmetic.psi_eq_of_no_prime_power (a := 113) (b := 120) (by decide) (by decide +kernel)

private theorem envelope_113_121 {t : ℝ} (ht : 101 ≤ t) :
    (11 / 2 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  exact
    lee_nosal_envelope_101_lower.trans
      (RiemannZeta.lee_nosal_envelope_mono (x := 101) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- The Lee–Nosal psi error estimate holds unconditionally on `[113, 121)`.
Both endpoint bounds use a single checked prefix, which remains constant through 120. -/
theorem bound_113_121 {x : ℝ} (ha : 113 ≤ x) (hb : x < 121) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  apply
    RiemannZeta.lee_nosal_cell_check_sound ⟨113, 121, 117000, 118000, 5500, 5500⟩ Chebyshev.psi_mono
      Chebyshev.psi_eq_psi_coe_floor (by decide +kernel)
  · norm_num only
    exact psi_113_bounds.1
  · norm_num only
    rw [psi_120_eq_113]
    exact psi_113_bounds.2
  · norm_num only
    exact envelope_113_121 (by norm_num only)
  · norm_num only
    exact envelope_113_121 (by norm_num only)
  · exact ha
  · exact hb

/-- Adjacent certified cells give the Lee–Nosal psi error bound on `[101, 121)`. -/
theorem bound_101_121 {x : ℝ} (ha : 101 ≤ x) (hb : x < 121) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h : x < 113
  · exact bound_101_113 ha h
  · exact bound_113_121 (le_of_not_gt h) hb

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiChecks
