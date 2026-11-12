/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalLogCheck
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone

/-! # An envelope bound from the dyadic endpoint 32768 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The Lee–Nosal envelope at 32768 is at least 600. Two checked rational logarithm
intervals and a squared rational comparison certify the bound. -/
private theorem lee_nosal_envelope_32768 :
    (600 : ℝ) ≤
      Real.sqrt 32768 *
        (Real.log 32768 * (Real.log 32768 - Real.log (Real.log 32768)) / (8 * Real.pi)) := by
  have h :=
    lee_nosal_envelope_of_log_checks (N := 32768) (lo := 1039 / 100) (hi := 52 / 5) (vlo := 23 / 10)
      (vhi := 47 / 20) (c := 600) (j := 15) (k := 4) (n := 32) (m := 32) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by decide +kernel)
      (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_ofNat] at h
  exact h

/-- The Lee–Nosal envelope is at least 600 for every real `x ≥ 32768`.
Monotonicity transfers the certified dyadic endpoint bound. -/
theorem lee_nosal_envelope_ge_600_of_32768 {x : ℝ} (hx : 32768 ≤ x) :
    (600 : ℝ) ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_envelope_32768.trans
      (lee_nosal_envelope_mono (x := 32768) (y := x)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) hx)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
