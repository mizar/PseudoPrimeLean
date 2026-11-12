/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalLogCheck
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone

/-! # A Lee–Nosal envelope bound from 16384 onward -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The Lee–Nosal error envelope is at least 365 for every `t ≥ 16384`.
A rational logarithm certificate proves the endpoint bound, and monotonicity extends it. -/
theorem lee_nosal_envelope_ge_365 {t : ℝ} (ht : 16384 ≤ t) :
    (365 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    lee_nosal_envelope_of_log_checks (N := 16384) (lo := 970 / 100) (hi := 971 / 100) (vlo :=
      227 / 100) (vhi := 228 / 100) (c := 365) (j := 14) (k := 4) (n := 32) (m := 32)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (lee_nosal_envelope_mono (x := 16384) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
