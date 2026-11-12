/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalLogCheck
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone

/-! # A Lee–Nosal envelope bound from 10000 onward -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The Lee–Nosal error envelope is at least 255 for every `t ≥ 10000`.
A rational logarithm certificate proves the endpoint bound, and monotonicity extends it. -/
theorem lee_nosal_envelope_ge_255 {t : ℝ} (ht : 10000 ≤ t) :
    (255 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    lee_nosal_envelope_of_log_checks (N := 10000) (lo := 921 / 100) (hi := 922 / 100) (vlo :=
      222 / 100) (vhi := 223 / 100) (c := 255) (j := 13) (k := 4) (n := 32) (m := 32)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (lee_nosal_envelope_mono (x := 10000) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
