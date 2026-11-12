/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.PreciseLogTaylorBounds
public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Real.Pi.Bounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalCertificate

/-! # Rational logarithm checks for Lee–Nosal envelopes -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Two certified logarithm intervals and a rational square comparison prove a
Lee–Nosal envelope lower bound at a positive rational point. The fixed rational
upper bound for pi is supplied by mathlib. -/
theorem lee_nosal_envelope_of_log_checks {N lo hi vlo vhi c : ℚ} {j k n m : ℕ} (hN : 0 < N)
    (hc : 0 ≤ c) (hlo : 0 < lo) (hvl : vhi ≤ lo)
    (hlog : Analysis.preciseLogCheck N j n lo hi = true)
    (hloglog : Analysis.preciseLogCheck hi k m vlo vhi = true)
    (hsq : (8 * (3141593 / 1000000 : ℚ) * c) ^ 2 ≤ N * lo ^ 2 * (lo - vhi) ^ 2) :
    (c : ℝ) ≤
      Real.sqrt (N : ℝ) *
        (Real.log (N : ℝ) * (Real.log (N : ℝ) - Real.log (Real.log (N : ℝ))) / (8 * Real.pi)) := by
  have h1 := Analysis.preciseLogCheck_sound hlog
  have h2 := Analysis.preciseLogCheck_sound hloglog
  apply
    lee_nosal_envelope_of_sq (l := (lo : ℝ)) (u := (hi : ℝ)) (v := (vhi : ℝ)) (P :=
      (3141593 / 1000000 : ℝ)) _ _ _ _ h1.1 h1.2 h2.2 _ _
  · exact_mod_cast hN
  · exact_mod_cast hc
  · exact_mod_cast hlo
  · exact_mod_cast hvl
  · convert Real.pi_lt_d6.le using 1; norm_num only
  · have hs :
      (((8 * (3141593 / 1000000 : ℚ) * c) ^ 2 : ℚ) : ℝ) ≤
        ((N * lo ^ 2 * (lo - vhi) ^ 2 : ℚ) : ℝ) := by
      exact_mod_cast hsq
    norm_num only [Rat.cast_mul, Rat.cast_pow, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat] at hs
    nlinarith only [hs]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
