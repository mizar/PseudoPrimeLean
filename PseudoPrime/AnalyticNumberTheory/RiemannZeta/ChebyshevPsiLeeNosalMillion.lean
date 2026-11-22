/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.PsiEnvelopeLow
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiSqrtLeeNosal1423

/-! # Lee–Nosal psi bound through one million -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The unconditional Lee–Nosal psi bound holds on `[101, 1000000]`.
The joint low cells certify the envelope directly. From 1423 the four-fifths bound suffices. -/
theorem psi_lee_nosal_101_million {x : ℝ} (ha : 101 ≤ x) (hb : x ≤ 1000000) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h : x < 1423
  · exact Cert.Chebyshev.Joint.psi_envelope_low ha h
  · exact psi_lee_nosal_1423_million (le_of_not_gt h) hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
