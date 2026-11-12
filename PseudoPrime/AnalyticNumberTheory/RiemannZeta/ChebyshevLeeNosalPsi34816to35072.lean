/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalCells
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalEnvelope32768
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal34816Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal35072Upper

/-! # A finite Lee–Nosal psi error bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The Lee–Nosal psi error bound holds unconditionally on `[34816, 35072]`.
Certified endpoint bounds supply the interval criterion. -/
theorem psi_lee_nosal_34816_35072 {x : ℝ} (ha : 34816 ≤ x) (hb : x ≤ 35072) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  apply psi_lee_nosal_cell (a := 34816) (b := 35072) (c := 600) _ ha hb _ _ _
  · exact Real.exp_one_lt_three.le.trans (by norm_num only)
  · linarith only [psi_34816_lower]
  · linarith only [psi_35072_upper]
  · exact lee_nosal_envelope_ge_600_of_32768 (by norm_num only)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
