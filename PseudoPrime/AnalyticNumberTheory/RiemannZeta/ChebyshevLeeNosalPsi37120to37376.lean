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
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal37120Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal37376Upper

/-! # A finite Lee–Nosal psi error bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The Lee–Nosal psi error bound holds unconditionally on `[37120, 37376]`.
Certified endpoint bounds supply the interval criterion. -/
theorem psi_lee_nosal_37120_37376 {x : ℝ} (ha : 37120 ≤ x) (hb : x ≤ 37376) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  apply psi_lee_nosal_cell (a := 37120) (b := 37376) (c := 600) _ ha hb _ _ _
  · exact Real.exp_one_lt_three.le.trans (by norm_num only)
  · linarith only [psi_37120_lower]
  · linarith only [psi_37376_upper]
  · exact lee_nosal_envelope_ge_600_of_32768 (by norm_num only)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
