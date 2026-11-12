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
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal35584Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal35840Upper

/-! # A finite Lee–Nosal psi error bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The Lee–Nosal psi error bound holds unconditionally on `[35584, 35840]`.
Certified endpoint bounds supply the interval criterion. -/
theorem psi_lee_nosal_35584_35840 {x : ℝ} (ha : 35584 ≤ x) (hb : x ≤ 35840) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  apply psi_lee_nosal_cell (a := 35584) (b := 35840) (c := 600) _ ha hb _ _ _
  · exact Real.exp_one_lt_three.le.trans (by norm_num only)
  · linarith only [psi_35584_lower]
  · linarith only [psi_35840_upper]
  · exact lee_nosal_envelope_ge_600_of_32768 (by norm_num only)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
