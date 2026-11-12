/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalInterval
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalInterval40512

/-! # Combined finite Lee–Nosal error bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The unconditional Lee–Nosal psi error bound holds on `[39760, 40512]`.
The proof combines two independently certified intervals at 40000. -/
theorem psi_lee_nosal_39760_40512 {x : ℝ} (ha : 39760 ≤ x) (hb : x ≤ 40512) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h : x ≤ 40000
  · exact psi_lee_nosal_39760_40000 ha h
  · exact psi_lee_nosal_40000_40512 (le_of_not_ge h) hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
