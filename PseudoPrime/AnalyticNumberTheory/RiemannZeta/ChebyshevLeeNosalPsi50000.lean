/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalPsi22016
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal22016to25757
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal25757to29587
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal29587to32768
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalPsi32768to50000

/-! # Cumulative Lee–Nosal psi bound through 50000 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The certified adjacent intervals give the Lee–Nosal psi estimate on `[101, 50000]`. -/
theorem psi_lee_nosal_101_50000 {x : ℝ} (ha : 101 ≤ x) (hb : x ≤ 50000) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h1 : x < 22016
  · exact psi_lee_nosal_101_22016 ha h1
  by_cases h2 : x < 25757
  · exact psi_lee_nosal_22016_25757 (le_of_not_gt h1) h2
  by_cases h3 : x < 29587
  · exact psi_lee_nosal_25757_29587 (le_of_not_gt h2) h3
  by_cases h4 : x < 32768
  · exact psi_lee_nosal_29587_32768 (le_of_not_gt h3) h4
  · exact psi_lee_nosal_32768_50000 (le_of_not_gt h4) hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
