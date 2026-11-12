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
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal39168Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal39424Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalPrimePowers

/-! # A finite Lee–Nosal theta error bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The Lee–Nosal theta error bound holds unconditionally on `[39168, 39424]`.
Certified endpoint bounds supply the interval criterion. -/
theorem theta_lee_nosal_39168_39424 {x : ℝ} (ha : 39168 ≤ x) (hb : x ≤ 39424) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  apply theta_lee_nosal_cell (a := 39168) (b := 39424) (c := 600) _ ha hb _ _ _
  · exact Real.exp_one_lt_three.le.trans (by norm_num only)
  · have h := psi_sub_theta_le_300 (x := 39168) (by norm_num only) (by norm_num only)
    linarith only [h, psi_39168_lower]
  · have ht := Chebyshev.theta_le_psi 39424
    linarith only [ht, psi_39424_upper]
  · exact lee_nosal_envelope_ge_600_of_32768 (by norm_num only)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
