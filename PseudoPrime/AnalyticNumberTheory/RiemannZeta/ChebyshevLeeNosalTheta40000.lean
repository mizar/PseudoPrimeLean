/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalPrimePowers
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalCells
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalEnvelope
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal40000Bounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal40512

/-! # A finite Lee–Nosal theta error bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The unconditional Lee–Nosal theta error bound holds on `[40000, 40312]`.
The proof combines two psi endpoint certificates with the global prime-power bound. -/
theorem theta_lee_nosal_40000_40312 {x : ℝ} (ha : 40000 ≤ x) (hb : x ≤ 40312) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  apply theta_lee_nosal_cell (a := 40000) (b := 40312) (c := 600) _ ha hb _ _ _
  · exact Real.exp_one_lt_three.le.trans (by norm_num only)
  · have h := psi_sub_theta_le_300 (x := 40000) (by norm_num only) (by norm_num only)
    linarith only [h, psi_40000_bounds.1]
  · have hm := Chebyshev.psi_mono (show (40312 : ℝ) ≤ 40512 by norm_num only)
    have ht := Chebyshev.theta_le_psi 40312
    linarith only [hm, ht, psi_40512_upper]
  · exact lee_nosal_envelope_ge_600 (by norm_num only) (by norm_num only)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
