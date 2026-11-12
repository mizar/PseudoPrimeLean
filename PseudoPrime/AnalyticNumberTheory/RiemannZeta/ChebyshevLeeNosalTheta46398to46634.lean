/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalCells
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalEnvelope
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalPrimePowers
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal46398ThetaLower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal46656Upper

/-! # Finite Lee–Nosal theta error bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The unconditional Lee–Nosal theta error bound holds on `[46398, 46634]`.
The proof uses independent psi endpoint and prime-power mass certificates. -/
theorem theta_lee_nosal_46398_46634 {x : ℝ} (ha : 46398 ≤ x) (hb : x ≤ 46634) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  apply theta_lee_nosal_cell (a := 46398) (b := 46634) (c := 600) _ ha hb _ _ _
  · exact Real.exp_one_lt_three.le.trans (by norm_num only)
  · have h := psi_sub_theta_le_300 (x := 46398) (by norm_num only) (by norm_num only)
    linarith only [h, psi_46398_theta_lower]
  · have hm := Chebyshev.psi_mono (show (46634 : ℝ) ≤ 46656 by norm_num only)
    have ht := Chebyshev.theta_le_psi 46634
    linarith only [hm, ht, psi_46656_upper]
  · exact lee_nosal_envelope_ge_600 (by norm_num only) (by norm_num only)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
