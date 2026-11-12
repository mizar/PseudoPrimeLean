/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalInterval
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalInterval40512
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalInterval41024
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalInterval41024to41536
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalInterval41536to42048
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalInterval42048to42560
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalInterval42560to42816
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalInterval42816to43072
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalInterval43072to43584
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalInterval43584to44096
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalInterval44096to44608
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalInterval44608to45120
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalInterval45120to45632
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalInterval45632to46144
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalInterval46144to46656
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalInterval46656to47168
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalInterval47168to47680
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalInterval47680to48192
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalInterval48192to48704
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalInterval48704to49216
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalInterval49216to49728
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalInterval49728to50000

/-! # Finite Lee–Nosal psi error bound through 50000 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The Lee–Nosal psi error bound holds unconditionally on `[39760, 50000]`.
The proof combines independent interval theorems. -/
theorem psi_lee_nosal_39760_50000 {x : ℝ} (ha : 39760 ≤ x) (hb : x ≤ 50000) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h40000 : x ≤ 40000
  · exact psi_lee_nosal_39760_40000 ha h40000
  by_cases h40512 : x ≤ 40512
  · exact psi_lee_nosal_40000_40512 (by linarith only [h40000]) h40512
  by_cases h41024 : x ≤ 41024
  · exact psi_lee_nosal_40512_41024 (by linarith only [h40512]) h41024
  by_cases h41536 : x ≤ 41536
  · exact psi_lee_nosal_41024_41536 (by linarith only [h41024]) h41536
  by_cases h42048 : x ≤ 42048
  · exact psi_lee_nosal_41536_42048 (by linarith only [h41536]) h42048
  by_cases h42560 : x ≤ 42560
  · exact psi_lee_nosal_42048_42560 (by linarith only [h42048]) h42560
  by_cases h42816 : x ≤ 42816
  · exact psi_lee_nosal_42560_42816 (by linarith only [h42560]) h42816
  by_cases h43072 : x ≤ 43072
  · exact psi_lee_nosal_42816_43072 (by linarith only [h42816]) h43072
  by_cases h43584 : x ≤ 43584
  · exact psi_lee_nosal_43072_43584 (by linarith only [h43072]) h43584
  by_cases h44096 : x ≤ 44096
  · exact psi_lee_nosal_43584_44096 (by linarith only [h43584]) h44096
  by_cases h44608 : x ≤ 44608
  · exact psi_lee_nosal_44096_44608 (by linarith only [h44096]) h44608
  by_cases h45120 : x ≤ 45120
  · exact psi_lee_nosal_44608_45120 (by linarith only [h44608]) h45120
  by_cases h45632 : x ≤ 45632
  · exact psi_lee_nosal_45120_45632 (by linarith only [h45120]) h45632
  by_cases h46144 : x ≤ 46144
  · exact psi_lee_nosal_45632_46144 (by linarith only [h45632]) h46144
  by_cases h46656 : x ≤ 46656
  · exact psi_lee_nosal_46144_46656 (by linarith only [h46144]) h46656
  by_cases h47168 : x ≤ 47168
  · exact psi_lee_nosal_46656_47168 (by linarith only [h46656]) h47168
  by_cases h47680 : x ≤ 47680
  · exact psi_lee_nosal_47168_47680 (by linarith only [h47168]) h47680
  by_cases h48192 : x ≤ 48192
  · exact psi_lee_nosal_47680_48192 (by linarith only [h47680]) h48192
  by_cases h48704 : x ≤ 48704
  · exact psi_lee_nosal_48192_48704 (by linarith only [h48192]) h48704
  by_cases h49216 : x ≤ 49216
  · exact psi_lee_nosal_48704_49216 (by linarith only [h48704]) h49216
  by_cases h49728 : x ≤ 49728
  · exact psi_lee_nosal_49216_49728 (by linarith only [h49216]) h49728
  exact psi_lee_nosal_49728_50000 (by linarith only [h49728]) hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
