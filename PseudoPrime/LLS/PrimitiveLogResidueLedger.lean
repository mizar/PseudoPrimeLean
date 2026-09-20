/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveLogResidueClosedForms
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogResidueLedger
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ZeroContribution
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveMultiplicityBridge
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.QuadraticFunctionalConsequences
import PseudoPrime.LLS.PrimitiveLogResidueBounds
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ContourRegularity

/-!
# The logarithmic residue-sum upper bound for LLS Lemma 2.2

This file combines the origin-residue estimates in `PrimitiveLogResidueBounds.lean` with the
finite zero-sum bound from `AnalyticNumberTheory/DirichletLFunction/ZeroContribution.lean`.
The residue function and its splitting identity are defined in the foundation module
`AnalyticNumberTheory/DirichletLFunction/LogResidueLedger.lean`. For a nontrivial character the
logarithmic kernel is regular at `s = 1`, whose residue contributes zero.
-/

namespace PseudoPrime.LLS

/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial quadratic mod `N`, GRH, `χ⁻¹ ≠ 1`, `x ≥ 64`,
`0, 1` in the primitive singularity ledger of `z, w`.
Conclusion:
`Re Σ_{s ∈ S} r_log(s) ≤ (2√x + 2 + log x)|Re B(χ)| + (1/2)(log N - log π) log x - 11/4`.
Content: `DirichletLFunction.dirichletSplitLogSingularitySum` splits off `r_log(1) = 0`
(`DirichletLFunction.dirichletLogResidueAt_one`) and `r_log(0)` (parity-dispatched into the `s = 0`
bounds from
`PrimitiveLogResidueBounds.lean`), and `DirichletLFunction.re_sum_erased_primitiveLogResidues_le`
bounds the rest by
`2√x|Re B(χ)|`. Adding the two estimates gives the coefficient in LLS Section 3.1, equation (3.3).
Role: supplies the uniform finite residue-sum bound for the logarithmic contour-limit argument.
-/
theorem re_sum_llsPrimitiveLogResidueAt_le {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 64 ≤ x) {z w : ℂ}
    (h0 :
      (0 : ℂ) ∈
        AnalyticNumberTheory.DirichletLFunction.dirichletLFunctionSingularitiesInRectangle χ hne z
          w)
    (h1 :
      (1 : ℂ) ∈
        AnalyticNumberTheory.DirichletLFunction.dirichletLFunctionSingularitiesInRectangle χ hne z
          w) :
    (∑
          s ∈
            AnalyticNumberTheory.DirichletLFunction.dirichletLFunctionSingularitiesInRectangle χ hne
              z w,
          AnalyticNumberTheory.DirichletLFunction.dirichletLogResidueAt hne x s).re ≤
      (2 * Real.sqrt x + 2 + Real.log x) *
            |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| +
          (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
        11 / 4 := by
  have hxpos : (0 : ℝ) < x := by linarith
  rw [AnalyticNumberTheory.DirichletLFunction.dirichletSplitLogSingularitySum x hne h1 h0,
    AnalyticNumberTheory.DirichletLFunction.dirichletLogResidueAt_one hne x]
  have hr0_bound :
    (AnalyticNumberTheory.DirichletLFunction.dirichletLogResidueAt hne x 0).re ≤
      (2 + Real.log x) * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| +
          (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
        11 / 4 := by
    rcases χ.even_or_odd with heven | hodd
    · rw [AnalyticNumberTheory.DirichletLFunction.dirichletLogResidueAt_zero_of_even hne x heven]
      exact
        re_iteratedDeriv_two_llsPrimitiveLogEvenZeroRegularization_zero_div_two_le hN2 hGRH
          hprimitive hne hinv hquad hx
    · rw [AnalyticNumberTheory.DirichletLFunction.dirichletLogResidueAt_zero_of_odd hne x hodd]
      exact
        re_deriv_llsPrimitiveLogMellinZeroRegularization_zero_of_odd_le hN2 hGRH hprimitive hne hinv
          hquad hodd hx
  have herased :=
    AnalyticNumberTheory.DirichletLFunction.re_sum_erased_primitiveLogResidues_le hN2 hGRH
      hprimitive hne hinv hquad hxpos (z := z) (w := w)
  simp only [Complex.add_re, Complex.zero_re]
  nlinarith [hr0_bound, herased]

end PseudoPrime.LLS
