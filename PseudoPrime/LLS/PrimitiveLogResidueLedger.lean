/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveLogResidueClosedForms
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogResidueLedger
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ZeroContribution
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveMultiplicityBridge
public import PseudoPrime.LLS.PrimitiveLogResidueBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ContourRegularity

/-!
# The logarithmic residue-sum upper bound for LLS Lemma 2.2

This file combines the origin-residue estimates in `PrimitiveLogResidueBounds.lean` with the
finite zero-sum bound from `AnalyticNumberTheory/DirichletLFunction/ZeroContribution.lean`.
The residue function and its splitting identity are defined in the foundation module
`AnalyticNumberTheory/DirichletLFunction/LogResidueLedger.lean`. For a nontrivial character the
logarithmic kernel is regular at `s = 1`, whose residue contributes zero.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- Bound the real logarithmic residue sum in a rectangle containing both zero and one,
for a primitive nonprincipal character under GRH and `x ≥ 64`.
Split off those two points, use the appropriate parity bound at zero and the vanishing
residue at one, then add the `2√x |B|` bound for the remaining ledger.
The result supplies a parity-independent bound for the finite contour identity. -/
theorem re_sum_llsPrimitiveLogResidueAt_le {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 64 ≤ x) {z w : ℂ}
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
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (show (0 : ℝ) < 64 by norm_num only) hx
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
          hprimitive hne hinv hx
    · rw [AnalyticNumberTheory.DirichletLFunction.dirichletLogResidueAt_zero_of_odd hne x hodd]
      exact
        re_deriv_llsPrimitiveLogMellinZeroRegularization_zero_of_odd_le hN2 hGRH hprimitive hne hinv
          hodd hx
  have herased :=
    AnalyticNumberTheory.DirichletLFunction.re_sum_erased_primitiveLogResidues_le hN2 hGRH
      hprimitive hne hinv hxpos (z := z) (w := w)
  simp only [Complex.add_re, Complex.zero_re]
  have hsum := add_le_add hr0_bound herased
  calc
    0 + (AnalyticNumberTheory.DirichletLFunction.dirichletLogResidueAt hne x 0).re +
          (∑
              ρ ∈
                ((AnalyticNumberTheory.DirichletLFunction.dirichletLFunctionSingularitiesInRectangle
                          χ hne z w).erase
                      1).erase
                  0,
              AnalyticNumberTheory.DirichletLFunction.dirichletLogResidueAt hne x ρ).re =
        (AnalyticNumberTheory.DirichletLFunction.dirichletLogResidueAt hne x 0).re +
          (∑
              ρ ∈
                ((AnalyticNumberTheory.DirichletLFunction.dirichletLFunctionSingularitiesInRectangle
                          χ hne z w).erase
                      1).erase
                  0,
              AnalyticNumberTheory.DirichletLFunction.dirichletLogResidueAt hne x ρ).re :=
      by rw [zero_add]
    _ ≤
        (2 + Real.log x) * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| +
              (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
            11 / 4 +
          2 * Real.sqrt x * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| :=
      hsum
    _ =
        (2 * Real.sqrt x + 2 + Real.log x) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| +
            (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
          11 / 4 :=
      by ring

end PseudoPrime.LLS
