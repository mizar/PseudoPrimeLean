/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorLogDeriv
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveHorizontalLogDerivBound
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorMultiplicityBridge
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ZeroContribution
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ContourRegularity
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.SmoothedContour
import Mathlib.Analysis.Meromorphic.Complex

/-!
# Finite reciprocal zero-ledger bound

After erasing the Mellin endpoints `0,1`, each reciprocal residue is an ordinary
zero contribution. The multiplicity bridge and trivial-zero sign bound compare its
real part to a completed-zero norm. The finite norm sum is at most
`2*|primitiveBRe χ|/sqrt x` under the general primitive-character GRH hypotheses.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-! ### Analyticity/multiplicity-bridge inputs

`GammaFactorMultiplicityBridge` supplies analyticity at nonzero gamma-factor values and
identifies the ordinary analytic multiplicity with the completed divisor there.
These inputs do not require a particular contour weight. -/

/-! ### From pointwise zero contributions to the erased finite ledger

`ZeroContribution` supplies the trivial-zero sign estimate and the finite completed-zero
norm bound. Apply those general estimates to the rectangle ledger after erasing `0,1`. -/

/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial mod `N`, GRH, `χ⁻¹ ≠ 1`, `x > 0`.
Conclusion: `Re Σ_{ρ ∈ (S.erase 1).erase 0} r(ρ) ≤ 2|Re B(χ)|/√x`, where `S` is the primitive
singularity ledger of any rectangle `z, w`.
Content: `Complex.re_sum` splits the real part of the sum; on the erased ledger,
`DirichletLFunction.dirichletReciprocalResidueAt_eq_zeroContribution_of_mem_erase` identifies each
residue with
its zero contribution and gives `ρ ≠ 0`; the pointwise bound
(`DirichletLFunction.dirichletLFunctionReciprocalZeroContribution_re_le_completedTerm_norm`)
dominates each summand
by the completed-zero term's norm; `Finset.sum_le_sum` plus the finite subset bound
(`sum_norm_completedReciprocalZeroTerm_le_abs_BRe_of_grh`) finishes.
Role: **the zero-contribution completion** — the boxed `(Z)` bound `Re Σ_{ρ≠0,1} r(ρ) ≤ 2b/√x`,
with an
`A`,`k`-independent right-hand side, closing off the need for any infinite zero-ledger `Tendsto`
machinery.
-/
theorem re_sum_erased_primitiveReciprocalResidues_le {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) {z w : ℂ} :
    (∑ ρ ∈ ((dirichletLFunctionSingularitiesInRectangle χ hne z w).erase 1).erase 0,
          dirichletReciprocalResidueAt hne x ρ).re ≤
      2 * |primitiveBRe χ| / Real.sqrt x := by
  set S := ((dirichletLFunctionSingularitiesInRectangle χ hne z w).erase 1).erase 0 with hS_def
  rw [Complex.re_sum]
  have hstep :
    ∀ ρ ∈ S,
      (dirichletReciprocalResidueAt hne x ρ).re ≤
        ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
              (x : ℂ) ^ (ρ - 1) /
            (ρ * (ρ - 1))‖ := by
    intro ρ hρ
    rw [dirichletReciprocalResidueAt_eq_zeroContribution_of_mem_erase x hne (hS_def ▸ hρ)]
    have hρ0 : ρ ≠ 0 := (Finset.mem_erase.mp hρ).1
    exact dirichletLFunctionReciprocalZeroContribution_re_le_completedTerm_norm hne hx hρ0
  calc
    ∑ ρ ∈ S, (dirichletReciprocalResidueAt hne x ρ).re ≤
        ∑ ρ ∈ S,
          ‖((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℤ) : ℂ) *
                (x : ℂ) ^ (ρ - 1) /
              (ρ * (ρ - 1))‖ :=
      Finset.sum_le_sum hstep
    _ ≤ 2 * |primitiveBRe χ| / Real.sqrt x :=
      sum_norm_completedReciprocalZeroTerm_le_abs_BRe_of_grh hN2 hGRH hprimitive hne hinv hx S

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
