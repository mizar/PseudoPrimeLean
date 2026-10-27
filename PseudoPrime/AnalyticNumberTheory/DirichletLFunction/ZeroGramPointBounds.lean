/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ZeroGramNumericalBounds
public import PseudoPrime.Analysis.ExponentialMeanSquareRowPointBounds

/-!
# Direct explicit point bounds for fixed Dirichlet zero sums

The exact conductor row and direct derivative Schur bound avoid the Abel block factor four.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a fixed primitive nonprincipal individual-RH character and a finite height
window, the actual multiplicity-weighted zero sum has squared norm at most
(1+H)(log q+20+log(2+H)) times its coefficient l2 mass. Apply the direct Schur-Sobolev
theorem to actual Dirichlet rows; no independent derivative or energy budget remains. -/
theorem completed_zero_sum_sq_le_height {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (S : Finset ℂ) (a : ℂ → ℂ) {H : ℝ} (hH : 0 ≤ H) (hheight : ∀ ρ ∈ S, |ρ.im| ≤ H) :
    ‖∑ ρ ∈ S, ((analyticOrderNatAt χ.completedLFunction ρ : ℝ) : ℂ) * a ρ‖ ^ 2 ≤
      (1 + H) *
        (dirichletGramRowBudget q H *
          ∑ ρ ∈ S, (analyticOrderNatAt χ.completedLFunction ρ : ℝ) * ‖a ρ‖ ^ 2) := by
  have h :=
    PseudoPrime.Analysis.ExponentialMeanSquare.point_le_weighted_rows_height S Complex.im
      (fun ρ ↦ (analyticOrderNatAt χ.completedLFunction ρ : ℝ)) a
      (dirichletGramRowBudget_nonneg q hH) hH (fun ρ hρ ↦ Nat.cast_nonneg _) hheight
      (fun ρ hρ ↦ by
        have hr := finite_completed_gram_row_le hq hRH hp hne hinv S ρ.im
        have hb := completed_logDeriv_re_le_height hne (hheight ρ hρ)
        dsimp only [dirichletGramRowBudget]
        linarith only [hr, hb])
  simpa only [PseudoPrime.Analysis.ExponentialMeanSquare.exponentialSum, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, mul_one] using h

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
