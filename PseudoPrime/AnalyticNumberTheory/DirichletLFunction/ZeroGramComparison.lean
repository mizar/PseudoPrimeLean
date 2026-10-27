/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ZeroGramPointBounds
public import PseudoPrime.Analysis.WeightedPointBudgetObstruction

/-!
# Comparison with the squared triangle bound

The explicit coefficient-independent Dirichlet Gram point budget never improves the
triangle-inequality upper bound on the same finite zero set. Phase-sensitive estimates
or additional coefficient structure are necessary for a witness-bound improvement.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For individual-RH primitive nonprincipal data on a finite height window, the explicit
Gram point upper bound dominates the squared triangle upper bound for every coefficient
family. Apply the uniform-budget obstruction to the actual completed-zero point theorem.
This rules out using that phase-blind point budget alone to improve a witness bound. -/
theorem completed_zero_triangle_sq_le_gram_budget {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (S : Finset ℂ) (a : ℂ → ℂ) {H : ℝ} (hH : 0 ≤ H)
    (hheight : ∀ ρ ∈ S, |ρ.im| ≤ H) :
    (∑ ρ ∈ S, (analyticOrderNatAt χ.completedLFunction ρ : ℝ) * ‖a ρ‖) ^ 2 ≤
      (1 + H) *
        (dirichletGramRowBudget q H *
          ∑ ρ ∈ S, (analyticOrderNatAt χ.completedLFunction ρ : ℝ) * ‖a ρ‖ ^ 2) := by
  have hC : 0 ≤ (1 + H) * dirichletGramRowBudget q H :=
    mul_nonneg (by linarith only [hH]) (dirichletGramRowBudget_nonneg q hH)
  have ht :=
    PseudoPrime.Analysis.ExponentialMeanSquare.triangle_sq_le_uniform_point_budget S
      (fun ρ ↦ (analyticOrderNatAt χ.completedLFunction ρ : ℝ)) (fun ρ hρ ↦ Nat.cast_nonneg _) hC
      (fun b ↦ by
        simpa only [mul_assoc] using
          completed_zero_sum_sq_le_height hq hRH hp hne hinv S b hH hheight)
      a
  simpa only [mul_assoc] using ht

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
