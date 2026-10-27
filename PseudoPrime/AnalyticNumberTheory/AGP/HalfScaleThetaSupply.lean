/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.AGP.LogDifferenceThetaSupply
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogHalfScaleRecovery

/-! # Aggregate half-scale error budgets imply progression theta supply -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

open Classical in
/-- One absolute principal threshold works for all positive moduli, coprime
residues, and local cutoffs `L >= 1`. Aggregate nonprincipal half-scale error
`epsilon t` above `L` implies `theta(x;q,a) >= x/(2 phi(q))` whenever the displayed
explicit budget holds and `4x/5 >= L`. Recover full sums dyadically, compare the
two endpoints, and use the finite arithmetic theta conversion. The half-scale
family estimate and the scalar budget remain separate tasks for density and scale selection. -/
theorem exists_uniform_half_scale_theta_threshold :
    ∃ X : ℝ,
      1 ≤ X ∧
        ∀ (q a : ℕ) [NeZero q],
          Nat.Coprime a q →
            ∀ (ε L x : ℝ),
              0 ≤ ε →
                1 ≤ L →
                X ≤ x →
                L ≤ 4 * x / 5 →
                (∀ t : ℝ,
                  L ≤ t →
                    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
                        ‖Arithmetic.characterLogWeightedSum t χ -
                            Arithmetic.characterLogWeightedSum (t / 2) χ‖ ≤
                      ε * t) →
                (1 / 2 : ℝ) * q.primeFactors.card * (Real.log x) ^ 2 +
                    (4 * ε * x +
                      2 * (((Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1).card : ℝ) *
                        ((Real.log 4 + 4) * (2 * L) * Real.log (2 * L))) +
                    18 * (q.totient : ℝ) * Real.sqrt x * Real.log (5 / 4) ≤
                  (1 / 32 : ℝ) * x * Real.log (5 / 4) →
                x / (2 * (q.totient : ℝ)) ≤ thetaInProgressionReal x q a := by
  obtain ⟨X, hX, htheta⟩ := exists_uniform_log_difference_theta_threshold
  refine ⟨X, hX, ?_⟩
  intro q a inst ha ε L x hε hL hx hLx hhalf hbudget
  have hb :=
    Arithmetic.sum_norm_characterLogWeightedSum_four_fifths_difference_le
      ((Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1) (fun _ ↦ q) (fun χ ↦ χ) hε hL hLx
      hhalf
  apply htheta q a ha x hx
  linarith only [hb, hbudget]

end PseudoPrime.AnalyticNumberTheory.AGP
