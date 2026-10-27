/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.FamilyImprimitiveHalfBudget
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalInducedConductorFour

/-! # Full nonprincipal half-scale family budgets including conductor four -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

open Classical in
/-- Fixed positive constants give a full nonprincipal-family half-scale budget
outside the reduced exceptional conductor divisors, including conductor four.
For every requested positive error rate, one threshold independent of the height,
ambient level, and finite family bounds the conductor-four contribution by that
rate times the scale. Split the family by primitive conductor four, combine the
two unconditional bounds, and recombine the level-change corrections exactly.
The remaining terms are the explicit primitive remainders and the gap-controlled
leading error; their uniform absorption is a subsequent quantitative scale choice. -/
theorem exists_character_family_half_scale_budget :
    ∃ A B C K T : ℝ,
      0 < A ∧
        0 < B ∧
        0 < C ∧
        0 < K ∧
        0 < T ∧
        ∀ (ε : ℝ),
          0 < ε →
            ∃ X : ℝ,
              4 ≤ X ∧
                ∀ (c : ℝ),
                  0 < c →
                    ∀ (H : ℕ),
                      2 ≤ H →
                        ∀ (x σ : ℝ),
                          X ≤ x →
                            (1 / 2 : ℝ) ≤ σ →
                            σ ≤ 1 →
                            A * (1 - σ) ≤ 1 / 2 →
                            2 * A * Real.log ((H + 1 + 1 : ℕ) : ℝ) ≤ Real.log x →
                            ∀ (q : ℕ) [NeZero q] (hq : q ≤ H + 1),
                              ∀ S : Finset (DirichletCharacter ℂ q),
                                (∀ χ ∈ S, χ ≠ 1) →
                                  (∀
                                    e ∈
                                      exceptionalFamilyConductorsAwayFromFour (H + 1)
                                        (1 - c / Real.log ((H + 1 : ℕ) : ℝ)),
                                    ¬e ∣ q) →
                                  (∑ χ ∈ S,
                                      ‖Arithmetic.characterLogWeightedSum x χ -
                                          Arithmetic.characterLogWeightedSum (x / 2) χ‖) ≤
                                    B * x *
                                        Real.exp
                                          (-(c / Real.log ((H + 1 : ℕ) : ℝ)) * Real.log x / 2) +
                                      ε * x +
                                      (∑
                                        p ∈
                                          (S.filter (fun χ ↦ χ.conductor ≠ 4)).image
                                            (Arithmetic.boundedPrimitiveCharacterLabel hq),
                                        primitiveHalfScaleRemainderBudget (p.1.val + 1) x σ H C K
                                          T) +
                                      (S.card : ℝ) *
                                        ((q.primeFactors.card : ℝ) * (Real.log x) ^ 2) := by
  obtain ⟨A, B, C, K, T, hA, hB, hC, hK, hT, hgood⟩ :=
    exists_character_family_half_scale_budget_off_exceptional_conductors
  refine ⟨A, B, C, K, T, hA, hB, hC, hK, hT, ?_⟩
  intro ε hε
  obtain ⟨X, hX, hfour⟩ := exists_uniform_induced_conductor_four_half_sum_bound hε
  refine ⟨max 4 X, le_max_left _ _, ?_⟩
  intro c hc H hH x σ hx hσlo hσhi hδ hscale q inst hq S hne havoid
  have hx4 : 4 ≤ x := (le_max_left 4 X).trans hx
  let G := S.filter (fun χ ↦ χ.conductor ≠ 4)
  let F := S.filter (fun χ ↦ χ.conductor = 4)
  have hb :=
    hgood c hc H hH x σ hx4 hσlo hσhi hδ hscale q hq G
      (fun χ hχ ↦ hne χ (Finset.mem_filter.mp hχ).1) (fun χ hχ ↦ (Finset.mem_filter.mp hχ).2) havoid
  have hf :=
    hfour q F (fun χ hχ ↦ hne χ (Finset.mem_filter.mp hχ).1)
      (fun χ hχ ↦ (Finset.mem_filter.mp hχ).2) x ((le_max_right 4 X).trans hx)
  have hs :=
    Finset.sum_filter_add_sum_filter_not (s := S) (f := fun χ ↦
      ‖Arithmetic.characterLogWeightedSum x χ - Arithmetic.characterLogWeightedSum (x / 2) χ‖) (p :=
      fun χ ↦ χ.conductor = 4)
  have hcard :=
    Finset.sum_filter_add_sum_filter_not (s := S) (f := fun _ ↦ (1 : ℝ)) (p := fun χ ↦
      χ.conductor = 4)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hcard
  have hm := congrArg (fun r : ℝ ↦ r * ((q.primeFactors.card : ℝ) * (Real.log x) ^ 2)) hcard
  dsimp only [F, G] at hb hf
  nlinarith only [hb, hf, hs, hm]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
