/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalLogRightPowerWeights
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.FamilyCharacterWeightedGap

/-! # Regularized near-one zero norm sums outside exceptional conductors -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

namespace LogFreeDensity

open Classical in
/-- Positive absolute constants bound the total regularized near-one zero norm
sum of any finite character family avoiding the reduced exceptional conductors
and conductor four. The scale and real-part conditions remain explicit. Absorb
the genus correction into the power weight and apply the proved multiplicity-
preserving family density estimate. The total leading error acquires no extra
factor from the number of characters, and neither RH nor an unproved density
input is assumed. This is the near-one contribution to the half-scale family budget. -/
theorem exists_character_family_regularized_zero_norm_sum_off_exceptional_conductors :
    ∃ A C : ℝ,
      0 < A ∧
        0 < C ∧
        ∀ (c : ℝ),
          0 < c →
            ∀ (R : ℕ),
              2 ≤ R →
                ∀ (x σ₀ : ℝ),
                  2 ≤ x →
                    (1 / 2 : ℝ) ≤ σ₀ →
                    σ₀ ≤ 1 →
                    A * (1 - σ₀) ≤ 1 / 2 →
                    2 * A * Real.log ((R + 1 : ℕ) : ℝ) ≤ Real.log x →
                    ∀ S : Finset (FamilyCharacterLabel R),
                      (∀ p ∈ S, p.1.val + 1 ≠ 4) →
                        (∀ p ∈ S,
                          p.1.val + 1 ∉
                            exceptionalFamilyConductorsAwayFromFour R (1 - c / Real.log R)) →
                        (∑ p ∈ S,
                            if hne : p.2 ≠ 1 then
                              if _hp : p.2.IsPrimitive then
                                ∑
                                  ρ ∈
                                    completedZerosInRectangle p.2 hne
                                      ((σ₀ : ℂ) - (R : ℝ) * Complex.I)
                                      ((1 : ℂ) + (R : ℝ) * Complex.I),
                                  ‖regularizedLogHalfZeroTerm p.2 x ρ‖
                              else 0
                            else 0) ≤
                          C * x * Real.exp (-(c / Real.log R) * Real.log x / 2) := by
  obtain ⟨A, C, hA, hC, hbound⟩ :=
    exists_character_family_weighted_zero_sum_off_exceptional_conductors
  let K : ℝ := 8 + 4 * Real.log 2
  have hK : 0 < K := by
    dsimp only [K]
    linarith only [Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 2)]
  refine ⟨A, K * C, hA, mul_pos hK hC, ?_⟩
  intro c hc R hR x σ₀ hx hσlo hσhi hδ hscale S hfour havoid
  have hb := hbound c hc R hR x σ₀ (by linarith only [hx]) hσlo hσhi hδ hscale S hfour havoid
  have hm := mul_le_mul_of_nonneg_left hb hK.le
  have hn :
    (∑ p ∈ S,
        if hne : p.2 ≠ 1 then
          if _hp : p.2.IsPrimitive then
            ∑
              ρ ∈
                completedZerosInRectangle p.2 hne ((σ₀ : ℂ) - (R : ℝ) * Complex.I)
                  ((1 : ℂ) + (R : ℝ) * Complex.I),
              ‖regularizedLogHalfZeroTerm p.2 x ρ‖
          else 0
        else 0) ≤
      K *
        ∑ p ∈ S,
          if hne : p.2 ≠ 1 then
            if _hp : p.2.IsPrimitive then
              ∑
                ρ ∈
                  completedZerosInRectangle p.2 hne ((σ₀ : ℂ) - (R : ℝ) * Complex.I)
                    ((1 : ℂ) + (R : ℝ) * Complex.I),
                (MeromorphicOn.divisor p.2.completedLFunction Set.univ ρ : ℝ) *
                  (x ^ ρ.re / (1 + ρ.im ^ 2))
            else 0
          else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p _
    by_cases hne : p.2 ≠ 1
    · rw [dite_eq_left hne, dite_eq_left hne]
      by_cases hp : p.2.IsPrimitive
      · rw [dite_eq_left hp, dite_eq_left hp]
        exact sum_norm_regularizedLogHalfZeroTerm_rectangle_le_right_power_weight hne hx hσlo hσhi R
      · rw [dite_eq_right hp, dite_eq_right hp, mul_zero]
    · rw [dite_eq_right hne, dite_eq_right hne, mul_zero]
  calc
    _ ≤ K * (C * x * Real.exp (-(c / Real.log R) * Real.log x / 2)) := hn.trans hm
    _ = _ := by ring

end LogFreeDensity

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
