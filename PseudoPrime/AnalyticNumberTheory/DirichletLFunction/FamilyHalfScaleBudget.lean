/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalHalfScaleBudget
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.FamilyRegularizedGap

/-! # Unconditional primitive-family half-scale arithmetic budgets -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- A primitive nonprincipal character at nonzero level has level at least two.
Primitivity identifies the level with its conductor, and conductor one is equivalent
to principality. This discharges the lower-modulus condition in finite family sums. -/
theorem two_le_level_of_primitive_nonprincipal {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) : 2 ≤ q := by
  apply (Nat.two_le_iff q).mpr
  refine ⟨NeZero.ne q, ?_⟩
  intro hq
  apply hne
  exact χ.eq_one_iff_conductor_eq_one.mpr ((DirichletCharacter.isPrimitive_def χ).mp hp |>.trans hq)

/-- Collect the low and intermediate strips, high-zero tail, and logarithmic
arithmetic remainder for one primitive character at a natural height cutoff.
The three positive constants are absolute once chosen by the unconditional
individual estimates. This separates the gap-controlled leading family error
from the explicit remainder to be absorbed by scale selection. -/
noncomputable def primitiveHalfScaleRemainderBudget (q : ℕ) (x σ : ℝ) (H : ℕ) (C K T : ℝ) : ℝ :=
  ((2 * ((H + 1 : ℕ) : ℝ) + 1) * K * (Real.log q + Real.log (4 + ((H + 1 : ℕ) : ℝ)) + 1)) *
      regularizedLowHeightMajorant x σ +
    regularizedHighZeroTailMajorant q x H T +
    C * (Real.log x + 1)

namespace LogFreeDensity

open Classical in
/-- There are fixed positive constants bounding the aggregate half-scale
arithmetic norm of any finite primitive nonprincipal family outside the reduced
exceptional conductors, with conductor four excluded. Split at height `H+1`,
apply the proved regularized near-one family estimate, and sum the individual
explicit remainders. The leading exponential error has no character-count factor.
All density, counting, truncation, and remainder estimates are unconditional;
only the displayed scale and exception-avoidance conditions remain. -/
theorem exists_primitive_character_family_half_scale_budget_off_exceptional_conductors :
    ∃ A B C K T : ℝ,
      0 < A ∧
        0 < B ∧
        0 < C ∧
        0 < K ∧
        0 < T ∧
        ∀ (c : ℝ),
          0 < c →
            ∀ (H : ℕ),
              2 ≤ H →
                ∀ (x σ : ℝ),
                  4 ≤ x →
                    (1 / 2 : ℝ) ≤ σ →
                    σ ≤ 1 →
                    A * (1 - σ) ≤ 1 / 2 →
                    2 * A * Real.log ((H + 1 + 1 : ℕ) : ℝ) ≤ Real.log x →
                    ∀ S : Finset (FamilyCharacterLabel (H + 1)),
                      (∀ p ∈ S, p.2.IsPrimitive) →
                        (∀ p ∈ S, p.2 ≠ 1) →
                        (∀ p ∈ S, p.1.val + 1 ≠ 4) →
                        (∀ p ∈ S,
                          p.1.val + 1 ∉
                            exceptionalFamilyConductorsAwayFromFour (H + 1)
                              (1 - c / Real.log ((H + 1 : ℕ) : ℝ))) →
                        (∑ p ∈ S,
                            ‖Arithmetic.characterLogWeightedSum x p.2 -
                                Arithmetic.characterLogWeightedSum (x / 2) p.2‖) ≤
                          B * x * Real.exp (-(c / Real.log ((H + 1 : ℕ) : ℝ)) * Real.log x / 2) +
                            ∑ p ∈ S,
                              primitiveHalfScaleRemainderBudget (p.1.val + 1) x σ H C K T := by
  obtain ⟨A, B, hA, hB, hnear⟩ :=
    exists_character_family_regularized_zero_norm_sum_off_exceptional_conductors
  obtain ⟨C, K, T, hC, hK, hT, hpart⟩ :=
    exists_norm_characterLogWeightedSum_half_le_truncated_zero_budget
  refine ⟨A, B, C, K, T, hA, hB, hC, hK, hT, ?_⟩
  intro c hc H hH x σ hx hσlo hσhi hδ hscale S hp hne hfour havoid
  have hx2 : 2 ≤ x := by linarith only [hx]
  have hH2 : 2 ≤ H + 1 := hH.trans (Nat.le_succ H)
  have hb := hnear c hc (H + 1) hH2 x σ hx2 hσlo hσhi hδ hscale S hfour havoid
  have hs :
    (∑ p ∈ S,
        ‖Arithmetic.characterLogWeightedSum x p.2 -
            Arithmetic.characterLogWeightedSum (x / 2) p.2‖) ≤
      (∑ p ∈ S,
          if hne : p.2 ≠ 1 then
            if _hp : p.2.IsPrimitive then
              ∑
                ρ ∈
                  completedZerosInRectangle p.2 hne ((σ : ℂ) - ((H + 1 : ℕ) : ℝ) * Complex.I)
                    ((1 : ℂ) + ((H + 1 : ℕ) : ℝ) * Complex.I),
                ‖regularizedLogHalfZeroTerm p.2 x ρ‖
            else 0
          else 0) +
        ∑ p ∈ S, primitiveHalfScaleRemainderBudget (p.1.val + 1) x σ H C K T := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hps
    have hpn := hne p hps
    have hpp := hp p hps
    have hq := two_le_level_of_primitive_nonprincipal hpp hpn
    have hb := hpart (p.1.val + 1) hq p.2 hpp hpn (inv_ne_one.mpr hpn) x σ hx hσhi H hH
    rw [dite_eq_left hpn, dite_eq_left hpp]
    dsimp only [primitiveHalfScaleRemainderBudget]
    linarith only [hb]
  exact hs.trans (add_le_add hb le_rfl)

end LogFreeDensity

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
