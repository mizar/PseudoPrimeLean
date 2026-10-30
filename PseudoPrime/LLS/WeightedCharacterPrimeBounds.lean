/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.ResidueSubgroup
public import PseudoPrime.LLS.WeightedCharacterComparison
public import PseudoPrime.LLS.ConductorSumBounds
public import PseudoPrime.NumberTheory.CharacterWeights
/-! # Weighted conductor budgets and actual least-prime criteria -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements
/-- Under GRH, finite nonnegative weights on nonprincipal characters admit
a uniform upper bound using kernel mass times the exact weighted conductor
sum, plus total weight times the ambient allowance and common scale remainder.
The constant and modulus threshold are independent of the family and weights. -/
theorem exists_weighted_character_upper (K : MellinKernel)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η →
      ∃ Q : ℕ, 20000 ≤ Q ∧ ∀ (q : ℕ) [NeZero q], Q ≤ q →
        ∀ (S : Finset (DirichletCharacter ℂ q)) (w : DirichletCharacter ℂ q → ℝ),
          (∀ χ ∈ S, 0 ≤ w χ) → (∀ χ ∈ S, χ ≠ 1) →
          ∀ x : ℝ, 2 ≤ x →
            (∑ χ ∈ S, w χ * (∑' n : ℕ, (MellinKernel.summand K) χ x n).re) ≤
              K.mass * NumberTheory.weightedConductorLogSum S w +
                (η * Real.log q + C * (1 + Real.log q * Real.log x / Real.sqrt x)) *
                  NumberTheory.characterWeightTotal S w := by
  obtain ⟨C, hC, hb⟩ := MellinKernel.exists_uniform_nonprincipal_summand_le_conductor K hg
  refine ⟨C, hC, ?_⟩
  intro η hη
  obtain ⟨Q, hQ, hb⟩ := hb η hη
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq S w hw hnp x hx
  have hs := Finset.sum_le_sum (fun χ hχ ↦
    mul_le_mul_of_nonneg_left (hb q hq χ (hnp χ hχ) x hx) (hw χ hχ))
  apply hs.trans_eq
  rw [NumberTheory.weightedConductorLogSum,
    NumberTheory.characterWeightTotal, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro χ _
  ring
/-- Under GRH, a strict weighted conductor-budget gap against the actual
principal prefix and tail yields an actual least eligible outside prime.
The error constant and modulus threshold are uniform over subgroups, families,
weights and trace penalties. Nonnegativity, nonprincipality, annihilator
membership and the trace certificate remain explicit hypotheses. -/
theorem weighted_least_prime_criterion (K : MellinKernel)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η →
      ∃ Q : ℕ, 20000 ≤ Q ∧ ∀ (q : ℕ) [NeZero q], Q ≤ q →
        ∀ (H : Subgroup (ZMod q)ˣ) (S : Finset (DirichletCharacter ℂ q))
          (w : DirichletCharacter ℂ q → ℝ),
          (∀ χ ∈ S, 0 ≤ w χ) → (∀ χ ∈ S, χ ≠ 1) →
          (∀ χ ∈ S, χ ∈ NumberTheory.subgroupAnnihilator H) →
          ∀ m X x : ℝ, 2 ≤ x →
            (∀ z : ZMod q, -m ≤ NumberTheory.weightedCharacterTrace S w z) →
            ∀ T : Finset ℕ, (∀ n ∈ T, (n : ℝ) ≤ X) →
              K.mass * NumberTheory.weightedConductorLogSum S w +
                  (η * Real.log q + C * (1 + Real.log q * Real.log x / Real.sqrt x)) *
                    NumberTheory.characterWeightTotal S w <
                (NumberTheory.characterWeightTotal S w + m) *
                    (∑ n ∈ T,
                      ((MellinKernel.summand K) (1 : DirichletCharacter ℂ q)
                      x n).re) -
                  m * (∑' n : ℕ,
                    (MellinKernel.summand K) (1 : DirichletCharacter ℂ q) x
                    n).re →
              ∃ p : ℕ, IsLeast (NumberTheory.primesOutside q H) p ∧ (p : ℝ) ≤ X := by
  obtain ⟨C, hC, hb⟩ := exists_weighted_character_upper K hg
  refine ⟨C, hC, ?_⟩
  intro η hη
  obtain ⟨Q, hQ, hb⟩ := hb η hη
  refine ⟨Q, hQ, ?_⟩
  intro q _ hq H S w hw hnp hS m X x hx htrace T hT hgap
  exact least_weighted_prime_of_gap K H S w hS
    ((by norm_num only : (0 : ℝ) < 2).trans_le hx) htrace T hT
    ((hb q hq S w hw hnp x hx).trans_lt hgap)
end PseudoPrime.LLS.PaperStatements
