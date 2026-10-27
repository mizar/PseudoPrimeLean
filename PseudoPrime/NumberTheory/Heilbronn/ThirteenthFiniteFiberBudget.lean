/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.FiniteFiberEnergyBridge
public import PseudoPrime.NumberTheory.Heilbronn.ThirteenthEnergyBridge
public import PseudoPrime.Analysis.ThirteenthCountingBudget

/-! # Finite-fiber budgets using the proved 32/13 energy exponent -/

public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Fixed rational exponents with `g/a=1/84+eta` and `71a+13g<39b`
admit one threshold for the full energy budget at every admissible height.
Combine the unconditional finite-fiber count with the proved thirteenth
energy estimate and logarithmic absorption. No energy estimate is assumed.
This strengthens the square-energy budget used by rational witness scales. -/
theorem exists_thirteenth_finite_fiber_energy_budget {eta : ℝ} {a b g : ℕ} (heta : 0 < eta)
    (ha : 0 < a) (hratio : (g : ℝ) / a = 1 / 84 + eta) (hb : b ≤ 2 * a)
    (hslack : 71 * a + 13 * g < 39 * b) :
    ∃ P : ℕ,
      ∀ (p H k : ℕ) [Fact p.Prime],
        Odd p →
          P ≤ p →
          H < p →
          (H : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ) →
          p ^ b ≤ k ^ a →
          H ^ a ≤ p ^ (2 * a - b) → p * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2 := by
  obtain ⟨D, hD⟩ := exists_finite_fiber_count_power_bound heta ha hratio
  have hs : 0 < 39 * b - (71 * a + 13 * g) := Nat.sub_pos_of_lt hslack
  obtain ⟨P, hP⟩ := exists_thirteenth_energy_power_threshold a D hs
  refine ⟨P, ?_⟩
  intro p H k hp hodd hlarge hHp htop hcut hheight
  exact
    PseudoPrime.Analysis.thirteenth_counting_budget (Fact.out : p.Prime).pos ha hb hslack hcut
      hheight (hD p H hodd hHp htop) (hP p hodd hlarge)

/-- The logarithmic-exponent-two energy bound supplies the same finite-fiber
counting budget with a smaller logarithmic absorption cost. -/
theorem exists_log_square_finite_fiber_energy_budget {eta : ℝ} {a b g : ℕ} (heta : 0 < eta)
    (ha : 0 < a) (hratio : (g : ℝ) / a = 1 / 84 + eta) (hb : b ≤ 2 * a)
    (hslack : 71 * a + 13 * g < 39 * b) :
    ∃ P : ℕ,
      ∀ (p H k : ℕ) [Fact p.Prime],
        Odd p →
          P ≤ p →
          H < p →
          (H : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ) →
          p ^ b ≤ k ^ a →
          H ^ a ≤ p ^ (2 * a - b) → p * heilbronnEnergy p * boundedCongruenceCount p H < k ^ 2 := by
  obtain ⟨D, hD⟩ := exists_finite_fiber_count_power_bound heta ha hratio
  have hs : 0 < 39 * b - (71 * a + 13 * g) := Nat.sub_pos_of_lt hslack
  obtain ⟨P, hP⟩ := exists_log_square_energy_power_threshold a D hs
  refine ⟨P, ?_⟩
  intro p H k hp hodd hlarge hHp htop hcut hheight
  exact
    PseudoPrime.Analysis.thirteenth_counting_budget (Fact.out : p.Prime).pos ha hb hslack hcut
      hheight (hD p H hodd hHp htop) (hP p hodd hlarge)

end PseudoPrime.NumberTheory.Heilbronn
