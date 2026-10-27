/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.WeightedCorrelationAmplification

/-! # Invariant correlation weights supported on selected nonzero levels -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Keep the exact correlation at nonzero differences satisfying P and
zero elsewhere. Its pair mass is the retained level energy. Arbitrary P
supports energy thresholds and dyadic bands with the same amplification. -/
noncomputable def heilbronnLevelWeight (p : ℕ) [Fact p.Prime] (P : ℕ → Prop) (a : ZMod (p ^ 2)) :
    ℕ := by
  classical
    exact if a ∈ heilbronnCorrelationLevel p P then Nat.card (cosetDifferenceAt p 0 0 a) else 0

/-- The selected weight is even because correlation and nonzero support
are preserved by negation. This verifies kernel symmetry for all levels. -/
theorem heilbronnLevelWeight_neg {p : ℕ} [Fact p.Prime] (P : ℕ → Prop) (a : ZMod (p ^ 2)) :
    heilbronnLevelWeight p P (-a) = heilbronnLevelWeight p P a := by
  classical
    simp only [heilbronnLevelWeight, mem_heilbronnCorrelationLevel, neg_ne_zero,
    heilbronn_correlation_neg]

/-- The selected weight is invariant under Heilbronn multiplication.
Unit cancellation preserves nonzero support and scaling preserves correlation.
This verifies constant row mass without an additional numerical hypothesis. -/
theorem heilbronnLevelWeight_invariant {p : ℕ} [Fact p.Prime] (P : ℕ → Prop) {γ : ZMod (p ^ 2)}
    (hγ : γ ∈ shiftedTeichCoset p 0) (a : ZMod (p ^ 2)) :
    heilbronnLevelWeight p P (γ * a) = heilbronnLevelWeight p P a := by
  classical
  have hz : γ * a ≠ 0 ↔ a ≠ 0 := by
    constructor
    · intro h ha
      exact h (ha ▸ mul_zero γ)
    · intro h ha
      exact h ((isUnit_of_mem_heilbronn hγ).mul_left_cancel (ha.trans (mul_zero γ).symm))
  simp only [heilbronnLevelWeight, mem_heilbronnCorrelationLevel, hz, correlation_mul_heilbronn hγ]

/-- The pair mass of a selected weight is exactly the sum of squared
correlations on its level set. Partition the pair sum by difference and
restrict the support. This supplies the retained energy B for B²E≤t³Q. -/
theorem heilbronnLevelWeight_pair_mass {p : ℕ} [Fact p.Prime] (P : ℕ → Prop) :
    (∑ x : heilbronnElements p,
        ∑ y : heilbronnElements p, heilbronnLevelWeight p P (x.val - y.val)) =
      ∑ a ∈ heilbronnCorrelationLevel p P, Nat.card (cosetDifferenceAt p 0 0 a) ^ 2 := by
  classical
  have hpairs :
    (∑ x : heilbronnElements p,
        ∑ y : heilbronnElements p, heilbronnLevelWeight p P (x.val - y.val)) =
      ∑ x ∈ heilbronnElements p, ∑ y ∈ heilbronnElements p, heilbronnLevelWeight p P (x - y) := by
    rw [Finset.sum_coe_sort (heilbronnElements p)
        (fun x ↦ ∑ y : heilbronnElements p, heilbronnLevelWeight p P (x - y.val))]
    apply Finset.sum_congr rfl
    intro x _
    exact Finset.sum_coe_sort (heilbronnElements p) (fun y ↦ heilbronnLevelWeight p P (x - y))
  rw [hpairs, PseudoPrime.Analysis.finite_pair_sum_eq_correlation]
  simp only [← heilbronn_correlation_eq_finiteDifferenceCorrelation, heilbronnLevelWeight, ite_mul,
    zero_mul, ← pow_two, Finset.sum_ite_mem, Finset.univ_inter]

end PseudoPrime.NumberTheory.Heilbronn
