/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.OffDiagonalMixedEnergy

/-! # Exact diagonal separation for amplified Heilbronn triples -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- The full triple sum splits into its exact y=z contribution and the
off-diagonal sum. The diagonal is (p-1) times the g²-weighted correlation
mass. Isolate one summation term and group the remaining pair sum by its
difference. No estimate or discarded contribution is hidden in this identity. -/
theorem weightedHeilbronnTriple_eq_diagonal_add_offDiagonal {p : ℕ} [Fact p.Prime]
    (g : ZMod (p ^ 2) → ℕ) :
    weightedHeilbronnTriple p g =
      (p - 1) * (∑ a : ZMod (p ^ 2), g a ^ 2 * Nat.card (cosetDifferenceAt p 0 0 a)) +
        weightedHeilbronnOffDiagonal p g := by
  classical
  have hs (x y : heilbronnElements p) :=
    Finset.sum_ite (s := Finset.univ) (p := fun z : heilbronnElements p ↦ y = z)
      (fun z ↦
        g (x.val - y.val) * g (x.val - z.val) * Nat.card (cosetDifferenceAt p 0 0 (y.val - z.val)))
      (fun z ↦
        g (x.val - y.val) * g (x.val - z.val) * Nat.card (cosetDifferenceAt p 0 0 (y.val - z.val)))
  simp only [ite_self, Finset.sum_filter, Finset.sum_ite_eq, Finset.mem_univ, ite_true, ite_not,
    sub_self, card_cosetDifferenceAt_zero, ← pow_two] at hs
  have h :=
    Finset.sum_congr rfl
      (fun x (_ : x ∈ (Finset.univ : Finset (heilbronnElements p))) ↦
        Finset.sum_congr rfl
          (fun y (_ : y ∈ (Finset.univ : Finset (heilbronnElements p))) ↦ hs x y))
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul] at h
  rw [PseudoPrime.Analysis.finite_subtype_pair_sum_eq_correlation (heilbronnElements p)
      (fun a ↦ g a ^ 2)] at h
  simpa only [weightedHeilbronnTriple, weightedHeilbronnOffDiagonal,
    ← heilbronn_correlation_eq_finiteDifferenceCorrelation, mul_comm (p - 1)] using h

/-- On a selected level of height at most Δ, the diagonal moment of g²
is at most Δ times the retained energy B. Expand the support and compare
each r³ with Δr². This bounds the diagonal by (p-1)ΔB in amplification. -/
theorem level_weight_diagonal_moment_le {p : ℕ} [Fact p.Prime] (P : ℕ → Prop) (Δ : ℕ)
    (hP : ∀ v, P v → v ≤ Δ) :
    (∑ a : ZMod (p ^ 2), heilbronnLevelWeight p P a ^ 2 * Nat.card (cosetDifferenceAt p 0 0 a)) ≤
      Δ * heilbronnLevelEnergy p P := by
  classical
  simp only [heilbronnLevelWeight, ite_pow, zero_pow (by decide : 2 ≠ 0), ite_mul, zero_mul,
    Finset.sum_ite_mem, Finset.univ_inter, heilbronnLevelEnergy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have hv := hP _ ((mem_heilbronnCorrelationLevel P a).mp ha).2
  have h := Nat.mul_le_mul_right (Nat.card (cosetDifferenceAt p 0 0 a) ^ 2) hv
  simpa only [mul_comm] using h

/-- A selected weight of height at most Δ has total triple sum at most
(p-1)ΔB plus its actual off-diagonal sum. Combine the exact split with the
pointwise diagonal estimate. The off-diagonal term can now be controlled
by the independently proved mixed third-energy inequality. -/
theorem level_weight_triple_le_diagonal_add_offDiagonal {p : ℕ} [Fact p.Prime] (P : ℕ → Prop)
    (Δ : ℕ) (hP : ∀ v, P v → v ≤ Δ) :
    weightedHeilbronnTriple p (heilbronnLevelWeight p P) ≤
      (p - 1) * Δ * heilbronnLevelEnergy p P +
        weightedHeilbronnOffDiagonal p (heilbronnLevelWeight p P) := by
  rw [weightedHeilbronnTriple_eq_diagonal_add_offDiagonal]
  have h :=
    Nat.add_le_add_right
      (Nat.mul_le_mul_left (p - 1) (level_weight_diagonal_moment_le (p := p) P Δ hP))
      (weightedHeilbronnOffDiagonal p (heilbronnLevelWeight p P))
  simpa only [mul_assoc] using h

end PseudoPrime.NumberTheory.Heilbronn
