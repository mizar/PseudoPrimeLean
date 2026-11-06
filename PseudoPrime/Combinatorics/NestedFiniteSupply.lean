/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Basic

/-! # Extending finite supplies without subtracting lower bounds -/

@[expose] public section

namespace PseudoPrime.Combinatorics

/-- If `A ⊆ B` and the requested cardinality lies between their cardinalities,
there is an intermediate finite set of exactly that size. Choose the missing
elements from `B \ A`; this supports nested prime supplies without inferring
an interval count by subtracting two lower bounds. -/
theorem exists_intermediate_card {α : Type*} (A B : Finset α) (m : ℕ) (hAB : A ⊆ B)
    (hlo : A.card ≤ m) (hhi : m ≤ B.card) : ∃ C : Finset α, A ⊆ C ∧ C ⊆ B ∧ C.card = m := by
  classical
  have hcard : (B \ A).card = B.card - A.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAB]
  have hdiff : m - A.card ≤ (B \ A).card := by
    rw [hcard]
    exact Nat.sub_le_sub_right hhi _
  obtain ⟨D, hD, hDcard⟩ := Finset.exists_subset_card_eq hdiff
  have hdis : Disjoint A D := Finset.disjoint_of_subset_right hD Finset.disjoint_sdiff
  refine
    ⟨A ∪ D, Finset.subset_union_left, Finset.union_subset hAB (hD.trans Finset.sdiff_subset), ?_⟩
  rw [Finset.card_union_of_disjoint hdis, hDcard, Nat.add_comm, Nat.sub_add_cancel hlo]

/-- Monotone finite supplies and monotone requested cardinalities admit nested
subsets of exactly those sizes whenever each supply is large enough. Each
successor extends the previous choice inside the next supply. -/
theorem exists_nested_supply {α : Type*} (B : ℕ → Finset α) (m : ℕ → ℕ) (hB : Monotone B)
    (hm : Monotone m) (hs : ∀ i, m i ≤ (B i).card) :
    ∃ S : ℕ → Finset α, Monotone S ∧ ∀ i, S i ⊆ B i ∧ (S i).card = m i := by
  classical
  let step (i : ℕ) (A : Finset α) : Finset α :=
    if h : A ⊆ B (i + 1) ∧ A.card ≤ m (i + 1) then
      Classical.choose (exists_intermediate_card A (B (i + 1)) (m (i + 1)) h.1 h.2 (hs (i + 1)))
    else ∅
  let S : ℕ → Finset α := Nat.rec (Classical.choose (Finset.exists_subset_card_eq (hs 0))) step
  have hbase : S 0 ⊆ B 0 ∧ (S 0).card = m 0 :=
    Classical.choose_spec (Finset.exists_subset_card_eq (hs 0))
  have hstep (i : ℕ) (h : S i ⊆ B i ∧ (S i).card = m i) :
    S i ⊆ S (i + 1) ∧ S (i + 1) ⊆ B (i + 1) ∧ (S (i + 1)).card = m (i + 1) := by
    have hp : S i ⊆ B (i + 1) ∧ (S i).card ≤ m (i + 1) :=
      ⟨h.1.trans (hB (Nat.le_succ i)), h.2 ▸ hm (Nat.le_succ i)⟩
    change S i ⊆ step i (S i) ∧ step i (S i) ⊆ B (i + 1) ∧ (step i (S i)).card = m (i + 1)
    dsimp only [step]
    rw [dite_eq_left hp]
    exact
      Classical.choose_spec
        (exists_intermediate_card (S i) (B (i + 1)) (m (i + 1)) hp.1 hp.2 (hs (i + 1)))
  have hall : ∀ i, S i ⊆ B i ∧ (S i).card = m i := by
    intro i
    induction i with
    | zero => exact hbase
    | succ i ih => exact (hstep i ih).2
  exact ⟨S, monotone_nat_of_le_succ (fun i ↦ (hstep i (hall i)).1), hall⟩

/-- Successive differences of nested finite sets are pairwise disjoint.
The earlier difference is contained in the later set's excluded prefix. -/
theorem nested_differences_disjoint {α : Type*} [DecidableEq α] (S : ℕ → Finset α) (hS : Monotone S)
    {i j : ℕ} (hij : i < j) : Disjoint (S (i + 1) \ S i) (S (j + 1) \ S j) := by
  exact
    Finset.disjoint_of_subset_left (Finset.sdiff_subset.trans (hS (Nat.succ_le_of_lt hij)))
      Finset.disjoint_sdiff

/-- The cardinality of a successive difference equals the difference of the
exact selected cardinalities. This does not subtract prime-count lower bounds. -/
theorem nested_difference_card {α : Type*} [DecidableEq α] (S : ℕ → Finset α) (hS : Monotone S)
    (m : ℕ → ℕ) (hm : ∀ i, (S i).card = m i) (i : ℕ) :
    (S (i + 1) \ S i).card = m (i + 1) - m i := by
  rw [Finset.card_sdiff_of_subset (hS (Nat.le_succ i)), hm, hm]

end PseudoPrime.Combinatorics
