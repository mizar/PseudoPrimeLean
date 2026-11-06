/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.PrimeProductFamilyCounting

/-! # Weighted multiset families for Miller–Rabin count certificates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If every factor has positive integer weight, the number of factors in a
multiset is at most its total weight. Repeated factors are counted with their
multiplicities, so a budget also bounds the padding length. -/
theorem multiset_card_le_weight (T : Multiset ℕ) (w : ℕ → ℕ) (hw : ∀ p ∈ T, 1 ≤ w p) :
    T.card ≤ (T.map w).sum := by
  induction T using Multiset.induction_on with
  | empty => simp only [Multiset.card_zero, Multiset.map_zero, Multiset.sum_zero, le_refl]
  | @cons p T ih =>
    have hp := hw p (Multiset.mem_cons_self p T)
    have ht := ih (fun q hq ↦ hw q (Multiset.mem_cons_of_mem hq))
    simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons]
    exact (Nat.add_le_add ht hp).trans_eq (Nat.add_comm _ _)

/-- The finite family of multisets selected from a supply by an integer weight
budget. The finite ambient multiset contains `H` copies of each supplied
element; positive weights ensure this bound does not omit any admissible
multiset. The family provides a semantic target for the counting algorithm. -/
noncomputable def weightedPrimeFamily (S : Finset ℕ) (w : ℕ → ℕ) (H : ℕ) : Finset (Multiset ℕ) := by
  classical
    exact
    (S.val.bind (fun p ↦ Multiset.replicate H p)).powerset.toFinset.filter
      (fun T ↦ (T.map w).sum ≤ H)

/-- For positive weights on the supply, membership in the finite weighted
family is equivalent to support in the supply and total cost at most `H`.
The budget bounds every multiplicity, so the ambient powerset is exhaustive. -/
theorem mem_weightedPrimeFamily (S : Finset ℕ) (w : ℕ → ℕ) (H : ℕ) (hw : ∀ p ∈ S, 1 ≤ w p)
    (T : Multiset ℕ) : T ∈ weightedPrimeFamily S w H ↔ (∀ p ∈ T, p ∈ S) ∧ (T.map w).sum ≤ H := by
  classical
  have hcount (a : ℕ) :
    Multiset.count a (S.val.bind (fun p ↦ Multiset.replicate H p)) = if a ∈ S then H else 0 := by
    rw [Multiset.count_bind]
    change (∑ p ∈ S, Multiset.count a (Multiset.replicate H p)) = _
    simp only [Multiset.count_replicate]
    exact Finset.sum_ite_eq' S a (fun _ ↦ H)
  simp only [weightedPrimeFamily, Finset.mem_filter, Multiset.mem_toFinset, Multiset.mem_powerset]
  constructor
  · intro ⟨hle, hcost⟩
    refine ⟨?_, hcost⟩
    intro p hp
    have hc : 0 < Multiset.count p T := Multiset.count_pos.mpr hp
    have hh := (Multiset.le_iff_count.mp hle) p
    rw [hcount] at hh
    by_contra h
    simp only [h, ite_false] at hh
    exact (Nat.not_lt_zero _) (hc.trans_le hh)
  · intro ⟨hsub, hcost⟩
    refine ⟨Multiset.le_iff_count.mpr ?_, hcost⟩
    intro p
    rw [hcount]
    by_cases hp : p ∈ S
    · simp only [hp, ite_true]
      exact
        (Multiset.count_le_card p T).trans
          ((multiset_card_le_weight T w (fun q hq ↦ hw q (hsub q hq))).trans hcost)
    · simp only [hp, ite_false]
      exact Nat.eq_zero_of_not_pos (fun h ↦ hp (hsub p (Multiset.count_pos.mp h))) |>.le

/-- Adding a supplied element of weight at most the budget is equivalent to
reducing the budget by its weight. This is the membership-level step for
the repeated-factor counting recurrence. -/
theorem cons_mem_weightedPrimeFamily (S : Finset ℕ) (w : ℕ → ℕ) (H p : ℕ) (hp : p ∈ S)
    (hw : ∀ a ∈ S, 1 ≤ w a) (hH : w p ≤ H) (T : Multiset ℕ) :
    p ::ₘ T ∈ weightedPrimeFamily S w H ↔ T ∈ weightedPrimeFamily S w (H - w p) := by
  rw [mem_weightedPrimeFamily S w H hw, mem_weightedPrimeFamily S w (H - w p) hw]
  simp only [Multiset.mem_cons, Multiset.map_cons, Multiset.sum_cons]
  constructor
  · intro ⟨hsub, hcost⟩
    refine ⟨fun a ha ↦ hsub a (Or.inr ha), ?_⟩
    exact (Nat.le_sub_iff_add_le' hH).mpr hcost
  · intro ⟨hsub, hcost⟩
    refine ⟨?_, (Nat.le_sub_iff_add_le' hH).mp hcost⟩
    intro a ha
    rcases ha with he | he
    · exact he ▸ hp
    · exact hsub a he

/-- When a supplied element's weight fits the budget, weighted multisets
containing it are equinumerous with the whole family at the reduced budget.
Removing one occurrence and adding it back provide inverse maps. -/
theorem weightedPrimeFamily_card_contains (S : Finset ℕ) (w : ℕ → ℕ) (H p : ℕ) (hp : p ∈ S)
    (hw : ∀ a ∈ S, 1 ≤ w a) (hH : w p ≤ H) :
    ((weightedPrimeFamily S w H).filter fun T ↦ p ∈ T).card =
      (weightedPrimeFamily S w (H - w p)).card := by
  classical
  have heq :
    (weightedPrimeFamily S w H).filter (fun T ↦ p ∈ T) =
      (weightedPrimeFamily S w (H - w p)).image (fun T ↦ p ::ₘ T) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · intro ⟨hT, hpT⟩
      refine ⟨T.erase p, ?_, Multiset.cons_erase hpT⟩
      exact
        (cons_mem_weightedPrimeFamily S w H p hp hw hH _).mp ((Multiset.cons_erase hpT).symm ▸ hT)
    · rintro ⟨U, hU, rfl⟩
      exact ⟨(cons_mem_weightedPrimeFamily S w H p hp hw hH U).mpr hU, Multiset.mem_cons_self p U⟩
  rw [heq, Finset.card_image_of_injective]
  exact fun _ _ he ↦ (Multiset.cons_inj_right p).mp he

/-- Removing from the weighted family the multisets containing `p` gives
exactly the weighted family formed from the supply with `p` erased. This is
the zero-multiplicity branch of the counting recurrence. -/
theorem weightedPrimeFamily_filter_not (S : Finset ℕ) (w : ℕ → ℕ) (H p : ℕ)
    (hw : ∀ a ∈ S, 1 ≤ w a) :
    (weightedPrimeFamily S w H).filter (fun T ↦ p ∉ T) = weightedPrimeFamily (S.erase p) w H := by
  classical
  have hwe : ∀ a ∈ S.erase p, 1 ≤ w a := fun a ha ↦ hw a (Finset.mem_erase.mp ha).2
  ext T
  simp only [Finset.mem_filter, mem_weightedPrimeFamily S w H hw T,
    mem_weightedPrimeFamily (S.erase p) w H hwe T, Finset.mem_erase]
  constructor
  · rintro ⟨⟨hsub, hcost⟩, hn⟩
    refine ⟨?_, hcost⟩
    intro a ha
    exact ⟨fun he ↦ hn (he ▸ ha), hsub a ha⟩
  · rintro ⟨hsub, hcost⟩
    refine ⟨⟨fun a ha ↦ (hsub a ha).2, hcost⟩, ?_⟩
    intro hp
    exact (hsub p hp).1 rfl

/-- The positive-weight family obeys the unbounded-knapsack recurrence when
the selected element's weight fits the budget. Split on whether it occurs;
erasing one occurrence identifies the nonzero branch with the reduced budget. -/
theorem weightedPrimeFamily_card_step (S : Finset ℕ) (w : ℕ → ℕ) (H p : ℕ) (hp : p ∈ S)
    (hw : ∀ a ∈ S, 1 ≤ w a) (hH : w p ≤ H) :
    (weightedPrimeFamily S w H).card =
      (weightedPrimeFamily (S.erase p) w H).card + (weightedPrimeFamily S w (H - w p)).card := by
  classical
  have hs := Finset.card_filter_add_card_filter_not (s := weightedPrimeFamily S w H) (fun T ↦ p ∈ T)
  rw [weightedPrimeFamily_card_contains S w H p hp hw hH,
    weightedPrimeFamily_filter_not S w H p hw] at hs
  exact hs.symm.trans (Nat.add_comm _ _)

/-- When an element's weight exceeds the budget, no weighted multiset can
contain it, so deleting that element from the supply preserves the family.
This supplies the low-budget branch of the counting recurrence. -/
theorem weightedPrimeFamily_remove_heavy (S : Finset ℕ) (w : ℕ → ℕ) (H p : ℕ)
    (hw : ∀ a ∈ S, 1 ≤ w a) (hH : H < w p) :
    weightedPrimeFamily S w H = weightedPrimeFamily (S.erase p) w H := by
  classical
  have hfilter :
    (weightedPrimeFamily S w H).filter (fun T ↦ p ∉ T) = weightedPrimeFamily S w H := by
    apply Finset.filter_true_of_mem
    intro T hT hpT
    have hcost := ((mem_weightedPrimeFamily S w H hw T).mp hT).2
    have he := Multiset.cons_erase hpT
    rw [← he, Multiset.map_cons, Multiset.sum_cons] at hcost
    exact (not_le_of_gt hH) ((Nat.le_add_right _ _).trans hcost)
  exact hfilter.symm.trans (weightedPrimeFamily_filter_not S w H p hw)

/-- With an empty supply, the only admissible weighted multiset is the empty
multiset, independently of the budget. This is the base case for counting. -/
theorem weightedPrimeFamily_empty (w : ℕ → ℕ) (H : ℕ) : weightedPrimeFamily ∅ w H = {0} := by
  classical
  ext T
  have hw : ∀ p ∈ (∅ : Finset ℕ), 1 ≤ w p := fun _ hp ↦ (Finset.notMem_empty _ hp).elim
  rw [mem_weightedPrimeFamily ∅ w H hw T]
  simp only [Finset.mem_singleton, Finset.notMem_empty, imp_false]
  constructor
  · exact fun h ↦ Multiset.eq_zero_of_forall_notMem h.1
  · intro h
    subst T
    refine ⟨fun p ↦ Multiset.notMem_zero p, ?_⟩
    simp only [Multiset.map_zero, Multiset.sum_zero, Nat.zero_le]

end PseudoPrime.PrimeTestBounds.MillerRabin
