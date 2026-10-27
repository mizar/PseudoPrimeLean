/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Finite counting bounds for occurrence maps -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/--
Inputs: finite source and target sets, a map sending every source element into the target, and a
uniform upper bound for the map's fibers.
Claim: the source cardinality is at most the target cardinality times the fiber bound.
Proof: cover the source by the fibers over the target, use the cardinality bound for finite unions,
and sum the fiber bounds.
Role: supplies the combinatorial incidence estimate needed to retain multiplicity when zero
occurrences are mapped to finitely many derivative-detection events.
-/
theorem card_le_card_mul_of_fiber_bound {α β : Type*} [DecidableEq β] (s : Finset α) (t : Finset β)
    (f : α → β) (B : ℕ) (hmap : ∀ x ∈ s, f x ∈ t)
    (hfiber : ∀ y ∈ t, (s.filter fun x => f x = y).card ≤ B) : s.card ≤ t.card * B := by
  classical
    calc
    s.card ≤ (t.biUnion fun y => s.filter fun x => f x = y).card := by
      apply Finset.card_le_card
      intro x hx
      exact Finset.mem_biUnion.mpr ⟨f x, hmap x hx, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
    _ ≤ ∑ y ∈ t, (s.filter fun x => f x = y).card := Finset.card_biUnion_le
    _ ≤ ∑ y ∈ t, B := Finset.sum_le_sum fun y hy => hfiber y hy
    _ = t.card * B := by
      apply Finset.sum_const_nat
      intro y hy
      rfl

/--
Inputs: finite sets of occurrences and windows, a Boolean incidence relation, a lower bound for
the number of windows meeting each occurrence, and an upper bound for the occurrences meeting
each window.

Claim: the occurrence count times the minimum incidence per occurrence is at most the window
count times the maximum incidence per window.

Proof: count the finite set of incident occurrence-window pairs by each coordinate.

Role: transfers multiplicity-preserving zero-window incidence into an integrated family estimate.
-/
theorem card_mul_le_card_mul_of_incidence {α β : Type*} (s : Finset α) (t : Finset β)
    (inc : α → β → Bool) (L U : ℕ) (hlower : ∀ a ∈ s, L ≤ (t.filter fun b => inc a b = true).card)
    (hupper : ∀ b ∈ t, (s.filter fun a => inc a b = true).card ≤ U) : s.card * L ≤ t.card * U := by
  classical
  let r : Finset (α × β) := (s ×ˢ t).filter fun p => inc p.1 p.2 = true
  have hleftCard (a : α) (ha : a ∈ s) :
    (t.filter fun b => inc a b = true).card = (r.filter fun p => p.1 = a).card := by
    apply Finset.card_bij (fun b _ => (a, b))
    · intro b hb
      rcases Finset.mem_filter.mp hb with ⟨hb, hinc⟩
      have hr : (a, b) ∈ r := by
        dsimp only [r]
        rw [Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨ha, hb⟩, hinc⟩
      exact Finset.mem_filter.mpr ⟨hr, rfl⟩
    · intro b₁ hb₁ b₂ hb₂ heq
      exact congrArg Prod.snd heq
    · intro p hp
      have hpr : p ∈ r := (Finset.mem_filter.mp hp).1
      dsimp only [r] at hpr
      obtain ⟨hprod, hinter⟩ := Finset.mem_filter.mp hpr
      obtain ⟨ha', hb'⟩ := Finset.mem_product.mp hprod
      refine ⟨p.2, Finset.mem_filter.mpr ⟨hb', ?_⟩, Prod.ext (Finset.mem_filter.mp hp).2.symm rfl⟩
      simpa only [(Finset.mem_filter.mp hp).2] using hinter
  have hrightCard (b : β) (hb : b ∈ t) :
    (s.filter fun a => inc a b = true).card = (r.filter fun p => p.2 = b).card := by
    apply Finset.card_bij (fun a _ => (a, b))
    · intro a ha
      rcases Finset.mem_filter.mp ha with ⟨ha, hinc⟩
      have hr : (a, b) ∈ r := by
        dsimp only [r]
        rw [Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨ha, hb⟩, hinc⟩
      exact Finset.mem_filter.mpr ⟨hr, rfl⟩
    · intro a₁ ha₁ a₂ ha₂ heq
      exact congrArg Prod.fst heq
    · intro p hp
      have hpr : p ∈ r := (Finset.mem_filter.mp hp).1
      dsimp only [r] at hpr
      obtain ⟨hprod, hinter⟩ := Finset.mem_filter.mp hpr
      obtain ⟨ha', hb'⟩ := Finset.mem_product.mp hprod
      refine ⟨p.1, Finset.mem_filter.mpr ⟨ha', ?_⟩, Prod.ext rfl (Finset.mem_filter.mp hp).2.symm⟩
      simpa only [(Finset.mem_filter.mp hp).2] using hinter
  have hleftSum : (∑ a ∈ s, (t.filter fun b => inc a b = true).card) = r.card := by
    calc
      _ = ∑ a ∈ s, (r.filter fun p => p.1 = a).card := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hleftCard a ha
      _ = (r.filter fun p => p.1 ∈ s).card := Finset.sum_card_fiberwise_eq_card_filter r s Prod.fst
      _ = r.card := by
        congr 1
        apply Finset.filter_eq_self.mpr
        intro p hp
        dsimp only [r] at hp
        exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  have hrightSum : (∑ b ∈ t, (s.filter fun a => inc a b = true).card) = r.card := by
    calc
      _ = ∑ b ∈ t, (r.filter fun p => p.2 = b).card := by
        apply Finset.sum_congr rfl
        intro b hb
        exact hrightCard b hb
      _ = (r.filter fun p => p.2 ∈ t).card := Finset.sum_card_fiberwise_eq_card_filter r t Prod.snd
      _ = r.card := by
        congr 1
        apply Finset.filter_eq_self.mpr
        intro p hp
        dsimp only [r] at hp
        exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
  calc
    s.card * L ≤ ∑ a ∈ s, (t.filter fun b => inc a b = true).card := by
      calc
        _ = ∑ a ∈ s, L := by
          symm
          apply Finset.sum_const_nat
          intro a ha
          rfl
        _ ≤ _ := Finset.sum_le_sum fun a ha => hlower a ha
    _ = r.card := hleftSum
    _ = ∑ b ∈ t, (s.filter fun a => inc a b = true).card := hrightSum.symm
    _ ≤ t.card * U := by
      calc
        _ ≤ ∑ b ∈ t, U := Finset.sum_le_sum fun b hb => hupper b hb
        _ = t.card * U := by
          apply Finset.sum_const_nat
          intro b hb
          rfl

/--
Inputs: finite sets of occurrences and windows, a Boolean incidence relation, a lower bound for
the incidence count of every occurrence, and a pointwise upper bound for each window fiber.
Claim: the occurrence count times its minimum incidence is at most the sum of the window-fiber
bounds.
Proof: count incident pairs by their occurrence and window coordinates, then apply the supplied
pointwise upper bounds.
Role: keeps conductor- and height-dependent local multiplicity bounds inside the window sum
instead of replacing them with an unproved global maximum.
-/
theorem card_mul_le_sum_window_fiber_bounds {α β : Type*} (s : Finset α) (t : Finset β)
    (inc : α → β → Bool) (L : ℕ) (fiberBound : β → ℕ)
    (hlower : ∀ a ∈ s, L ≤ (t.filter fun b => inc a b = true).card)
    (hupper : ∀ b ∈ t, (s.filter fun a => inc a b = true).card ≤ fiberBound b) :
    s.card * L ≤ ∑ b ∈ t, fiberBound b := by
  classical
  let r : Finset (α × β) := (s ×ˢ t).filter fun p => inc p.1 p.2 = true
  have hleftCard (a : α) (ha : a ∈ s) :
    (t.filter fun b => inc a b = true).card = (r.filter fun p => p.1 = a).card := by
    apply Finset.card_bij (fun b _ => (a, b))
    · intro b hb
      rcases Finset.mem_filter.mp hb with ⟨hb, hinc⟩
      have hr : (a, b) ∈ r := by
        dsimp only [r]
        rw [Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨ha, hb⟩, hinc⟩
      exact Finset.mem_filter.mpr ⟨hr, rfl⟩
    · intro b₁ hb₁ b₂ hb₂ heq
      exact congrArg Prod.snd heq
    · intro p hp
      have hpr : p ∈ r := (Finset.mem_filter.mp hp).1
      dsimp only [r] at hpr
      obtain ⟨hprod, hinter⟩ := Finset.mem_filter.mp hpr
      obtain ⟨ha', hb'⟩ := Finset.mem_product.mp hprod
      refine ⟨p.2, Finset.mem_filter.mpr ⟨hb', ?_⟩, Prod.ext (Finset.mem_filter.mp hp).2.symm rfl⟩
      simpa only [(Finset.mem_filter.mp hp).2] using hinter
  have hrightCard (b : β) (hb : b ∈ t) :
    (s.filter fun a => inc a b = true).card = (r.filter fun p => p.2 = b).card := by
    apply Finset.card_bij (fun a _ => (a, b))
    · intro a ha
      rcases Finset.mem_filter.mp ha with ⟨ha, hinc⟩
      have hr : (a, b) ∈ r := by
        dsimp only [r]
        rw [Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨ha, hb⟩, hinc⟩
      exact Finset.mem_filter.mpr ⟨hr, rfl⟩
    · intro a₁ ha₁ a₂ ha₂ heq
      exact congrArg Prod.fst heq
    · intro p hp
      have hpr : p ∈ r := (Finset.mem_filter.mp hp).1
      dsimp only [r] at hpr
      obtain ⟨hprod, hinter⟩ := Finset.mem_filter.mp hpr
      obtain ⟨ha', hb'⟩ := Finset.mem_product.mp hprod
      refine ⟨p.1, Finset.mem_filter.mpr ⟨ha', ?_⟩, Prod.ext rfl (Finset.mem_filter.mp hp).2.symm⟩
      simpa only [(Finset.mem_filter.mp hp).2] using hinter
  have hleftSum : (∑ a ∈ s, (t.filter fun b => inc a b = true).card) = r.card := by
    calc
      _ = ∑ a ∈ s, (r.filter fun p => p.1 = a).card := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hleftCard a ha
      _ = (r.filter fun p => p.1 ∈ s).card := Finset.sum_card_fiberwise_eq_card_filter r s Prod.fst
      _ = r.card := by
        congr 1
        apply Finset.filter_eq_self.mpr
        intro p hp
        dsimp only [r] at hp
        exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  have hrightSum : (∑ b ∈ t, (s.filter fun a => inc a b = true).card) = r.card := by
    calc
      _ = ∑ b ∈ t, (r.filter fun p => p.2 = b).card := by
        apply Finset.sum_congr rfl
        intro b hb
        exact hrightCard b hb
      _ = (r.filter fun p => p.2 ∈ t).card := Finset.sum_card_fiberwise_eq_card_filter r t Prod.snd
      _ = r.card := by
        congr 1
        apply Finset.filter_eq_self.mpr
        intro p hp
        dsimp only [r] at hp
        exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
  calc
    s.card * L ≤ ∑ a ∈ s, (t.filter fun b => inc a b = true).card := by
      calc
        _ = ∑ a ∈ s, L := by
          symm
          apply Finset.sum_const_nat
          intro a ha
          rfl
        _ ≤ _ := Finset.sum_le_sum fun a ha => hlower a ha
    _ = r.card := hleftSum
    _ = ∑ b ∈ t, (s.filter fun a => inc a b = true).card := hrightSum.symm
    _ ≤ ∑ b ∈ t, fiberBound b := Finset.sum_le_sum fun b hb => hupper b hb

/-- If every nonempty finite fiber activates one event in a bounded order range,
its cardinality is at most its cardinality bound times the number of active orders.
Use one active order in the nonempty case and the zero cardinality otherwise.
This turns local multiplicity bounds into detector-event incidence bounds. -/
theorem card_le_bound_mul_order_event_sum {α : Type*} (s : Finset α) (B nmax : ℕ) (event : ℕ → Prop)
    [DecidablePred event] (hbound : s.card ≤ B) (hactivate : s.Nonempty → ∃ n ≤ nmax, event n) :
    s.card ≤ B * (∑ n ∈ Finset.range (nmax + 1), if event n then 1 else 0) := by
  by_cases hs : s.Nonempty
  · obtain ⟨n, hn, hevent⟩ := hactivate hs
    have hsum :=
      Finset.single_le_sum (s := Finset.range (nmax + 1)) (f := fun k ↦
        if event k then (1 : ℕ) else 0) (fun k hk ↦ Nat.zero_le _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
    rw [ite_eq_left hevent] at hsum
    exact hbound.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left B hsum)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.card_empty]
    exact Nat.zero_le _

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
