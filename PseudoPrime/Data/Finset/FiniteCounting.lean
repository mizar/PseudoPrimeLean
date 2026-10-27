/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # Finite counting

Finite sum and fiber-counting lemmas used by analytic number theory modules.
-/

@[expose] public section

namespace PseudoPrime.Data.Finset

/--
Inputs: a finite index set `s`, a natural-valued function on its indices, and a
threshold `T`.

Claim: if the sum of the values exceeds `s.card * T`, then some index has value
strictly greater than `T`.

Content: this is the finite averaging step that turns a lower bound on total
incidences into a lower bound for one parameter choice.

Proof: compare the sum with the constant function `T`, then apply
`Finset.exists_lt_of_sum_lt`.

Role: this records the pigeonhole step used when averaging divisor-indexed
prime counts over the parameter `k` in the AGP source argument.
-/
theorem exists_index_with_value_gt_of_sum_gt_card_mul {ι : Type} (s : Finset ι) (f : ι → ℕ) (T : ℕ)
    (h : s.card * T < ∑ i ∈ s, f i) : ∃ i ∈ s, T < f i := by
  have hsum : (∑ i ∈ s, T) < ∑ i ∈ s, f i := by
    rw [Finset.sum_const_nat (s := s) (m := T) (f := fun _ => T) (fun _ _ => rfl)]
    exact h
  exact Finset.exists_lt_of_sum_lt hsum

/--
Inputs: a nonempty finite set, a map from its elements to a finite codomain,
and an upper bound `m` for the codomain cardinality.

Claim: some fiber has cardinality greater than `(S.card - 1) / m`.

Proof: apply finite pigeonhole counting with threshold `(S.card - 1) / m`.

Role: supplies finite counting arguments that repeatedly select a large fiber.
-/
theorem exists_fiber_card_gt_div_of_card_le {α β : Type} [Fintype β] [DecidableEq β] (S : Finset α)
    (f : α → β) (m : ℕ) (hcard : Fintype.card β ≤ m) (hS : 0 < S.card) :
    ∃ y : β, (S.filter fun x => f x = y).card > (S.card - 1) / m := by
  classical
  have hprod : Fintype.card β * ((S.card - 1) / m) < S.card := by
    calc
      Fintype.card β * ((S.card - 1) / m) ≤ m * ((S.card - 1) / m) := Nat.mul_le_mul_right _ hcard
      _ ≤ S.card - 1 := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self (S.card - 1) m
      _ < S.card := Nat.sub_lt hS (by decide)
  obtain ⟨y, hy, hfiber⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (s := S) (t := Finset.univ) (f := f) (n :=
      (S.card - 1) / m)
      (by
        intro x hx; exact Finset.mem_univ _)
      (by simpa only [Finset.card_univ, Fintype.card_coe] using hprod)
  exact ⟨y, hfiber⟩

/--
Inputs: a nonempty finite set, a map to a finite codomain of cardinality at
most `m`, and the integer `m`.

Claim: some fiber removes at least `(S.card - 1) / m + 1` elements.

Proof: partition `S` into that fiber and its complement.

Role: gives the additive form of the finite fiber contraction bound.
-/
theorem exists_fiber_complement_card_le {α β : Type} [Fintype β] [DecidableEq β] (S : Finset α)
    (f : α → β) (m : ℕ) (hcard : Fintype.card β ≤ m) (hS : 0 < S.card) :
    ∃ y : β, ((S.card - 1) / m + 1) + (S.filter fun x => f x ≠ y).card ≤ S.card := by
  classical
  obtain ⟨y, hfiber⟩ := exists_fiber_card_gt_div_of_card_le S f m hcard hS
  have hcomp : (S.filter fun x => f x = y).card + (S.filter fun x => f x ≠ y).card = S.card := by
    rw [Finset.card_filter_add_card_filter_not]
  have hlarge : (S.card - 1) / m + 1 ≤ (S.filter fun x => f x = y).card := Nat.succ_le_of_lt hfiber
  refine ⟨y, ?_⟩
  calc
    ((S.card - 1) / m + 1) + (S.filter fun x => f x ≠ y).card ≤
        (S.filter fun x => f x = y).card + (S.filter fun x => f x ≠ y).card :=
      Nat.add_le_add_right hlarge _
    _ = S.card := hcomp

/--
Inputs: a nonempty finite set, a map to a finite codomain of size at most `m`,
and a positive integer `m`.

Claim: some value leaves a complement satisfying
`m * complement ≤ (m - 1) * S.card`.

Proof: convert the preceding fiber bound to a product inequality.

Role: gives the multiplicative form of the finite fiber contraction bound.
-/
theorem exists_fiber_complement_mul_card_le {α β : Type} [Fintype β] [DecidableEq β] (S : Finset α)
    (f : α → β) (m : ℕ) (hm : 0 < m) (hcard : Fintype.card β ≤ m) (hS : 0 < S.card) :
    ∃ y : β, m * (S.filter fun x => f x ≠ y).card ≤ (m - 1) * S.card := by
  classical
  obtain ⟨y, hy⟩ := exists_fiber_complement_card_le S f m hcard hS
  refine ⟨y, ?_⟩
  have hceil : S.card ≤ m * ((S.card - 1) / m + 1) := by
    have hdiv := Nat.div_add_mod (S.card - 1) m
    have hmod := Nat.mod_lt (S.card - 1) hm
    rw [Nat.mul_add]
    omega
  have hmul := Nat.mul_le_mul_left m hy
  simp only [Nat.mul_add] at hmul
  have hmdecomp : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm))
  have hrhs : m * S.card = (m - 1) * S.card + S.card := by
    calc
      m * S.card = (m - 1 + 1) * S.card := by rw [hmdecomp]
      _ = (m - 1) * S.card + S.card := by rw [Nat.add_mul, Nat.one_mul]
  rw [hrhs] at hmul
  have hceil' : S.card ≤ m * ((S.card - 1) / m) + m := by
    calc
      S.card ≤ m * ((S.card - 1) / m + 1) := hceil
      _ = m * ((S.card - 1) / m) + m := by rw [Nat.mul_add, Nat.mul_one]
  omega

/--
Inputs: finite index sets `D` and `K`, and a relation `R` on pairs from their
product.

Claim: counting the pairs satisfying `R` by their `K` coordinate gives the
same total as counting them by their `D` coordinate.

Content: this is the finite double-counting identity for the incidence set
`{(d, k) | R d k}`.

Proof: sum the cardinalities of the fibers of each coordinate projection; each
sum equals the cardinality of the same filtered product.

Role: this converts the sum over divisors in the prime-pair argument into a
sum over candidate values of `k`, where the finite averaging lemma can be
applied.
-/
theorem sum_fiber_card_eq_sum_fiber_card_product {α β : Type} [DecidableEq α] [DecidableEq β]
    (D : Finset α) (K : Finset β) (R : α → β → Prop) [DecidablePred (fun z : α × β => R z.1 z.2)] :
    let S := (D.product K).filter (fun z => R z.1 z.2)
    (∑ k ∈ K, (S.filter (fun z => z.2 = k)).card) =
      ∑ d ∈ D, (S.filter (fun z => z.1 = d)).card := by
  classical
  dsimp only
  let S := (D.product K).filter (fun z => R z.1 z.2)
  have hfilterSnd : S.filter (fun z => z.2 ∈ K) = S := by
    apply Finset.filter_eq_self.mpr
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    exact (Finset.mem_product.mp hz'.1).2
  have hfilterFst : S.filter (fun z => z.1 ∈ D) = S := by
    apply Finset.filter_eq_self.mpr
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    exact (Finset.mem_product.mp hz'.1).1
  have hsumSnd : (∑ k ∈ K, (S.filter (fun z => z.2 = k)).card) = S.card := by
    calc
      _ = (S.filter (fun z => z.2 ∈ K)).card :=
        Finset.sum_card_fiberwise_eq_card_filter S K Prod.snd
      _ = S.card := by rw [hfilterSnd]
  have hsumFst : (∑ d ∈ D, (S.filter (fun z => z.1 = d)).card) = S.card := by
    calc
      _ = (S.filter (fun z => z.1 ∈ D)).card :=
        Finset.sum_card_fiberwise_eq_card_filter S D Prod.fst
      _ = S.card := by rw [hfilterFst]
  exact hsumSnd.trans hsumFst.symm

/--
Inputs: finite sets `D` and `K`, a relation `R` on their product, and an index
`k ∈ K`.

Claim: the number of related pairs with second coordinate `k` equals the
number of elements `d ∈ D` satisfying `R d k`.

Content: fixing the second coordinate makes the first-coordinate projection
injective, and every related `d` determines the pair `(d, k)`.

Proof: identify the image of the pair fiber under `Prod.fst` with the filtered
set of related `d`, then use the finite-set image-cardinality theorem.

Role: this reads the large fiber produced by the averaging theorem as the
number of divisors producing primes for the selected `k`.
-/
theorem card_pair_fiber_eq_card_left {α β : Type} [DecidableEq β] (D : Finset α) (K : Finset β)
    (k : β) (R : α → β → Prop) [DecidablePred (fun z : α × β => R z.1 z.2)]
    [DecidablePred (fun d : α => R d k)] (hk : k ∈ K) :
    let S := (D.product K).filter (fun z => R z.1 z.2)
    (S.filter (fun z => z.2 = k)).card = (D.filter (fun d => R d k)).card := by
  classical
  dsimp only
  let S := (D.product K).filter (fun z => R z.1 z.2)
  let F := S.filter (fun z => z.2 = k)
  have himage : F.image Prod.fst = D.filter (fun d => R d k) := by
    ext d
    constructor
    · intro h
      rcases Finset.mem_image.mp h with ⟨z, hz, hfst⟩
      have hzF := Finset.mem_filter.mp hz
      have hzS := Finset.mem_filter.mp hzF.1
      have hzProd := Finset.mem_product.mp hzS.1
      cases z with
      | mk zd zk =>
        have hzk : zk = k := hzF.2
        change zd = d at hfst
        subst zd
        subst zk
        apply Finset.mem_filter.mpr
        exact ⟨hzProd.1, hzS.2⟩
    · intro h
      have hdR := Finset.mem_filter.mp h
      rw [Finset.mem_image]
      refine ⟨(d, k), ?_, rfl⟩
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_product.mpr ⟨hdR.1, hk⟩
        · exact hdR.2
      · rfl
  have hInj : (F : Set (α × β)).InjOn Prod.fst := by
    intro z hz w hw hfst
    have hzK := (Finset.mem_filter.mp (Finset.mem_coe.mp hz)).2
    have hwK := (Finset.mem_filter.mp (Finset.mem_coe.mp hw)).2
    cases z with
    | mk zd zk =>
      cases w with
      | mk wd wk =>
        change zd = wd at hfst
        have hzk : zk = k := hzK
        have hwk : wk = k := hwK
        subst wd
        subst zk
        subst wk
        rfl
  calc
    F.card = (F.image Prod.fst).card := (Finset.card_image_of_injOn hInj).symm
    _ = (D.filter (fun d => R d k)).card := congrArg Finset.card himage

/--
Inputs: finite sets `D` and `K`, a relation on their product, and a threshold
`T`.

Claim: if the sum of the left-coordinate fiber sizes exceeds `K.card * T`,
then some right-coordinate fiber has size greater than `T`.

Proof: exchange the two fiber sums using double counting, then average over
`K`.

Role: this is the general finite relation-counting step used by the AGP
progression argument.
-/
theorem exists_right_fiber_gt_of_left_fiber_sum_gt {α β : Type} [DecidableEq α] [DecidableEq β]
    (D : Finset α) (K : Finset β) (R : α → β → Prop) [DecidablePred (fun z : α × β => R z.1 z.2)]
    (T : ℕ) :
    let S := (D.product K).filter (fun z => R z.1 z.2)
    K.card * T < (∑ d ∈ D, (S.filter (fun z => z.1 = d)).card) →
      ∃ k ∈ K, T < (S.filter (fun z => z.2 = k)).card := by
  classical
  dsimp only
  intro h
  have hdouble := sum_fiber_card_eq_sum_fiber_card_product D K R
  rw [← hdouble] at h
  exact
    exists_index_with_value_gt_of_sum_gt_card_mul K
      (fun k => ((D.product K).filter (fun z => R z.1 z.2) |>.filter (fun z => z.2 = k)).card) T h

end PseudoPrime.Data.Finset
