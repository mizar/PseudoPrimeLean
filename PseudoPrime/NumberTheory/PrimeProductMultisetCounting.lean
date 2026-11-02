/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.RingTheory.UniqueFactorizationDomain.Nat
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.Data.Sym.Card

/-! # Products of prime multisets modulo an integer -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Equal products of multisets of primes have the same factors, including
multiplicity. Recover each multiset by normalized prime factorization. This
provides injectivity for prime-product counting with repeated factors. -/
theorem prime_multiset_prod_injective {s t : Multiset ℕ} (hs : ∀ p ∈ s, Nat.Prime p)
    (ht : ∀ p ∈ t, Nat.Prime p) (h : s.prod = t.prod) : s = t := by
  calc
    s = UniqueFactorizationMonoid.normalizedFactors s.prod :=
      (UniqueFactorizationMonoid.normalizedFactors_prod_of_prime (fun p hp ↦ (hs p hp).prime)).symm
    _ = UniqueFactorizationMonoid.normalizedFactors t.prod := congrArg _ h
    _ = t := UniqueFactorizationMonoid.normalizedFactors_prod_of_prime (fun p hp ↦ (ht p hp).prime)

/-- Prime multisets whose products are below the modulus are equal when their
products have equal residues. Recover the natural products from their residues,
then apply unique factorization. This supplies the injection into a residue subgroup. -/
theorem prime_multiset_prod_mod_injective {q : ℕ} [NeZero q] {s t : Multiset ℕ}
    (hs : ∀ p ∈ s, Nat.Prime p) (ht : ∀ p ∈ t, Nat.Prime p) (hsq : s.prod < q) (htq : t.prod < q)
    (h : (s.prod : ZMod q) = (t.prod : ZMod q)) : s = t := by
  have he : s.prod = t.prod := by
    have hv := congrArg ZMod.val h
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hsq, Nat.mod_eq_of_lt htq] using hv
  exact prime_multiset_prod_injective hs ht he

/-- Two equally sized multisets padded with ones agree if their prime parts
have products below the modulus and equal residues. Unique factorization fixes
the prime parts, and the common length fixes the number of padding ones. This
is the injection needed for counting products with at most `k` prime factors. -/
theorem padded_prime_prod_mod_injective {q k : ℕ} [NeZero q] {s t : Sym ℕ k}
    (hs : ∀ p ∈ ((s.filterNe 1).2 : Multiset ℕ), Nat.Prime p)
    (ht : ∀ p ∈ ((t.filterNe 1).2 : Multiset ℕ), Nat.Prime p)
    (hsq : ((s.filterNe 1).2 : Multiset ℕ).prod < q)
    (htq : ((t.filterNe 1).2 : Multiset ℕ).prod < q)
    (h :
      ((((s.filterNe 1).2 : Multiset ℕ).prod : ℕ) : ZMod q) =
        ((((t.filterNe 1).2 : Multiset ℕ).prod : ℕ) : ZMod q)) :
    s = t := by
  have hm := prime_multiset_prod_mod_injective hs ht hsq htq h
  have he : s.filterNe 1 = t.filterNe 1 := Sym.sigma_sub_ext hm
  calc
    s = (s.filterNe 1).2.fill 1 (s.filterNe 1).1 := (Sym.fill_filterNe 1 s).symm
    _ = (t.filterNe 1).2.fill 1 (t.filterNe 1).1 := congrArg (fun x ↦ x.2.fill 1 x.1) he
    _ = t := Sym.fill_filterNe 1 t

/-- An injective encoding of padded prime multisets whose products lie below
the modulus and have representatives in `H` gives the multichoose lower bound
on `H`. Count the encoded multisets and use residue injectivity. The hypotheses
allow callers to construct the padding and subgroup representatives separately. -/
theorem multichoose_le_card_subgroup_of_encoding {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (S : Finset ℕ) (k : ℕ) (g : Sym (Option ↥S) k → Sym ℕ k) (hg : Function.Injective g)
    (hp : ∀ s, ∀ p ∈ (((g s).filterNe 1).2 : Multiset ℕ), Nat.Prime p)
    (hl : ∀ s, (((g s).filterNe 1).2 : Multiset ℕ).prod < q)
    (hm :
      ∀ s, ∃ u : H, ((u : (ZMod q)ˣ) : ZMod q) = ((((g s).filterNe 1).2 : Multiset ℕ).prod : ℕ)) :
    Nat.choose (S.card + k) k ≤ Nat.card H := by
  classical
  let : Fintype H := Fintype.ofFinite H
  choose f hf using hm
  have hinj : Function.Injective f := by
    intro s t he
    apply hg
    apply padded_prime_prod_mod_injective (hp s) (hp t) (hl s) (hl t)
    exact (hf s).symm.trans ((congrArg (fun u : H ↦ ((u : (ZMod q)ˣ) : ZMod q)) he).trans (hf t))
  have h := Fintype.card_le_of_injective f hinj
  rw [Sym.card_sym_eq_choose, Fintype.card_option, Fintype.card_coe, Nat.add_right_comm S.card 1 k,
    Nat.add_sub_cancel] at h
  simpa only [Nat.card_eq_fintype_card] using h

/-- Every member of the non-padding part of a multiset encoded from `S` is
an element of `S`. Removing ones excludes the padding case. This transfers prime,
size, and subgroup hypotheses from `S` to the counted products. -/
theorem mem_of_padded_prime_part (S : Finset ℕ) {k p : ℕ} (s : Sym (Option ↥S) k)
    (h : p ∈ (((s.map (fun x ↦ x.elim 1 Subtype.val)).filterNe 1).2 : Multiset ℕ)) : p ∈ S := by
  have hf : p ∈ ((s.map (fun x ↦ x.elim 1 Subtype.val)) : Multiset ℕ) ∧ 1 ≠ p :=
    Multiset.mem_filter.mp h
  obtain ⟨x, hx, he⟩ := Sym.mem_map.mp (Sym.mem_coe.mp hf.1)
  cases x with
  | none => exact False.elim (hf.2 he)
  | some x =>
    change (x : ℕ) = p at he
    exact he ▸ x.property

/-- The product of a multiset whose members have representatives in `H` has
a representative in `H`. Induction multiplies the representatives; this works
with repeated factors and includes the empty product. -/
theorem multiset_prod_mem_subgroup {q : ℕ} (H : Subgroup (ZMod q)ˣ) (s : Multiset ℕ)
    (hs : ∀ p ∈ s, ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q)) :
    ∃ u : H, ((u : (ZMod q)ˣ) : ZMod q) = (s.prod : ℕ) := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨⟨1, H.one_mem⟩, by simp only [Multiset.prod_zero, Units.val_one, Nat.cast_one]⟩
  | @cons p s ih =>
    obtain ⟨u, hu, he⟩ := hs p (Multiset.mem_cons_self p s)
    obtain ⟨v, hv⟩ := ih (fun r hr ↦ hs r (Multiset.mem_cons_of_mem hr))
    refine ⟨⟨u * (v : (ZMod q)ˣ), H.mul_mem hu v.property⟩, ?_⟩
    rw [Units.val_mul, he, hv, Multiset.prod_cons, Nat.cast_mul]

/-- If all primes in `S` are at most `B` and have representatives in `H`,
and `B ^ k < q`, then the number of products with at most `k` factors is at
most `card H`. Pad with ones, bound each product, and use the counting injection.
This is the repeated-prime counterpart of squarefree subgroup counting. -/
theorem multichoose_le_card_subgroup {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) (S : Finset ℕ)
    (k B : ℕ) (hB : 1 ≤ B) (hp : ∀ p ∈ S, Nat.Prime p) (hb : ∀ p ∈ S, p ≤ B) (hsize : B ^ k < q)
    (hm : ∀ p ∈ S, ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q)) :
    Nat.choose (S.card + k) k ≤ Nat.card H := by
  classical
  let f : Option ↥S → ℕ := fun x ↦ x.elim 1 Subtype.val
  have hf : Function.Injective f := by
    intro x y h
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y => exact False.elim ((hp y y.property).ne_one h.symm)
    | some x =>
      cases y with
      | none => exact False.elim ((hp x x.property).ne_one h)
      | some y => exact congrArg some (Subtype.ext h)
  apply multichoose_le_card_subgroup_of_encoding H S k (fun s ↦ s.map f) (Sym.map_injective hf k)
  · intro s p h
    exact hp p (mem_of_padded_prime_part S s h)
  · intro s
    let m := (((s.map f).filterNe 1).2 : Multiset ℕ)
    have hbound : ∀ p ∈ m, p ≤ B := fun p h ↦ hb p (mem_of_padded_prime_part S s h)
    have hc : m.card ≤ k := by
      exact (Multiset.card_le_card (Multiset.filter_le _ _)).trans_eq (s.map f).2
    exact ((Multiset.prod_le_pow_card m B hbound).trans (Nat.pow_le_pow_right hB hc)).trans_lt hsize
  · intro s
    apply multiset_prod_mem_subgroup H
    intro p h
    exact hm p (mem_of_padded_prime_part S s h)

/-- If the multichoose count exceeds `card H`, at least one prime in `S` has
no representative in `H`. Contradict the preceding subgroup count; no coprimality
assumption is needed. This supplies a small prime outside a local kernel. -/
theorem exists_prime_outside_of_multichoose {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (S : Finset ℕ) (k B : ℕ) (hB : 1 ≤ B) (hp : ∀ p ∈ S, Nat.Prime p) (hb : ∀ p ∈ S, p ≤ B)
    (hsize : B ^ k < q) (hcount : Nat.card H < Nat.choose (S.card + k) k) :
    ∃ p ∈ S, Nat.Prime p ∧ p ≤ B ∧ ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  classical
  by_contra h
  apply Nat.not_le_of_gt hcount
  apply multichoose_le_card_subgroup H S k B hB hp hb hsize
  intro p hmem
  by_contra hn
  exact h ⟨p, hmem, hp p hmem, hb p hmem, hn⟩

end PseudoPrime.NumberTheory
