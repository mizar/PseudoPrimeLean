/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Nat.Choose.Bounds

/-! # Squarefree prime products in small modular subgroups -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Equal products of finite sets of primes have equal supports. Prime divisibility
and primality identify each factor. Used to distinguish squarefree products in counting. -/
theorem prime_finset_product_injective {S T : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p)
    (hT : ∀ p ∈ T, Nat.Prime p) (he : S.prod id = T.prod id) : S = T := by
  have hsub :
    ∀ (U V : Finset ℕ),
      (∀ p ∈ U, Nat.Prime p) → (∀ p ∈ V, Nat.Prime p) → U.prod id = V.prod id → U ⊆ V := by
    intro U V hU hV hprod p hp
    have hd : p ∣ V.prod id := hprod ▸ Finset.dvd_prod_of_mem id hp
    obtain ⟨r, hr, hpr⟩ := (hU p hp).prime.dvd_finsetProd_iff id |>.mp hd
    exact ((hV r hr).dvd_iff_eq (hU p hp).ne_one).mp hpr ▸ hr
  exact Finset.Subset.antisymm (hsub S T hS hT he) (hsub T S hT hS he.symm)

/-- If every factor has a unit representative in H, so does its product.
Multiply the representatives and use subgroup closure. Supplies the counting map. -/
theorem residue_subgroup_product {q : ℕ} (H : Subgroup (ZMod q)ˣ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q)) :
    ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (S.prod id : ℕ) := by
  classical
    induction S using Finset.induction_on with
  | empty => exact ⟨1, H.one_mem, by simp only [Units.val_one, Finset.prod_empty, Nat.cast_one]⟩
  | @insert p S hp ih =>
    obtain ⟨u, hu, he⟩ := hS p (Finset.mem_insert_self p S)
    obtain ⟨v, hv, hf⟩ := ih (fun r hr ↦ hS r (Finset.mem_insert_of_mem hr))
    refine ⟨u * v, H.mul_mem hu hv, ?_⟩
    rw [Units.val_mul, he, hf, Finset.prod_insert hp, Nat.cast_mul]
    rfl

/-- Suppose S contains primes at most B, all represented in H, and B^k < q.
Then choose(card S,k) is at most card H. Distinct k-subsets have distinct products
below q, hence distinct residues. No analytic or GRH assumption is used. -/
theorem choose_le_card_subgroup_of_prime_products {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (S : Finset ℕ) (k B : ℕ) (hprime : ∀ p ∈ S, Nat.Prime p) (hbound : ∀ p ∈ S, p ≤ B)
    (hsize : B ^ k < q) (hmem : ∀ p ∈ S, ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q)) :
    Nat.choose S.card k ≤ Nat.card H := by
  classical
  let : Fintype H := Fintype.ofFinite H
  have hex (T : ↥(S.powersetCard k)) :
    ∃ u : H, ((u : (ZMod q)ˣ) : ZMod q) = (T.val.prod id : ℕ) := by
    obtain ⟨u, hu, he⟩ :=
      residue_subgroup_product H T.val
        (fun p hp ↦ hmem p ((Finset.mem_powersetCard.mp T.property).1 hp))
    exact ⟨⟨u, hu⟩, he⟩
  choose f hf using hex
  have hlt (T : ↥(S.powersetCard k)) : T.val.prod id < q := by
    have hb :=
      Finset.prod_le_prod (fun p hp ↦ hbound p ((Finset.mem_powersetCard.mp T.property).1 hp))
    rw [Finset.prod_const, (Finset.mem_powersetCard.mp T.property).2] at hb
    exact hb.trans_lt hsize
  have hinj : Function.Injective f := by
    intro T U he
    apply Subtype.ext
    apply
      prime_finset_product_injective
        (fun p hp ↦ hprime p ((Finset.mem_powersetCard.mp T.property).1 hp))
        (fun p hp ↦ hprime p ((Finset.mem_powersetCard.mp U.property).1 hp))
    have hz : ((T.val.prod id : ℕ) : ZMod q) = ((U.val.prod id : ℕ) : ZMod q) :=
      (hf T).symm.trans ((congrArg (fun u : H ↦ ((u : (ZMod q)ˣ) : ZMod q)) he).trans (hf U))
    have hv := congrArg ZMod.val hz
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (hlt T), Nat.mod_eq_of_lt (hlt U)] using hv
  have hc := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe, Finset.card_powersetCard, Nat.card_eq_fintype_card] using hc

/-- If B^k < q and choose(card S,k) > card H for primes S bounded by B,
some member of S has no representative in H. Contradict the product-count bound.
Coprimality is not imposed, so a prime divisor of q can also be returned. -/
theorem exists_prime_outside_of_card_lt_choose {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (S : Finset ℕ) (k B : ℕ) (hprime : ∀ p ∈ S, Nat.Prime p) (hbound : ∀ p ∈ S, p ≤ B)
    (hsize : B ^ k < q) (hcount : Nat.card H < Nat.choose S.card k) :
    ∃ p ∈ S, Nat.Prime p ∧ p ≤ B ∧ ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  classical
  by_contra h
  apply Nat.not_le_of_gt hcount
  apply choose_le_card_subgroup_of_prime_products H S k B hprime hbound hsize
  intro p hp
  by_contra hm
  exact h ⟨p, hp, hprime p hp, hbound p hp, hm⟩

/-- The elementary power lower bound for a binomial coefficient, with no division.
Bound the descending factorial below and k! above by k^k. Used to turn analytic
prime-count estimates into a subgroup-size contradiction. -/
theorem choose_power_lower (M k : ℕ) : (M + 1 - k) ^ k ≤ k ^ k * Nat.choose M k := by
  calc
    (M + 1 - k) ^ k ≤ M.descFactorial k := Nat.pow_sub_le_descFactorial M k
    _ = k.factorial * Nat.choose M k := Nat.descFactorial_eq_factorial_mul_choose M k
    _ ≤ k ^ k * Nat.choose M k := Nat.mul_le_mul_right (Nat.choose M k) (Nat.factorial_le_pow k)

/-- A strict power budget C*k^k < (M+1-k)^k implies C < choose(M,k).
Contradict the preceding lower bound. This avoids evaluating a large binomial
coefficient when applying the prime-product witness criterion. -/
theorem card_lt_choose_of_power_budget {C M k : ℕ} (h : C * k ^ k < (M + 1 - k) ^ k) :
    C < Nat.choose M k := by
  by_contra hn
  have hc : Nat.choose M k ≤ C := Nat.le_of_not_gt hn
  have hb := (choose_power_lower M k).trans (Nat.mul_le_mul_left (k ^ k) hc)
  rw [Nat.mul_comm C] at h
  exact Nat.not_lt_of_ge hb h

end PseudoPrime.NumberTheory
