/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.PrimeProductFamilyCounting

/-! # Signed prime-product families modulo an integer -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Two positive natural numbers whose sum is below the modulus have
distinct residues after one is negated. Otherwise their positive sum would
be a nonzero multiple of the modulus smaller than that modulus. -/
theorem natCast_ne_neg_of_add_lt {q a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a + b < q) :
    (a : ZMod q) ≠ -(b : ZMod q) := by
  intro he
  have hz : ((a + b : ℕ) : ZMod q) = 0 := by rw [Nat.cast_add, he, neg_add_cancel]
  have hd : q ∣ a + b := (ZMod.natCast_eq_zero_iff (a + b) q).mp hz
  exact (Nat.not_dvd_of_pos_of_lt (add_pos ha hb) hab) hd

/-- If a subgroup contains minus one and every prime in a finite supply,
then a prime-multiset family whose products are less than half the modulus
contributes twice its cardinality to the subgroup. Positive and negative
products are individually injective and cannot collide with each other. -/
theorem signed_prime_family_le_card {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) (S : Finset ℕ)
    (F : Finset (Multiset ℕ)) (hneg : (-1 : (ZMod q)ˣ) ∈ H) (hsub : ∀ T ∈ F, ∀ p ∈ T, p ∈ S)
    (hprime : ∀ p ∈ S, Nat.Prime p) (hsize : ∀ T ∈ F, 2 * T.prod < q)
    (hmem : ∀ p ∈ S, ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q)) :
    2 * F.card ≤ Nat.card H := by
  classical
  let : Fintype H := Fintype.ofFinite H
  have hex (T : ↥F) : ∃ u : H, ((u : (ZMod q)ˣ) : ZMod q) = (T.val.prod : ℕ) :=
    multiset_prod_mem_subgroup H T.val (fun p hp ↦ hmem p (hsub T T.property p hp))
  choose f hf using hex
  let g : Bool × ↥F → H := fun z ↦
    if z.1 then f z.2
    else
      ⟨-((f z.2 : H) : (ZMod q)ˣ), by
        simpa only [neg_one_mul] using H.mul_mem hneg (f z.2).property⟩
  have hg (b : Bool) (T : ↥F) :
    ((g (b, T) : H) : (ZMod q)ˣ) = if b then (f T : (ZMod q)ˣ) else -(f T : (ZMod q)ˣ) := by
    cases b <;> rfl
  have hpos (T : ↥F) : 0 < T.val.prod :=
    Multiset.prod_pos (fun p hp ↦ (hprime p (hsub T T.property p hp)).pos)
  have hsmall (T : ↥F) : T.val.prod < q := by
    have h := hsize T T.property
    omega
  have hinj : Function.Injective g := by
    rintro ⟨b, T⟩ ⟨c, U⟩ he
    have hv := congrArg (fun z : H ↦ ((z : (ZMod q)ˣ) : ZMod q)) he
    have hv' :
      (if b then (T.val.prod : ZMod q) else -(T.val.prod : ZMod q)) =
        if c then (U.val.prod : ZMod q) else -(U.val.prod : ZMod q) := by
      cases b <;> cases c <;>
        simpa only [hg, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, Units.val_neg, hf] using
          hv
    have hsum : T.val.prod + U.val.prod < q := by
      have ht := hsize T T.property
      have hu := hsize U U.property
      omega
    cases b <;> cases c
    · have heq : (T.val.prod : ZMod q) = (U.val.prod : ZMod q) := by
        simpa only [Bool.false_eq_true, ↓reduceIte, neg_inj] using hv'
      have hTU :=
        prime_multiset_prod_mod_injective (fun p hp ↦ hprime p (hsub T T.property p hp))
          (fun p hp ↦ hprime p (hsub U U.property p hp)) (hsmall T) (hsmall U) heq
      cases Subtype.ext hTU
      rfl
    · have hne :=
        natCast_ne_neg_of_add_lt (hpos U) (hpos T) (by omega : U.val.prod + T.val.prod < q)
      exact
        False.elim
          (hne (by simpa only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] using hv'.symm))
    · have hne := natCast_ne_neg_of_add_lt (hpos T) (hpos U) hsum
      exact
        False.elim
          (hne (by simpa only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] using hv'))
    · have heq : (T.val.prod : ZMod q) = (U.val.prod : ZMod q) := by
        simpa only [Bool.false_eq_true, ↓reduceIte] using hv'
      have hTU :=
        prime_multiset_prod_mod_injective (fun p hp ↦ hprime p (hsub T T.property p hp))
          (fun p hp ↦ hprime p (hsub U U.property p hp)) (hsmall T) (hsmall U) heq
      cases Subtype.ext hTU
      rfl
  have hc := Fintype.card_le_of_injective g hinj
  simpa only [Fintype.card_prod, Fintype.card_bool, Fintype.card_coe,
    Nat.card_eq_fintype_card] using hc

/-- If a subgroup contains representatives of all primes up to `B`, then
it also contains a representative of every positive integer at most `B`.
Prime factorization and closure under products provide the representative. -/
theorem small_nat_mem_subgroup {q B m : ℕ} (H : Subgroup (ZMod q)ˣ) (hm : 0 < m) (hmB : m ≤ B)
    (hmem : ∀ p : ℕ, p.Prime → p ≤ B → ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q)) :
    ∃ u : H, ((u : (ZMod q)ˣ) : ZMod q) = (m : ZMod q) := by
  let T : Multiset ℕ := m.primeFactorsList
  have hT : ∀ p ∈ T, ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
    intro p hp
    have hp' : p ∈ m.primeFactorsList := hp
    exact
      hmem p (Nat.prime_of_mem_primeFactorsList hp')
        ((Nat.le_of_mem_primeFactorsList hp').trans hmB)
  obtain ⟨u, hu⟩ := multiset_prod_mem_subgroup H T hT
  refine ⟨u, ?_⟩
  simpa only [T, Multiset.prod_coe, Nat.prod_primeFactorsList (Nat.ne_of_gt hm)] using hu

end PseudoPrime.NumberTheory
