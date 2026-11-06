/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.PrimeProductMultisetCounting
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Counting arbitrary finite families of repeated prime products -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- A finite family of fixed-length multisets over the prime supply augmented
with a padding symbol encodes an equally large family of prime multisets.
Removing padding is injective because the original length is fixed and no
prime equals one. This supports selecting the family by a weight budget. -/
theorem exists_prime_family_of_padded (S : Finset ℕ) (k : ℕ) (G : Finset (Sym (Option ↥S) k))
    (hp : ∀ p ∈ S, Nat.Prime p) :
    ∃ F : Finset (Multiset ℕ),
      F.card = G.card ∧
        (∀ T ∈ F, ∀ p ∈ T, p ∈ S) ∧
        ∀ T ∈ F,
          ∃ t ∈ G, T = (((t.map (fun x ↦ x.elim 1 Subtype.val)).filterNe 1).2 : Multiset ℕ) := by
  classical
  let f : Option ↥S → ℕ := fun x ↦ x.elim 1 Subtype.val
  let g (t : Sym (Option ↥S) k) : Multiset ℕ := (((t.map f).filterNe 1).2 : Multiset ℕ)
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
  have hg : Function.Injective g := by
    intro x y he
    apply Sym.map_injective hf k
    have hm : (x.map f).filterNe 1 = (y.map f).filterNe 1 := Sym.sigma_sub_ext he
    exact
      ((Sym.fill_filterNe 1 (x.map f)).symm.trans
        ((congrArg (fun z ↦ z.2.fill 1 z.1) hm).trans (Sym.fill_filterNe 1 (y.map f))))
  refine ⟨G.image g, Finset.card_image_of_injective G hg, ?_, ?_⟩
  · intro T hT p hpT
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hT
    exact mem_of_padded_prime_part S t hpT
  · intro T hT
    obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hT
    exact ⟨t, ht, he.symm⟩

/-- The logarithm of a product of positive natural factors is bounded by the
sum of their integer weights divided by `d` when each weight bounds the
corresponding logarithm. Multiplicity is retained in the multiset sum. -/
theorem log_multiset_prod_le_weight (T : Multiset ℕ) (w : ℕ → ℕ) (d : ℝ) (hp : ∀ p ∈ T, 0 < p)
    (hw : ∀ p ∈ T, Real.log p ≤ (w p : ℝ) / d) :
    Real.log (T.prod : ℝ) ≤ ((T.map w).sum : ℝ) / d := by
  induction T using Multiset.induction_on with
  | empty =>
    simp only [Multiset.prod_zero, Nat.cast_one, Real.log_one, Multiset.map_zero, Multiset.sum_zero,
      Nat.cast_zero, zero_div, le_refl]
  | @cons p T ih =>
    have hp0 := hp p (Multiset.mem_cons_self p T)
    have hpT : ∀ q ∈ T, 0 < q := fun q hq ↦ hp q (Multiset.mem_cons_of_mem hq)
    have hwT : ∀ q ∈ T, Real.log q ≤ (w q : ℝ) / d := fun q hq ↦ hw q (Multiset.mem_cons_of_mem hq)
    have hprod : 0 < T.prod := Multiset.prod_pos hpT
    have h := ih hpT hwT
    have hw' := hw p (Multiset.mem_cons_self p T)
    simp only [Multiset.prod_cons, Nat.cast_mul, Multiset.map_cons, Multiset.sum_cons, Nat.cast_add]
    rw [Real.log_mul (Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hp0))
        (Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hprod)),
      add_div]
    exact add_le_add hw' h

/-- A multiset whose total integer weight is at most `H` has product below a
positive modulus whenever `H / d` is strictly below its logarithm. The
individual weight bounds may differ between primes and include repetitions. -/
theorem multiset_prod_lt_of_weight (T : Multiset ℕ) (w : ℕ → ℕ) (d : ℝ) (H q : ℕ) (hd : 0 < d)
    (hq : 0 < q) (hp : ∀ p ∈ T, 0 < p) (hw : ∀ p ∈ T, Real.log p ≤ (w p : ℝ) / d)
    (hcost : (T.map w).sum ≤ H) (hbudget : (H : ℝ) / d < Real.log q) : T.prod < q := by
  have hlog := log_multiset_prod_le_weight T w d hp hw
  have hcostR : ((T.map w).sum : ℝ) ≤ H := Nat.cast_le.mpr hcost
  have hqlog := hlog.trans_lt ((div_le_div_of_nonneg_right hcostR hd.le).trans_lt hbudget)
  have hprod : (0 : ℝ) < T.prod := Nat.cast_pos.mpr (Multiset.prod_pos hp)
  exact_mod_cast (Real.log_lt_log_iff hprod (Nat.cast_pos.mpr hq)).mp hqlog

/-- A finite family of prime multisets whose products are below `q` has at
most as many elements as a subgroup containing representatives of every prime
in the supply. Unique factorization and the product bound give injectivity.
This permits weight-selected families with repeated prime factors. -/
theorem prime_multiset_family_le_card {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) (S : Finset ℕ)
    (F : Finset (Multiset ℕ)) (hsub : ∀ T ∈ F, ∀ p ∈ T, p ∈ S) (hprime : ∀ p ∈ S, Nat.Prime p)
    (hsize : ∀ T ∈ F, T.prod < q)
    (hmem : ∀ p ∈ S, ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q)) :
    F.card ≤ Nat.card H := by
  classical
  let : Fintype H := Fintype.ofFinite H
  have hex (T : ↥F) : ∃ u : H, ((u : (ZMod q)ˣ) : ZMod q) = (T.val.prod : ℕ) :=
    multiset_prod_mem_subgroup H T.val (fun p hp ↦ hmem p (hsub T T.property p hp))
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro T U he
    apply Subtype.ext
    apply
      prime_multiset_prod_mod_injective (fun p hp ↦ hprime p (hsub T T.property p hp))
        (fun p hp ↦ hprime p (hsub U U.property p hp)) (hsize T T.property) (hsize U U.property)
    exact (hf T).symm.trans ((congrArg (fun u : H ↦ ((u : (ZMod q)ˣ) : ZMod q)) he).trans (hf U))
  have hc := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe, Nat.card_eq_fintype_card] using hc

end PseudoPrime.NumberTheory
