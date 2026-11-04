/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Combinatorics.SubsetWeightBounds
public import PseudoPrime.NumberTheory.PrimeProductSubgroupCounting
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Selected prime products in modular subgroups

Count an arbitrary family of prime subsets whose products are below the modulus. This permits
selection by the total logarithmic weight without imposing a uniform bound on every product.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Let `F` be a family of subsets of a finite prime set `S`, each with product below `q`.
If every prime in `S` is represented in `H`, then `F.card ≤ Nat.card H`. Unique
factorization and the product bound make the subgroup map injective. This supports counting
selected products without a uniform `B ^ k` bound. -/
theorem selected_prime_products_le_card {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) (S : Finset ℕ)
    (F : Finset (Finset ℕ)) (hsub : ∀ T ∈ F, T ⊆ S) (hprime : ∀ p ∈ S, Nat.Prime p)
    (hsize : ∀ T ∈ F, T.prod id < q)
    (hmem : ∀ p ∈ S, ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q)) :
    F.card ≤ Nat.card H := by
  classical
  let : Fintype H := Fintype.ofFinite H
  have hex (T : ↥F) : ∃ u : H, ((u : (ZMod q)ˣ) : ZMod q) = (T.val.prod id : ℕ) := by
    obtain ⟨u, hu, he⟩ :=
      residue_subgroup_product H T.val (fun p hp ↦ hmem p (hsub T T.property hp))
    exact ⟨⟨u, hu⟩, he⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro T U he
    apply Subtype.ext
    apply
      prime_finset_product_injective (fun p hp ↦ hprime p (hsub T T.property hp))
        (fun p hp ↦ hprime p (hsub U U.property hp))
    have hz : ((T.val.prod id : ℕ) : ZMod q) = ((U.val.prod id : ℕ) : ZMod q) :=
      (hf T).symm.trans ((congrArg (fun u : H ↦ ((u : (ZMod q)ˣ) : ZMod q)) he).trans (hf U))
    have hv := congrArg ZMod.val hz
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (hsize T T.property),
      Nat.mod_eq_of_lt (hsize U U.property)] using hv
  have hc := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe, Nat.card_eq_fintype_card] using hc

/-- Suppose `S` is a finite set of primes represented in `H`, `1 ≤ k`, and
`0 ≤ τ ≤ log q`. If the total prime logarithm satisfies the displayed average bound with
margin `δ`, then `δ * choose (card S) k ≤ τ * card H`. Select subsets below the logarithmic
threshold and inject their products into `H`. This is the average-logarithm counting bound. -/
theorem weighted_prime_products_le_card {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) (S : Finset ℕ)
    (k : ℕ) (τ δ : ℝ) (hk : 1 ≤ k) (hτ : 0 ≤ τ) (hq : τ ≤ Real.log q) (hp : ∀ p ∈ S, Nat.Prime p)
    (havg :
      (Nat.choose (S.card - 1) (k - 1) : ℝ) * (∑ p ∈ S, Real.log p) ≤ (τ - δ) * Nat.choose S.card k)
    (hm : ∀ p ∈ S, ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q)) :
    δ * Nat.choose S.card k ≤ τ * Nat.card H := by
  classical
  let F := (S.powersetCard k).filter fun T : Finset ℕ ↦ (∑ p ∈ T, Real.log p) < τ
  have hsel :=
    Combinatorics.card_powersetCard_weight_lt S (fun p : ℕ ↦ Real.log p) τ δ hk
      (fun p _ ↦ Real.log_natCast_nonneg p) havg
  have hsub : ∀ T ∈ F, T ⊆ S := by
    intro T hT
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).1
  have hsize : ∀ T ∈ F, T.prod id < q := by
    intro T hT
    have hnonzero : ∀ p ∈ T, (p : ℝ) ≠ 0 := by
      intro p hpT
      exact Nat.cast_ne_zero.mpr (hp p (hsub T hT hpT)).ne_zero
    have hlog : Real.log ((T.prod id : ℕ) : ℝ) = ∑ p ∈ T, Real.log p := by
      rw [Nat.cast_prod]
      dsimp only [id]
      exact Real.log_prod hnonzero
    have hpos : 0 < ((T.prod id : ℕ) : ℝ) := by
      rw [Nat.cast_prod]
      exact Finset.prod_pos (fun p hpT ↦ Nat.cast_pos.mpr (hp p (hsub T hT hpT)).pos)
    have hqpos : 0 < (q : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
    have hlt : ((T.prod id : ℕ) : ℝ) < q := by
      apply (Real.log_lt_log_iff hpos hqpos).mp
      rw [hlog]
      exact (Finset.mem_filter.mp hT).2.trans_le hq
    exact_mod_cast hlt
  have hc := selected_prime_products_le_card H S F hsub hp hsize hm
  have hc' : (F.card : ℝ) ≤ Nat.card H := by exact_mod_cast hc
  exact hsel.trans (mul_le_mul_of_nonneg_left hc' hτ)

/-- Under the average-logarithm bound, if `δ * choose (card S) k` exceeds
`τ * card H`, some prime in `S` has no representative in `H`. Otherwise the preceding
subgroup count contradicts the strict inequality. This turns the counting budget into a
prime outside the subgroup. -/
theorem exists_prime_outside_of_weight {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) (S : Finset ℕ)
    (k : ℕ) (τ δ : ℝ) (hk : 1 ≤ k) (hτ : 0 ≤ τ) (hq : τ ≤ Real.log q) (hp : ∀ p ∈ S, Nat.Prime p)
    (havg :
      (Nat.choose (S.card - 1) (k - 1) : ℝ) * (∑ p ∈ S, Real.log p) ≤ (τ - δ) * Nat.choose S.card k)
    (hcount : τ * Nat.card H < δ * Nat.choose S.card k) :
    ∃ p ∈ S, ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  classical
  by_contra h
  have hm : ∀ p ∈ S, ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
    intro p hpS
    by_contra hn
    exact h ⟨p, hpS, hn⟩
  exact (not_le_of_gt hcount) (weighted_prime_products_le_card H S k τ δ hk hτ hq hp havg hm)

/-- For a nonempty finite set of primes, a mean logarithmic weight at most `τ - δ`
and a selected-product count exceeding `card H` force a prime outside `H`.
The binomial identity converts the mean condition to the preceding counting criterion.
This form accepts prime-count and Chebyshev bounds without choosing an arbitrary subset. -/
theorem exists_prime_outside_of_mean {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) (S : Finset ℕ)
    (k : ℕ) (τ δ : ℝ) (hk : 1 ≤ k) (hs : 1 ≤ S.card) (hτ : 0 ≤ τ) (hq : τ ≤ Real.log q)
    (hp : ∀ p ∈ S, Nat.Prime p) (hmean : (k : ℝ) * (∑ p ∈ S, Real.log p) ≤ (τ - δ) * S.card)
    (hcount : τ * Nat.card H < δ * Nat.choose S.card k) :
    ∃ p ∈ S, ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  exact
    exists_prime_outside_of_weight H S k τ δ hk hτ hq hp
      (Combinatorics.choose_weight_of_mean S.card k _ τ δ hk hs hmean) hcount

end PseudoPrime.NumberTheory
