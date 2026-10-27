/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.AdditiveEnergy

/-! # Cubic tails of normalized Heilbronn correlations -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Ordered difference correlation of the Heilbronn subgroup at the principal unit
with parameter tau. Its normalized root sets are disjoint for distinct parameters. -/
noncomputable def normalizedCorrelation (p : ℕ) (τ : ZMod p) : ℕ :=
  Nat.card (cosetDifferencePairs p 0 0 τ)

/-- For odd prime p the total normalized correlation mass is at most p.
Use the disjoint truncated-log root sets and their union inside the residue field. -/
theorem sum_normalizedCorrelation_le {p : ℕ} [Fact p.Prime] (hodd : Odd p) :
    ∑ τ : ZMod p, normalizedCorrelation p τ ≤ p := by
  classical
  let roots : ZMod p → Finset (ZMod p) := fun τ ↦ (affineLogRoots p 0 0 τ).toFinset
  have hd : (Set.univ : Set (ZMod p)).PairwiseDisjoint roots := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact
      (Set.disjoint_left.mp (affineLogRoots_disjoint_of_same_cosets 0 0 a b hab))
        (Set.mem_toFinset.mp hx) (Set.mem_toFinset.mp hy)
  have he : (∑ τ : ZMod p, normalizedCorrelation p τ) = (Finset.univ.biUnion roots).card := by
    rw [Finset.card_biUnion (by simpa only [Finset.coe_univ] using hd)]
    apply Finset.sum_congr rfl
    intro τ hτ
    rw [normalizedCorrelation, card_cosetDifferencePairs_eq_affineLogRoots hodd,
      Nat.card_eq_fintype_card, ← Set.toFinset_card]
  rw [he]
  exact (Finset.card_le_univ _).trans_eq (ZMod.card p)

/-- For odd prime p, a nonempty finite parameter set S and positive t with
64*card(S)^2*t^3<=p, its correlation sum times t is at most 32t+4p.
Enumerate S by Fin(card S) and apply the proved family bound. -/
theorem sum_normalizedCorrelation_finset_scaled {p t : ℕ} [Fact p.Prime] (hodd : Odd p)
    (S : Finset (ZMod p)) (hs : 0 < S.card) (ht : 0 < t) (hsize : 64 * S.card ^ 2 * t ^ 3 ≤ p) :
    (∑ τ ∈ S, normalizedCorrelation p τ) * t ≤ 32 * t + 4 * p := by
  classical
  let e := S.equivFin.symm
  let τ : Fin S.card → ZMod p := fun k ↦ (e k).val
  have hinj : Function.Injective τ := by
    intro a b h
    exact e.injective (Subtype.ext h)
  have he :
    (∑ k : Fin S.card, normalizedCorrelation p (τ k)) = ∑ a ∈ S, normalizedCorrelation p a :=
    (e.sum_comp (fun a ↦ normalizedCorrelation p a.val)).trans (Finset.sum_coe_sort _ _)
  rw [← he]
  exact sum_card_cosetDifferencePairs_scaled hodd 0 0 τ hinj hs ht hsize

/-- For positive s and 64s^2<=p, choose positive t with
64s^2*t^3<=p<512s^2*t^3. Maximality and t+1<=2t give the bounds without enumeration. -/
theorem exists_weighted_cubic_scale {p s : ℕ} (hs : 0 < s) (hp : 64 * s ^ 2 ≤ p) :
    ∃ t : ℕ, 0 < t ∧ 64 * s ^ 2 * t ^ 3 ≤ p ∧ p < 512 * s ^ 2 * t ^ 3 := by
  let t := Nat.findGreatest (fun u ↦ 64 * s ^ 2 * u ^ 3 ≤ p) p
  have hs1 : 1 ≤ s := hs
  have hs2 : 1 ≤ s ^ 2 := Nat.one_le_pow 2 s hs1
  have hp64 : 64 ≤ p := (Nat.mul_le_mul_left 64 hs2).trans hp
  have hp1 : 1 ≤ p := (by decide : 1 ≤ 64).trans hp64
  have h1 : 64 * s ^ 2 * 1 ^ 3 ≤ p := by simpa only [one_pow, mul_one] using hp
  have ht1 : 1 ≤ t := Nat.le_findGreatest hp1 h1
  have hsize : 64 * s ^ 2 * t ^ 3 ≤ p :=
    Nat.findGreatest_spec (P := fun u ↦ 64 * s ^ 2 * u ^ 3 ≤ p) hp1 h1
  have htple : t ≤ p := Nat.findGreatest_le p
  have htp : t < p := by
    apply lt_of_le_of_ne htple
    intro he
    rw [he] at hsize
    have hp3 : p ≤ p ^ 3 := Nat.le_pow (by decide : 0 < 3)
    have hm := Nat.mul_le_mul_right (p ^ 3) (Nat.mul_le_mul_left 64 hs2)
    nlinarith only [hsize, hp3, hp64, hm]
  have hnext : p < 64 * s ^ 2 * (t + 1) ^ 3 :=
    Nat.lt_of_not_ge
      (Nat.findGreatest_is_greatest (P := fun u ↦ 64 * s ^ 2 * u ^ 3 ≤ p) (Nat.lt_succ_self t) htp)
  have ht2 : t + 1 ≤ 2 * t := by linarith only [ht1]
  have hpow := Nat.pow_le_pow_left ht2 3
  refine ⟨t, ht1, hsize, ?_⟩
  exact hnext.trans_le ((Nat.mul_le_mul_left (64 * s ^ 2) hpow).trans_eq (by ring))

/-- For odd prime p, if each parameter in S has correlation at least K,
then card(S)*K<=p. Compare with the proved total normalized mass. -/
theorem card_mul_le_of_normalizedCorrelation_ge {p K : ℕ} [Fact p.Prime] (hodd : Odd p)
    (S : Finset (ZMod p)) (hS : ∀ τ ∈ S, K ≤ normalizedCorrelation p τ) : S.card * K ≤ p := by
  classical
  have hlow : S.card * K ≤ ∑ τ ∈ S, normalizedCorrelation p τ := by
    calc
      _ = ∑ _τ ∈ S, K := (Finset.sum_const_nat (fun _ _ ↦ rfl)).symm
      _ ≤ _ := Finset.sum_le_sum hS
  have hhigh : (∑ τ ∈ S, normalizedCorrelation p τ) ≤ ∑ τ : ZMod p, normalizedCorrelation p τ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun τ hτ hn ↦ Nat.zero_le _)
  exact hlow.trans (hhigh.trans (sum_normalizedCorrelation_le hodd))

/-- For odd prime p and K^2>=64p, any set S of correlations at least K
satisfies card(S)*K^3<=262144p^2. Mass bounds the size of S; choose a weighted cubic
scale and cube the family inequality. The small mass case uses K<=p. -/
theorem card_mul_cube_le_of_normalizedCorrelation_ge {p K : ℕ} [Fact p.Prime] (hodd : Odd p)
    (S : Finset (ZMod p)) (hS : ∀ τ ∈ S, K ≤ normalizedCorrelation p τ) (hK : 64 * p ≤ K ^ 2) :
    S.card * K ^ 3 ≤ 262144 * p ^ 2 := by
  classical
  by_cases hs : S.card = 0
  · rw [hs, zero_mul]
    exact Nat.zero_le _
  have hspos : 0 < S.card := Nat.pos_of_ne_zero hs
  have hmass := card_mul_le_of_normalizedCorrelation_ge hodd S hS
  have hp : 0 < p := Nat.Prime.pos Fact.out
  have hsize : 64 * S.card ^ 2 ≤ p := by
    have hm := Nat.pow_le_pow_left hmass 2
    have hk := Nat.mul_le_mul_left (S.card ^ 2) hK
    have he : (64 * S.card ^ 2) * p ≤ p * p := by nlinarith only [hm, hk]
    exact Nat.le_of_mul_le_mul_right he hp
  obtain ⟨τ, hτ⟩ := Finset.card_pos.mp hspos
  have hKp : K ≤ p :=
    (hS τ hτ).trans ((card_cosetDifferenceAt_le 0 0 (principalShift p τ)).trans (Nat.sub_le p 1))
  by_cases hsmall : S.card * K < 64
  · have he := Nat.mul_le_mul_right (K ^ 2) hsmall.le
    have hk := Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left hKp 2)
    calc
      _ = (S.card * K) * K ^ 2 := by ring
      _ ≤ 64 * K ^ 2 := he
      _ ≤ 64 * p ^ 2 := hk
      _ ≤ _ := Nat.mul_le_mul_right _ (by decide : 64 ≤ 262144)
  have h64 : 64 ≤ S.card * K := Nat.le_of_not_gt hsmall
  obtain ⟨t, ht, hst, hlarge⟩ := exists_weighted_cubic_scale hspos hsize
  have hupper := sum_normalizedCorrelation_finset_scaled hodd S hspos ht hst
  have hlow : S.card * K ≤ ∑ τ ∈ S, normalizedCorrelation p τ := by
    calc
      _ = ∑ _τ ∈ S, K := (Finset.sum_const_nat (fun _ _ ↦ rfl)).symm
      _ ≤ _ := Finset.sum_le_sum hS
  have hprod := (Nat.mul_le_mul_right t hlow).trans hupper
  have h64t := Nat.mul_le_mul_right t h64
  have hbound : (S.card * K) * t ≤ 8 * p := by nlinarith only [hprod, h64t]
  have hcube := Nat.pow_le_pow_left hbound 3
  have hmul := Nat.mul_le_mul_left ((S.card * K) ^ 3) hlarge.le
  have hfinal : (S.card * K ^ 3) * (S.card ^ 2 * p) ≤ (262144 * p ^ 2) * (S.card ^ 2 * p) := by
    calc
      _ ≤ 512 * S.card ^ 2 * ((S.card * K) * t) ^ 3 := by convert hmul using 1 <;> ring
      _ ≤ 512 * S.card ^ 2 * (8 * p) ^ 3 := Nat.mul_le_mul_left (512 * S.card ^ 2) hcube
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right hfinal (mul_pos (pow_pos hspos 2) hp)

end PseudoPrime.NumberTheory.Heilbronn
