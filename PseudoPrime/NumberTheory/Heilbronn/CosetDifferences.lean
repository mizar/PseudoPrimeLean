/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.TruncatedLogCongruence
public import PseudoPrime.NumberTheory.Heilbronn.StepanovConstraints

/-! # Heilbronn coset differences as affine truncated-log roots -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- The principal shift of nonzero Teichmuller lifts modulo p^2. For prime p
these are the Heilbronn multiplicative cosets used in the normalized difference equation. -/
def shiftedTeichCoset (p : ℕ) (i : ZMod p) : Set (ZMod (p ^ 2)) :=
  {x | ∃ b : ZMod p, b ≠ 0 ∧ x = principalShift p i * teichLift p b}

/-- Ordered pairs from the cosets with parameters i,j whose difference is the
principal shift of tau. The equation is normalized to reduction one. -/
def cosetDifferencePairs (p : ℕ) (i j τ : ZMod p) : Set (ZMod (p ^ 2) × ZMod (p ^ 2)) :=
  {z | z.1 ∈ shiftedTeichCoset p i ∧ z.2 ∈ shiftedTeichCoset p j ∧ z.1 - z.2 = principalShift p τ}

/-- Nonexceptional residues b, excluding zero and one, satisfying
f(b)=(i-j)b+j-tau. This is the finite-field solution set for a normalized coset difference. -/
def affineLogRoots (p : ℕ) (i j τ : ZMod p) : Set (ZMod p) :=
  {b | b ≠ 0 ∧ b ≠ 1 ∧ (truncatedLog p).eval b = (i - j) * b + j - τ}

/-- For prime p a principal-shifted lift of b reduces to b; this recovers coset parameters. -/
theorem reduction_shifted_teichLift {p : ℕ} [Fact p.Prime] (i b : ZMod p) :
    squareReduction p (principalShift p i * teichLift p b) = b := by
  rw [map_mul, squareReduction_principalShift, squareReduction_teichLift, one_mul]

/-- For odd prime p map an affine truncated-log root b to the pair of shifted
lifts of b and b-1. The exact difference identity supplies membership in the solution set. -/
noncomputable def affineRootToDifference {p : ℕ} [Fact p.Prime] (hodd : Odd p) (i j τ : ZMod p)
    (b : affineLogRoots p i j τ) : cosetDifferencePairs p i j τ :=
  ⟨(principalShift p i * teichLift p b.val, principalShift p j * teichLift p (b.val - 1)),
    ⟨⟨b.val, b.property.1, rfl⟩, ⟨b.val - 1, sub_ne_zero.mpr b.property.2.1, rfl⟩,
      (shifted_teichLift_difference_iff hodd i j τ b.val).mpr b.property.2.2⟩⟩

/-- For odd prime p the root-to-pair map is bijective. Reduction recovers b;
the difference equation forces the second residue to be b-1, proving surjectivity. -/
theorem affineRootToDifference_bijective {p : ℕ} [Fact p.Prime] (hodd : Odd p) (i j τ : ZMod p) :
    Function.Bijective (affineRootToDifference hodd i j τ) := by
  constructor
  · intro a b h
    apply Subtype.ext
    have he := congrArg (fun z : cosetDifferencePairs p i j τ ↦ squareReduction p z.val.1) h
    exact
      (reduction_shifted_teichLift i a.val).symm.trans
        (he.trans (reduction_shifted_teichLift i b.val))
  · intro z
    obtain ⟨b, hb, hxb⟩ := z.property.1
    obtain ⟨c, hc, hyc⟩ := z.property.2.1
    have hbc : b - c = 1 := by
      have he := congrArg (squareReduction p) z.property.2.2
      rw [map_sub, hxb, hyc, reduction_shifted_teichLift, reduction_shifted_teichLift,
        squareReduction_principalShift] at he
      exact he
    have hcb : c = b - 1 := by linear_combination -hbc
    have hb1 : b ≠ 1 := by
      intro he
      apply hc
      rw [hcb, he, sub_self]
    have heq : (truncatedLog p).eval b = (i - j) * b + j - τ := by
      apply (shifted_teichLift_difference_iff hodd i j τ b).mp
      rw [← hxb, ← hcb, ← hyc]
      exact z.property.2.2
    refine ⟨⟨b, hb, hb1, heq⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact hxb.symm
    · exact (congrArg (fun c ↦ principalShift p j * teichLift p c) hcb).symm.trans hyc.symm

/-- For odd prime p the normalized coset difference pairs are equivalent to
nonexceptional affine truncated-log roots. This is the exact cardinality transfer. -/
noncomputable def cosetDifferenceEquivAffineRoots {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (i j τ : ZMod p) : cosetDifferencePairs p i j τ ≃ affineLogRoots p i j τ :=
  (Equiv.ofBijective _ (affineRootToDifference_bijective hodd i j τ)).symm

/-- For odd prime p the coset difference and affine-root sets have the same cardinality,
by the explicitly constructed equivalence; no unproved counting input is used. -/
theorem card_cosetDifferencePairs_eq_affineLogRoots {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (i j τ : ZMod p) :
    Nat.card (cosetDifferencePairs p i j τ) = Nat.card (affineLogRoots p i j τ) :=
  Nat.card_congr (cosetDifferenceEquivAffineRoots hodd i j τ)

/-- For odd prime p, positive t and 64t^3<=p, each normalized coset correlation
satisfies card*t<=32t+4p. Transfer the equivalence to the constructed Stepanov bound. -/
theorem card_cosetDifferencePairs_scaled {p t : ℕ} [Fact p.Prime] (hodd : Odd p) (i j τ : ZMod p)
    (ht : 0 < t) (hsize : 64 * t ^ 3 ≤ p) :
    Nat.card (cosetDifferencePairs p i j τ) * t ≤ 32 * t + 4 * p := by
  classical
  rw [card_cosetDifferencePairs_eq_affineLogRoots hodd]
  let S := (affineLogRoots p i j τ).toFinset
  have hc : Nat.card (affineLogRoots p i j τ) = S.card := by
    rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
  rw [hc]
  apply
    card_affine_truncatedLog_solutions_scaled (s := 1) (fun _ ↦ i - j) (fun _ ↦ j - τ)
      (by decide : 0 < 1) ht
  · simpa only [one_pow, mul_one] using hsize
  · intro b hb
    have h : b ∈ affineLogRoots p i j τ := Set.mem_toFinset.mp hb
    refine ⟨h.1, h.2.1, ⟨0, ?_⟩⟩
    exact h.2.2.trans (by ring)

/-- Distinct shift targets for fixed source cosets give disjoint root sets.
Cancel the common affine expression; this prevents multiplicity loss in the family estimate. -/
theorem affineLogRoots_disjoint_of_same_cosets {p : ℕ} [Fact p.Prime] (i j τ σ : ZMod p)
    (h : τ ≠ σ) : Disjoint (affineLogRoots p i j τ) (affineLogRoots p i j σ) := by
  apply Set.disjoint_left.mpr
  intro b hb hc
  apply h
  linear_combination hb.2.2 - hc.2.2

/-- For odd prime p, positive s,t, distinct target parameters and 64s^2*t^3<=p,
the sum of normalized coset correlations times t is at most 32t+4p.
Disjoint affine-root sets let the constructed Stepanov bound control the entire sum. -/
theorem sum_card_cosetDifferencePairs_scaled {p s t : ℕ} [Fact p.Prime] (hodd : Odd p)
    (i j : ZMod p) (τ : Fin s → ZMod p) (hinj : Function.Injective τ) (hs : 0 < s) (ht : 0 < t)
    (hsize : 64 * s ^ 2 * t ^ 3 ≤ p) :
    (∑ k : Fin s, Nat.card (cosetDifferencePairs p i j (τ k))) * t ≤ 32 * t + 4 * p := by
  classical
  let roots : Fin s → Finset (ZMod p) := fun k ↦ (affineLogRoots p i j (τ k)).toFinset
  let S := Finset.univ.biUnion roots
  have hd : (Set.univ : Set (Fin s)).PairwiseDisjoint roots := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hx' : x ∈ affineLogRoots p i j (τ a) := Set.mem_toFinset.mp hx
    have hy' : x ∈ affineLogRoots p i j (τ b) := Set.mem_toFinset.mp hy
    exact
      (Set.disjoint_left.mp
          (affineLogRoots_disjoint_of_same_cosets i j (τ a) (τ b) (fun he ↦ hab (hinj he))))
        hx' hy'
  have hc : S.card = ∑ k : Fin s, Nat.card (cosetDifferencePairs p i j (τ k)) := by
    rw [Finset.card_biUnion (by simpa only [Finset.coe_univ] using hd)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [card_cosetDifferencePairs_eq_affineLogRoots hodd, Nat.card_eq_fintype_card, ←
      Set.toFinset_card]
  rw [← hc]
  apply card_affine_truncatedLog_solutions_scaled (fun _ ↦ i - j) (fun k ↦ j - τ k) hs ht hsize S
  intro b hb
  obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hb
  have h : b ∈ affineLogRoots p i j (τ k) := Set.mem_toFinset.mp hk
  exact ⟨h.1, h.2.1, ⟨k, h.2.2.trans (by ring)⟩⟩

end PseudoPrime.NumberTheory.Heilbronn
