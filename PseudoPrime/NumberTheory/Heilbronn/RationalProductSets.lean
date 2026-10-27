/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.RationalResidues

/-! # Bounded rational residues and Heilbronn product sets -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Map the p-th power subgroup of units to its underlying zero-shift coset.
This identifies group and residue-set cardinalities. -/
noncomputable def heilbronnSubgroupToCoset {p : ℕ} [Fact p.Prime] (u : heilbronnSubgroup p) :
    shiftedTeichCoset p 0 :=
  ⟨(u.val : ZMod (p ^ 2)),
    (shiftedTeichCoset_eq_heilbronn_coset 0 _).mpr
      ⟨u.val, u.property, by rw [principalShift_zero, one_mul]⟩⟩

/-- For prime p the subgroup-to-coset map is bijective, by injectivity of unit
coercion and the proved identification of the zero-shift coset. -/
theorem heilbronnSubgroupToCoset_bijective {p : ℕ} [Fact p.Prime] :
    Function.Bijective (heilbronnSubgroupToCoset (p := p)) := by
  constructor
  · intro u v h
    apply Subtype.ext
    apply Units.ext
    exact congrArg Subtype.val h
  · intro x
    obtain ⟨u, hu, he⟩ := (shiftedTeichCoset_eq_heilbronn_coset 0 x.val).mp x.property
    rw [principalShift_zero, one_mul] at he
    exact ⟨⟨u, hu⟩, Subtype.ext he.symm⟩

/-- For prime p the Heilbronn subgroup has exactly p-1 elements.
Transfer the already proved zero-coset cardinality through the group equivalence. -/
theorem card_heilbronnSubgroup {p : ℕ} [Fact p.Prime] : Nat.card (heilbronnSubgroup p) = p - 1 :=
  (Nat.card_congr (Equiv.ofBijective _ heilbronnSubgroupToCoset_bijective)).trans
    (card_shiftedTeichCoset 0)

/-- For prime p and Q^2<p^2, a finite family of height-Q positive rationals
represented in the Heilbronn subgroup has at most p-1 elements. Choose representatives
and use bounded modular injectivity; no rational growth estimate is assumed. -/
theorem card_rational_family_le_heilbronn {p Q : ℕ} [Fact p.Prime] (A : Finset ℚ)
    (hQ : Q ^ 2 < p ^ 2)
    (hA :
      ∀ q ∈ A,
        ∃ u : heilbronnSubgroup p, boundedRationalResidue (p ^ 2) Q q (u.val : ZMod (p ^ 2))) :
    A.card ≤ p - 1 := by
  classical
  choose f hf using (fun q : A ↦ hA q.val q.property)
  have hinj : Function.Injective f := by
    intro q r he
    apply Subtype.ext
    apply boundedRationalResidue_injective (hf q) _ hQ
    rw [he]
    exact hf r
  have hc := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_heilbronnSubgroup] at hc
  exact hc

/-- The finite set of n-fold products from A, including the empty product for n=0.
It is an analytic finite product set, not an enumerated certificate. -/
noncomputable def rationalProductSet (A : Finset ℚ) (n : ℕ) : Finset ℚ := by
  classical exact Finset.univ.image (fun f : Fin n → A ↦ ∏ i : Fin n, (f i).val)

/-- Products of n height-Q rationals represented in the Heilbronn subgroup
remain represented there with height Q^n. Multiply the chosen subgroup witnesses. -/
theorem rationalProductSet_has_residues {p Q n : ℕ} [Fact p.Prime] (A : Finset ℚ)
    (hA :
      ∀ q ∈ A,
        ∃ u : heilbronnSubgroup p, boundedRationalResidue (p ^ 2) Q q (u.val : ZMod (p ^ 2))) :
    ∀ q ∈ rationalProductSet A n,
      ∃ u : heilbronnSubgroup p,
        boundedRationalResidue (p ^ 2) (Q ^ n) q (u.val : ZMod (p ^ 2)) := by
  classical
  intro q hq
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hq
  choose g hg using (fun i : Fin n ↦ hA (f i).val (f i).property)
  refine ⟨∏ i : Fin n, g i, ?_⟩
  have he :=
    boundedRationalResidue_prod (Finset.univ : Finset (Fin n)) (fun i ↦ (f i).val)
      (fun i ↦ ((g i).val : ZMod (p ^ 2))) (fun i hi ↦ hg i)
  have hc :
    (((∏ i : Fin n, g i).val) : ZMod (p ^ 2)) = ∏ i : Fin n, ((g i).val : ZMod (p ^ 2)) := by
    change (((heilbronnSubgroup p).subtype (∏ i : Fin n, g i)) : ZMod (p ^ 2)) = _
    rw [map_prod, Units.coe_prod]
    rfl
  rw [hc]
  simpa only [Finset.card_univ, Fintype.card_fin] using he

/-- For prime p and Q^(2n)<p^2, the n-fold product set of a represented
height-Q rational family has at most p-1 elements. Combine height growth and modular injectivity. -/
theorem card_rationalProductSet_le_heilbronn {p Q n : ℕ} [Fact p.Prime] (A : Finset ℚ)
    (hQ : Q ^ (2 * n) < p ^ 2)
    (hA :
      ∀ q ∈ A,
        ∃ u : heilbronnSubgroup p, boundedRationalResidue (p ^ 2) Q q (u.val : ZMod (p ^ 2))) :
    (rationalProductSet A n).card ≤ p - 1 := by
  apply card_rational_family_le_heilbronn _ _ (rationalProductSet_has_residues A hA)
  have he : (Q ^ n) ^ 2 = Q ^ (2 * n) := by rw [← pow_mul, Nat.mul_comm n 2]
  exact he ▸ hQ

end PseudoPrime.NumberTheory.Heilbronn
