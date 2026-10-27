/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.HeilbronnFrequencyMultiplicity

/-! # Exact square mass of Heilbronn frequency multiplicities -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Bounded congruence solutions with the multiplier retained as a subgroup element.
This representation allows group multiplication and inversion in the collision bijection. -/
noncomputable def typedHeilbronnCongruences (p H : ℕ) [Fact p.Prime] :
    Finset (heilbronnSubgroup p × ℤ × ℤ) := by
  classical
    exact
    (Finset.univ ×ˢ (signedShortIntegers H ×ˢ signedShortIntegers H)).filter
      (fun z ↦ (z.1.val : ZMod (p ^ 2)) * z.2.1 = z.2.2)

/-- Membership in the typed congruence set records both short frequencies and their equation. -/
theorem mem_typedHeilbronnCongruences {p H : ℕ} [Fact p.Prime] (z : heilbronnSubgroup p × ℤ × ℤ) :
    z ∈ typedHeilbronnCongruences p H ↔
      z.2.1 ∈ signedShortIntegers H ∧
        z.2.2 ∈ signedShortIntegers H ∧ (z.1.val : ZMod (p ^ 2)) * z.2.1 = z.2.2 := by
  classical
    simp only [typedHeilbronnCongruences, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
    true_and, and_assoc]

/-- A collision u*x=v*y is equivalent to (v inverse times u)*x=y.
Multiply by the inverse unit; no nonzero assumption on x or y is needed. -/
theorem subgroup_inverse_frequency {p : ℕ} [Fact p.Prime] (u v : heilbronnSubgroup p)
    (x y : ZMod (p ^ 2)) :
    (u.val : ZMod (p ^ 2)) * x = (v.val : ZMod (p ^ 2)) * y ↔
      ((v⁻¹ * u).val : ZMod (p ^ 2)) * x = y := by
  constructor
  · intro h
    have hh := congrArg (fun z ↦ ((v⁻¹).val : ZMod (p ^ 2)) * z) h
    simpa only [← mul_assoc, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
      Units.val_one, one_mul] using hh
  · intro h
    have hh := congrArg (fun z ↦ (v.val : ZMod (p ^ 2)) * z) h
    simpa only [← mul_assoc, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      Units.val_one, one_mul] using hh

/-- Typed congruence solutions have exactly the original bounded congruence count.
The subgroup-to-coset bijection preserves both integer coordinates. -/
theorem card_typedHeilbronnCongruences {p H : ℕ} [Fact p.Prime] :
    (typedHeilbronnCongruences p H).card = boundedCongruenceCount p H := by
  classical
  apply Finset.card_bij (fun z hz ↦ ((z.1.val : ZMod (p ^ 2)), z.2))
  · intro z hz
    have ht := (mem_typedHeilbronnCongruences z).mp hz
    have hx := mem_signedShortIntegers.mp ht.1
    have hy := mem_signedShortIntegers.mp ht.2.1
    apply (mem_boundedHeilbronnCongruences_iff _).mpr
    exact
      ⟨(heilbronnSubgroupToCoset z.1).property, ⟨hx.1, hx.2.1⟩, ⟨hy.1, hy.2.1⟩, hx.2.2, hy.2.2,
        ht.2.2⟩
  · intro a ha b hb he
    have hu : a.1 = b.1 := Subtype.ext (Units.ext (congrArg Prod.fst he))
    have hs : a.2 = b.2 := congrArg (fun z : ZMod (p ^ 2) × ℤ × ℤ ↦ z.2) he
    exact Prod.ext hu hs
  · intro z hz
    have ht := (mem_boundedHeilbronnCongruences_iff z).mp hz
    obtain ⟨u, hu, he⟩ := (shiftedTeichCoset_eq_heilbronn_coset 0 z.1).mp ht.1
    rw [principalShift_zero, one_mul] at he
    refine ⟨(⟨u, hu⟩, z.2), ?_, ?_⟩
    · apply (mem_typedHeilbronnCongruences _).mpr
      refine
        ⟨mem_signedShortIntegers.mpr ⟨ht.2.1.1, ht.2.1.2, ht.2.2.2.1⟩,
          mem_signedShortIntegers.mpr ⟨ht.2.2.1.1, ht.2.2.1.2, ht.2.2.2.2.1⟩, ?_⟩
      exact he ▸ ht.2.2.2.2.2
    · exact Prod.ext he.symm rfl

/-- For prime p and arbitrary height H, the square mass is (p-1)*N_p(H).
Map a collision ((u,x),(v,y)) to (v,(v inverse times u,x,y)); the inverse
recovers u=v*t. Raw integer multiplicities are preserved without assuming H<p. -/
theorem sum_heilbronnFrequencyMultiplicity_sq {p H : ℕ} [Fact p.Prime] :
    (∑ w : ZMod (p ^ 2), heilbronnFrequencyMultiplicity p H w ^ 2) =
      (p - 1) * boundedCongruenceCount p H := by
  classical
  let C :=
    ((heilbronnFrequencyPairs p H) ×ˢ (heilbronnFrequencyPairs p H)).filter
      (fun z ↦ (z.1.1.val : ZMod (p ^ 2)) * z.1.2 = (z.2.1.val : ZMod (p ^ 2)) * z.2.2)
  have hc :
    C.card =
      ((Finset.univ : Finset (heilbronnSubgroup p)) ×ˢ typedHeilbronnCongruences p H).card := by
    apply Finset.card_bij (fun z hz ↦ (z.2.1, (z.2.1⁻¹ * z.1.1, z.1.2, z.2.2)))
    · intro z hz
      have ht := Finset.mem_filter.mp hz
      have hpairs := Finset.mem_product.mp ht.1
      have hx := (Finset.mem_product.mp hpairs.1).2
      have hy := (Finset.mem_product.mp hpairs.2).2
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_univ _, (mem_typedHeilbronnCongruences _).mpr ?_⟩
      exact ⟨hx, hy, (subgroup_inverse_frequency _ _ _ _).mp ht.2⟩
    · intro a ha b hb he
      have hv : a.2.1 = b.2.1 := congrArg (fun z ↦ z.1) he
      have ht : a.2.1⁻¹ * a.1.1 = b.2.1⁻¹ * b.1.1 := congrArg (fun z ↦ z.2.1) he
      have hx : a.1.2 = b.1.2 := congrArg (fun z ↦ z.2.2.1) he
      have hy : a.2.2 = b.2.2 := congrArg (fun z ↦ z.2.2.2) he
      rw [hv] at ht
      have hu := mul_left_cancel ht
      exact Prod.ext (Prod.ext hu hx) (Prod.ext hv hy)
    · intro z hz
      have ht := (mem_typedHeilbronnCongruences z.2).mp (Finset.mem_product.mp hz).2
      let a := ((z.1 * z.2.1, z.2.2.1), (z.1, z.2.2.2))
      have ha : a ∈ C := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
        · exact Finset.mem_product.mpr ⟨Finset.mem_univ _, ht.1⟩
        · exact Finset.mem_product.mpr ⟨Finset.mem_univ _, ht.2.1⟩
        · apply (subgroup_inverse_frequency _ _ _ _).mpr
          simpa only [a, inv_mul_cancel_left] using ht.2.2
      refine ⟨a, ha, ?_⟩
      simp only [a, inv_mul_cancel_left]
  have h :=
    sum_fiber_cards_sq (heilbronnFrequencyPairs p H) (fun z ↦ (z.1.val : ZMod (p ^ 2)) * z.2)
  change (∑ w, heilbronnFrequencyMultiplicity p H w ^ 2) = C.card at h
  rw [h, hc, Finset.card_product, Finset.card_univ, ← Nat.card_eq_fintype_card,
    card_heilbronnSubgroup, card_typedHeilbronnCongruences]

end PseudoPrime.NumberTheory.Heilbronn
