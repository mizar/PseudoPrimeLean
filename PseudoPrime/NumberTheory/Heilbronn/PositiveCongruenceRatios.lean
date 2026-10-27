/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.RationalProductSets

/-! # Bounded rational residues and Heilbronn product sets -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Positive integers x,y bounded by H with x*u=y modulo m give the bounded
rational residue y/x at height H. Use their natural absolute values as raw witnesses. -/
theorem boundedRationalResidue_of_positive_ints {m H : ℕ} {x y : ℤ} {u : ZMod m} (hx : 0 < x)
    (hy : 0 < y) (hxH : x ≤ H) (hyH : y ≤ H) (hu : (x : ZMod m) * u = (y : ZMod m)) :
    boundedRationalResidue m H ((y : ℚ) / (x : ℚ)) u := by
  have hxx : (x.natAbs : ℤ) = x := by rw [Int.natCast_natAbs, abs_of_pos hx]
  have hyy : (y.natAbs : ℤ) = y := by rw [Int.natCast_natAbs, abs_of_pos hy]
  have hxN : x.natAbs ≤ H := Int.ofNat_le.mp (hxx ▸ hxH)
  have hyN : y.natAbs ≤ H := Int.ofNat_le.mp (hyy ▸ hyH)
  refine
    ⟨y.natAbs, x.natAbs, Int.natAbs_pos.mpr (ne_of_gt hy), hyN, Int.natAbs_pos.mpr (ne_of_gt hx),
      hxN, ?_, ?_⟩
  · have hxq : (x.natAbs : ℚ) = (x : ℚ) := by rw [← Int.cast_natCast, hxx]
    have hyq : (y.natAbs : ℚ) = (y : ℚ) := by rw [← Int.cast_natCast, hyy]
    rw [hxq, hyq]
  · have hxq : (x.natAbs : ZMod m) = (x : ZMod m) := by rw [← Int.cast_natCast, hxx]
    have hyq : (y.natAbs : ZMod m) = (y : ZMod m) := by rw [← Int.cast_natCast, hyy]
    rw [hxq, hyq]
    exact hu

/-- A bounded Heilbronn congruence with both integer coordinates positive
gives a height-H rational y/x represented by an actual element of the subgroup. -/
theorem positive_congruence_has_rational_residue {p H : ℕ} [Fact p.Prime] {z : ZMod (p ^ 2) × ℤ × ℤ}
    (hz : z ∈ boundedHeilbronnCongruences p H) (hx : 0 < z.2.1) (hy : 0 < z.2.2) :
    ∃ u : heilbronnSubgroup p,
      boundedRationalResidue (p ^ 2) H ((z.2.2 : ℚ) / (z.2.1 : ℚ)) (u.val : ZMod (p ^ 2)) := by
  have hb := (mem_boundedHeilbronnCongruences_iff z).mp hz
  obtain ⟨u, hu, he⟩ := (shiftedTeichCoset_eq_heilbronn_coset 0 z.1).mp hb.1
  rw [principalShift_zero, one_mul] at he
  refine ⟨⟨u, hu⟩, boundedRationalResidue_of_positive_ints hx hy hb.2.1.2 hb.2.2.1.2 ?_⟩
  rw [← he, mul_comm]
  exact hb.2.2.2.2.2

/-- Distinct positive rational ratios y/x arising from bounded integer pairs.
This is an image set, so equal rational values are identified;
integer lifts are counted separately. -/
noncomputable def positiveRatioSet (p H : ℕ) [Fact p.Prime] : Finset ℚ := by
  classical
    exact
    ((boundedRatioPairs p H).filter (fun z ↦ 0 < z.1 ∧ 0 < z.2)).image
      (fun z ↦ (z.2 : ℚ) / (z.1 : ℚ))

/-- Every positive ratio of an actual bounded solution has a height-H residue
in the Heilbronn subgroup. Recover a triple before passing to the rational image. -/
theorem positiveRatioSet_has_residues {p H : ℕ} [Fact p.Prime] :
    ∀ q ∈ positiveRatioSet p H,
      ∃ u : heilbronnSubgroup p, boundedRationalResidue (p ^ 2) H q (u.val : ZMod (p ^ 2)) := by
  classical
  intro q hq
  obtain ⟨xy, hxy, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hmem, hx, hy⟩ := Finset.mem_filter.mp hxy
  obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hmem
  have hx' : 0 < z.2.1 := by
    rw [he]; exact hx
  have hy' : 0 < z.2.2 := by
    rw [he]; exact hy
  have hr := positive_congruence_has_rational_residue hz hx' hy'
  rw [he] at hr
  exact hr

/-- For prime p and H^(2n)<p^2, the n-fold product set of positive ratios
from the bounded congruence has at most p-1 elements. Apply the subgroup product-set bound. -/
theorem card_positive_ratio_products_le {p H n : ℕ} [Fact p.Prime] (hH : H ^ (2 * n) < p ^ 2) :
    (rationalProductSet (positiveRatioSet p H) n).card ≤ p - 1 :=
  card_rationalProductSet_le_heilbronn _ hH positiveRatioSet_has_residues

/-- For prime p and H^(2n)<p^2, a supplied product-growth loss D yields
card(A)^n<=D*(p-1) for the actual positive ratio set A. The growth lower bound is an
explicit premise; this theorem does not assert the missing rational product-growth estimate. -/
theorem positive_ratio_power_le_of_growth {p H n D : ℕ} [Fact p.Prime] (hH : H ^ (2 * n) < p ^ 2)
    (hgrowth :
      (positiveRatioSet p H).card ^ n ≤ D * (rationalProductSet (positiveRatioSet p H) n).card) :
    (positiveRatioSet p H).card ^ n ≤ D * (p - 1) :=
  hgrowth.trans (Nat.mul_le_mul_left D (card_positive_ratio_products_le hH))

end PseudoPrime.NumberTheory.Heilbronn
