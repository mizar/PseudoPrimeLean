/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.PositiveCongruencePairCounting

/-! # Signed Heilbronn congruences and positive ratio multiplicities -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Integer absolute values together with the flag of being negative determine the integer.
Use the two possible signs of equal absolute values and exclude incompatible signs. -/
theorem int_eq_of_natAbs_and_negative_flag {a b : ℤ} (hab : a.natAbs = b.natAbs)
    (hflag : decide (a < 0) = decide (b < 0)) : a = b := by
  have hi := decide_eq_decide.mp hflag
  rcases Int.natAbs_eq_natAbs_iff.mp hab with he | he
  · exact he
  · by_cases ha : a < 0
    · have hb := hi.mp ha
      nlinarith only [he, ha, hb]
    · have hb : 0 ≤ b := le_of_not_gt (fun hb ↦ ha (hi.mpr hb))
      have ha0 := le_of_not_gt ha
      nlinarith only [he, ha0, hb]

/-- Every finite integer-pair family has cardinality at most four times that of its absolute-value
image. Encode the two sign flags and the two absolute values; the flags have four possibilities. -/
theorem card_integer_pairs_le_four_abs_image (S : Finset (ℤ × ℤ)) :
    S.card ≤ 4 * (S.image (fun a ↦ (a.1.natAbs, a.2.natAbs))).card := by
  classical
  let F : (ℤ × ℤ) → (Bool × Bool) × (ℕ × ℕ) := fun a ↦
    ((decide (a.1 < 0), decide (a.2 < 0)), (a.1.natAbs, a.2.natAbs))
  have hc :=
    Finset.card_le_card_of_injOn (s := S) (t :=
      (Finset.univ : Finset (Bool × Bool)) ×ˢ S.image (fun a ↦ (a.1.natAbs, a.2.natAbs))) F
      (by
        intro a ha
        exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩)
      (by
        intro a ha b hb he
        apply Prod.ext
        · exact
            int_eq_of_natAbs_and_negative_flag
              (congrArg (fun z : (Bool × Bool) × (ℕ × ℕ) ↦ z.2.1) he)
              (congrArg (fun z : (Bool × Bool) × (ℕ × ℕ) ↦ z.1.1) he)
        · exact
            int_eq_of_natAbs_and_negative_flag
              (congrArg (fun z : (Bool × Bool) × (ℕ × ℕ) ↦ z.2.2) he)
              (congrArg (fun z : (Bool × Bool) × (ℕ × ℕ) ↦ z.1.2) he))
  simpa only [Finset.card_product, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
    Nat.reduceMul] using hc

/-- For odd p, the p-th-power subgroup of units is closed under negation.
A negative p-th power is the p-th power of the negative unit. -/
theorem heilbronnSubgroup_neg_mem {p : ℕ} (hodd : Odd p) {u : (ZMod (p ^ 2))ˣ}
    (hu : u ∈ heilbronnSubgroup p) : -u ∈ heilbronnSubgroup p := by
  obtain ⟨v, hv⟩ := hu
  refine ⟨-v, ?_⟩
  change (-v) ^ p = -u
  rw [hodd.neg_pow]
  exact congrArg Neg.neg hv

/-- For odd prime p, negation preserves the zero-shift Teichmuller coset.
Transfer subgroup closure through the established unit-coset identification. -/
theorem shiftedTeichCoset_zero_neg_mem {p : ℕ} [Fact p.Prime] (hodd : Odd p) {x : ZMod (p ^ 2)}
    (hx : x ∈ shiftedTeichCoset p 0) : -x ∈ shiftedTeichCoset p 0 := by
  obtain ⟨u, hu, he⟩ := (shiftedTeichCoset_eq_heilbronn_coset 0 x).mp hx
  apply (shiftedTeichCoset_eq_heilbronn_coset 0 (-x)).mpr
  refine ⟨-u, heilbronnSubgroup_neg_mem hodd hu, ?_⟩
  rw [principalShift_zero, one_mul, Units.val_neg]
  rw [principalShift_zero, one_mul] at he
  exact congrArg Neg.neg he

/-- For odd prime p, negating the first coordinate preserves actual bounded ratio pairs.
Negate the subgroup multiplier and first coordinate of a representing triple. -/
theorem boundedRatioPairs_neg_first {p H : ℕ} [Fact p.Prime] (hodd : Odd p) {a : ℤ × ℤ}
    (ha : a ∈ boundedRatioPairs p H) : (-a.1, a.2) ∈ boundedRatioPairs p H := by
  classical
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
  have h := (mem_boundedHeilbronnCongruences_iff z).mp hz
  apply Finset.mem_image.mpr
  refine ⟨(-z.1, -z.2.1, z.2.2), ?_, rfl⟩
  apply (mem_boundedHeilbronnCongruences_iff _).mpr
  refine
    ⟨shiftedTeichCoset_zero_neg_mem hodd h.1, ?_, h.2.2.1, neg_ne_zero.mpr h.2.2.2.1, h.2.2.2.2.1,
      ?_⟩
  · constructor <;> linarith only [h.2.1.1, h.2.1.2]
  · simpa only [Int.cast_neg, neg_mul_neg] using h.2.2.2.2.2

/-- For odd prime p, negating the second coordinate preserves actual bounded ratio pairs.
Negate the subgroup multiplier and second coordinate of a representing triple. -/
theorem boundedRatioPairs_neg_second {p H : ℕ} [Fact p.Prime] (hodd : Odd p) {a : ℤ × ℤ}
    (ha : a ∈ boundedRatioPairs p H) : (a.1, -a.2) ∈ boundedRatioPairs p H := by
  classical
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
  have h := (mem_boundedHeilbronnCongruences_iff z).mp hz
  apply Finset.mem_image.mpr
  refine ⟨(-z.1, z.2.1, -z.2.2), ?_, rfl⟩
  apply (mem_boundedHeilbronnCongruences_iff _).mpr
  refine
    ⟨shiftedTeichCoset_zero_neg_mem hodd h.1, h.2.1, ?_, h.2.2.2.1, neg_ne_zero.mpr h.2.2.2.2.1, ?_⟩
  · constructor <;> linarith only [h.2.2.1.1, h.2.2.1.2]
  · simpa only [Int.cast_neg, neg_mul] using congrArg Neg.neg h.2.2.2.2.2

/-- For odd prime p, taking both coordinate absolute values preserves actual bounded ratio pairs.
Use the separate coordinate sign symmetries according to their signs. -/
theorem boundedRatioPairs_abs_mem {p H : ℕ} [Fact p.Prime] (hodd : Odd p) {a : ℤ × ℤ}
    (ha : a ∈ boundedRatioPairs p H) : (|a.1|, |a.2|) ∈ boundedRatioPairs p H := by
  have hx : (|a.1|, a.2) ∈ boundedRatioPairs p H := by
    by_cases hx : 0 ≤ a.1
    · simpa only [abs_of_nonneg hx] using ha
    · simpa only [abs_of_neg (lt_of_not_ge hx)] using boundedRatioPairs_neg_first hodd ha
  by_cases hy : 0 ≤ a.2
  · simpa only [abs_of_nonneg hy] using hx
  · simpa only [abs_of_neg (lt_of_not_ge hy)] using boundedRatioPairs_neg_second hodd hx

/-- For odd prime p, the absolute-value image of all bounded ratio pairs lies in the positive
natural pair family. Nonzero original coordinates ensure positivity; all congruences
are preserved. -/
theorem boundedRatioPairs_abs_image_subset {p H : ℕ} [Fact p.Prime] (hodd : Odd p) :
    (boundedRatioPairs p H).image (fun a ↦ (a.1.natAbs, a.2.natAbs)) ⊆
      positiveNaturalRatioPairs p H := by
  classical
  intro b hb
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
  have h := boundedRatioPairs_coordinate_bounds ha
  apply Finset.mem_image.mpr
  refine ⟨((a.1.natAbs : ℤ), (a.2.natAbs : ℤ)), ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine
      ⟨?_, Int.natCast_pos.mpr (Int.natAbs_pos.mpr h.2.2.1),
        Int.natCast_pos.mpr (Int.natAbs_pos.mpr h.2.2.2)⟩
    simpa only [Int.natCast_natAbs] using boundedRatioPairs_abs_mem hodd ha
  · simp only [Int.natAbs_natCast]

/-- For odd prime p, all bounded signed ratio pairs number at most four times the positive
integer pairs. Combine sign encoding with the positive natural-image cardinality equality. -/
theorem boundedRatioPairs_card_le_four_positive {p H : ℕ} [Fact p.Prime] (hodd : Odd p) :
    (boundedRatioPairs p H).card ≤ 4 * (positiveIntegerRatioPairs p H).card := by
  have h := card_integer_pairs_le_four_abs_image (boundedRatioPairs p H)
  have hm :=
    Nat.mul_le_mul_left 4 (Finset.card_le_card (boundedRatioPairs_abs_image_subset (H := H) hodd))
  rw [card_positiveNaturalRatioPairs] at hm
  exact h.trans hm

/-- For odd prime p and 1 at most H less than p, bound the actual full congruence count squared
by 144*H^2*T(H)^2*card(positiveRatioSet). The short-coordinate projection is injective,
signs cost at most four, and denominator splitting controls repeated representations
of each ratio. -/
theorem boundedCongruenceCount_sq_le_positive_ratios {p H : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hH : 0 < H) (hHp : H < p) :
    boundedCongruenceCount p H ^ 2 ≤
      144 * H ^ 2 * maxDivisorCount H ^ 2 * (positiveRatioSet p H).card := by
  rw [boundedCongruenceCount_eq_ratioPairs_card hHp]
  have h := Nat.pow_le_pow_left (boundedRatioPairs_card_le_four_positive (H := H) hodd) 2
  have hp := Nat.mul_le_mul_left 16 (positiveIntegerRatioPairs_sq_le (p := p) hH)
  nlinarith only [h, hp]

end PseudoPrime.NumberTheory.Heilbronn
