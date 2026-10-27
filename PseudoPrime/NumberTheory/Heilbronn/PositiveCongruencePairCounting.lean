/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.PositivePairCounting
public import PseudoPrime.NumberTheory.Heilbronn.PositiveRatioGrowth

/-! # Positive integer pairs and their distinct Heilbronn ratios -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- The positive-coordinate part of the actual bounded integer ratio pairs for prime p.
Coordinates are retained as integers; pairs with identical rational ratios remain distinct. -/
noncomputable def positiveIntegerRatioPairs (p H : ℕ) [Fact p.Prime] : Finset (ℤ × ℤ) := by
  classical exact (boundedRatioPairs p H).filter (fun a ↦ 0 < a.1 ∧ 0 < a.2)

/-- The natural-coordinate image of positive integer ratio pairs, using absolute values.
Positivity makes this map injective, allowing generic natural-pair counting to apply. -/
noncomputable def positiveNaturalRatioPairs (p H : ℕ) [Fact p.Prime] : Finset (ℕ × ℕ) :=
  (positiveIntegerRatioPairs p H).image (fun a ↦ (a.1.natAbs, a.2.natAbs))

/-- Every projected bounded Heilbronn pair has two nonzero coordinates in [-H,H].
Recover a representing triple and retain its coordinate conditions. -/
theorem boundedRatioPairs_coordinate_bounds {p H : ℕ} [Fact p.Prime] {a : ℤ × ℤ}
    (ha : a ∈ boundedRatioPairs p H) :
    (-(H : ℤ) ≤ a.1 ∧ a.1 ≤ H) ∧ (-(H : ℤ) ≤ a.2 ∧ a.2 ≤ H) ∧ a.1 ≠ 0 ∧ a.2 ≠ 0 := by
  classical
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
  have h := (mem_boundedHeilbronnCongruences_iff z).mp hz
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-- Both coordinates of every positive natural ratio pair lie in [1,H].
Use positivity and the original integer interval bounds after taking absolute values. -/
theorem positiveNaturalRatioPairs_bounds {p H : ℕ} [Fact p.Prime] :
    ∀ a ∈ positiveNaturalRatioPairs p H, 0 < a.1 ∧ a.1 ≤ H ∧ 0 < a.2 ∧ a.2 ≤ H := by
  classical
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  have hm := Finset.mem_filter.mp hb
  have h := boundedRatioPairs_coordinate_bounds hm.1
  have hx : (b.1.natAbs : ℤ) = b.1 := by rw [Int.natCast_natAbs, abs_of_pos hm.2.1]
  have hy : (b.2.natAbs : ℤ) = b.2 := by rw [Int.natCast_natAbs, abs_of_pos hm.2.2]
  exact
    ⟨Int.natAbs_pos.mpr (ne_of_gt hm.2.1), Int.ofNat_le.mp (hx ▸ h.1.2),
      Int.natAbs_pos.mpr (ne_of_gt hm.2.2), Int.ofNat_le.mp (hy ▸ h.2.1.2)⟩

/-- The positive natural pair image has exactly the same cardinality as the positive integer
pair family. Absolute values are injective on positive coordinates. -/
theorem card_positiveNaturalRatioPairs {p H : ℕ} [Fact p.Prime] :
    (positiveNaturalRatioPairs p H).card = (positiveIntegerRatioPairs p H).card := by
  classical
  apply Finset.card_image_of_injOn
  intro a ha b hb he
  have hpa := (Finset.mem_filter.mp ha).2
  have hpb := (Finset.mem_filter.mp hb).2
  apply Prod.ext
  · have hx := congrArg (fun t : ℕ × ℕ ↦ (t.1 : ℤ)) he
    simpa only [Int.natCast_natAbs, abs_of_pos hpa.1, abs_of_pos hpb.1] using hx
  · have hy := congrArg (fun t : ℕ × ℕ ↦ (t.2 : ℤ)) he
    simpa only [Int.natCast_natAbs, abs_of_pos hpa.2, abs_of_pos hpb.2] using hy

/-- The rational image of the positive natural pairs is exactly positiveRatioSet.
Composing the natural-coordinate image preserves the original positive integer ratios. -/
theorem positiveNaturalRatioPairs_image {p H : ℕ} [Fact p.Prime] :
    (positiveNaturalRatioPairs p H).image (fun a ↦ (a.2 : ℚ) / a.1) = positiveRatioSet p H := by
  classical
  rw [positiveNaturalRatioPairs, Finset.image_image]
  apply Finset.image_congr
  intro a ha
  have hp := (Finset.mem_filter.mp ha).2
  have hx : (a.1.natAbs : ℤ) = a.1 := by rw [Int.natCast_natAbs, abs_of_pos hp.1]
  have hy : (a.2.natAbs : ℤ) = a.2 := by rw [Int.natCast_natAbs, abs_of_pos hp.2]
  change (a.2.natAbs : ℚ) / a.1.natAbs = (a.2 : ℚ) / a.1
  have hxq : (a.1.natAbs : ℚ) = (a.1 : ℚ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ ↦ (z : ℚ)) hx
  have hyq : (a.2.natAbs : ℚ) = (a.2 : ℚ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ ↦ (z : ℚ)) hy
  rw [hxq, hyq]

/-- For positive H, the square of the actual positive integer-pair count is at most
9*H^2*T(H)^2*card(positiveRatioSet). Transfer the generic denominator-cutoff count through
the cardinality-preserving natural image; equal-ratio multiplicities are fully retained. -/
theorem positiveIntegerRatioPairs_sq_le {p H : ℕ} [Fact p.Prime] (hH : 0 < H) :
    (positiveIntegerRatioPairs p H).card ^ 2 ≤
      9 * H ^ 2 * maxDivisorCount H ^ 2 * (positiveRatioSet p H).card := by
  have h := card_positive_pairs_sq_le hH (positiveNaturalRatioPairs_bounds (p := p))
  rw [card_positiveNaturalRatioPairs, positiveNaturalRatioPairs_image] at h
  exact h

end PseudoPrime.NumberTheory.Heilbronn
