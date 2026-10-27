/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.PositiveCongruencePairCounting
public import PseudoPrime.NumberTheory.Heilbronn.SignedCongruencePairCounting

/-! # Height-sensitive multiplicities of positive rational ratios -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- The canonical height of a rational number is the maximum of the absolute
numerator and the positive denominator. It controls the number of positive
integer pairs representing a fixed positive ratio in a bounded square. -/
def rationalPairHeight (q : ℚ) : ℕ :=
  max q.num.natAbs q.den

/-- For a positive denominator, both raw natural coordinates are reconstructed
from the canonical fraction and the quotient by its denominator. This fixes the
scale used in the height-sensitive injection for integer-pair multiplicities. -/
theorem fraction_coordinates_eq_scale {a b : ℕ} (hb : 0 < b) :
    a = (b / ((a : ℚ) / b).den) * ((a : ℚ) / b).num.natAbs ∧
      b = (b / ((a : ℚ) / b).den) * ((a : ℚ) / b).den := by
  obtain ⟨c, _, hn, hd⟩ := fraction_scale_of_den_pos (a := a) hb
  have he : b / ((a : ℚ) / b).den = c :=
    (congrArg (fun t ↦ t / ((a : ℚ) / b).den) hd).trans (Nat.mul_div_left c (Rat.den_pos _))
  rw [he]
  exact ⟨hn, hd⟩

/-- Positive raw coordinates at most H have canonical scaling factor between
one and floor(H/height). Reconstruct the coordinates, then use their maximum.
This keeps the exact reciprocal-height weight before any aggregate estimate. -/
theorem fraction_scale_mem_height_interval {a b H : ℕ} (hb : 0 < b) (haH : a ≤ H) (hbH : b ≤ H) :
    1 ≤ b / ((a : ℚ) / b).den ∧ b / ((a : ℚ) / b).den ≤ H / rationalPairHeight ((a : ℚ) / b) := by
  have hs := fraction_coordinates_eq_scale (a := a) hb
  have hd := (fraction_component_dvd_of_den_pos (a := a) hb).2
  refine ⟨Nat.div_pos (Nat.le_of_dvd hb hd) (Rat.den_pos _), ?_⟩
  apply (Nat.le_div_iff_mul_le ((Rat.den_pos _).trans_le (le_max_right _ _))).mpr
  rw [mul_max, ← hs.1, ← hs.2]
  exact max_le haH hbH

/-- A finite family of positive integer pairs in the H-square has cardinality
at most the sum of floor(H/height(q)) over its distinct ratios q. Encode each
pair by its ratio and canonical scale, and reconstruct both raw coordinates.
This avoids replacing all multiplicities by a common square-root estimate. -/
theorem card_positive_pairs_le_height_sum {S : Finset (ℕ × ℕ)} {H : ℕ}
    (hS : ∀ a ∈ S, 0 < a.1 ∧ a.1 ≤ H ∧ 0 < a.2 ∧ a.2 ≤ H) :
    S.card ≤ ∑ q ∈ S.image (fun a ↦ (a.2 : ℚ) / a.1), H / rationalPairHeight q := by
  classical
  let F : (ℕ × ℕ) → Σ _ : ℚ, ℕ := fun a ↦ ⟨(a.2 : ℚ) / a.1, a.1 / ((a.2 : ℚ) / a.1).den⟩
  have hc :=
    Finset.card_le_card_of_injOn (s := S) (t :=
      (S.image (fun a ↦ (a.2 : ℚ) / a.1)).sigma (fun q ↦ Finset.Icc 1 (H / rationalPairHeight q))) F
      (by
        intro a ha
        have h := hS a ha
        exact
          Finset.mem_sigma.mpr
            ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩,
              Finset.mem_Icc.mpr (fraction_scale_mem_height_interval h.1 h.2.2.2 h.2.1)⟩)
      (by
        intro a ha b hb he
        have hsa := hS a ha
        have hsb := hS b hb
        have hq : (a.2 : ℚ) / a.1 = (b.2 : ℚ) / b.1 := congrArg Sigma.fst he
        have hs : a.1 / ((a.2 : ℚ) / a.1).den = b.1 / ((b.2 : ℚ) / b.1).den := congrArg Sigma.snd he
        have hna := fraction_coordinates_eq_scale (a := a.2) hsa.1
        have hnb := fraction_coordinates_eq_scale (a := b.2) hsb.1
        apply Prod.ext
        · calc
            a.1 = _ := hna.2
            _ = _ := by rw [hs, hq]
            _ = b.1 := hnb.2.symm
        · calc
            a.2 = _ := hna.1
            _ = _ := by rw [hs, hq]
            _ = b.2 := hnb.1.symm)
  simpa only [Finset.card_sigma, Nat.card_Icc, Nat.add_sub_cancel] using hc

/-- The actual positive Heilbronn integer pairs obey the canonical-height
weighted ratio bound. Transfer the generic count through the natural image;
the sum is over distinct ratios while integer-pair multiplicity is retained. -/
theorem positiveIntegerRatioPairs_le_height_sum {p H : ℕ} [Fact p.Prime] :
    (positiveIntegerRatioPairs p H).card ≤
      ∑ q ∈ positiveRatioSet p H, H / rationalPairHeight q := by
  have h := card_positive_pairs_le_height_sum (positiveNaturalRatioPairs_bounds (p := p) (H := H))
  rw [card_positiveNaturalRatioPairs, positiveNaturalRatioPairs_image] at h
  exact h

/-- For an odd prime and H<p, the full signed congruence count is bounded by
four times the height-weighted positive ratio sum. Short-coordinate uniqueness
and the four sign choices preserve the original triple count. -/
theorem boundedCongruenceCount_le_four_height_sum {p H : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hHp : H < p) :
    boundedCongruenceCount p H ≤ 4 * ∑ q ∈ positiveRatioSet p H, H / rationalPairHeight q := by
  rw [boundedCongruenceCount_eq_ratioPairs_card hHp]
  exact
    (boundedRatioPairs_card_le_four_positive hodd).trans
      (Nat.mul_le_mul_left 4 positiveIntegerRatioPairs_le_height_sum)

/-- A family of positive pairs whose ratios all have height greater than J
has at most card(ratios)*floor(H/(J+1)) elements in the H-square. Apply the
height-weighted injection and bound its weights only within this height layer. -/
theorem card_positive_pairs_le_of_height_lower {S : Finset (ℕ × ℕ)} {H J : ℕ}
    (hS : ∀ a ∈ S, 0 < a.1 ∧ a.1 ≤ H ∧ 0 < a.2 ∧ a.2 ≤ H)
    (hJ : ∀ a ∈ S, J < rationalPairHeight ((a.2 : ℚ) / a.1)) :
    S.card ≤ (S.image (fun a ↦ (a.2 : ℚ) / a.1)).card * (H / (J + 1)) := by
  classical
  apply (card_positive_pairs_le_height_sum hS).trans
  calc
    _ ≤ ∑ _q ∈ S.image (fun a ↦ (a.2 : ℚ) / a.1), H / (J + 1) := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
      exact Nat.div_le_div_left (hJ a ha) (Nat.succ_pos J)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]

/-- Positive integer pairs of canonical height at most J number at most
J*H*maxDivisorCount(H). Their canonical denominator is at most J, so the
existing divisor encoding applies without any congruence hypothesis. -/
theorem card_positive_pairs_le_of_height_upper {S : Finset (ℕ × ℕ)} {H J : ℕ}
    (hS : ∀ a ∈ S, 0 < a.1 ∧ a.1 ≤ H ∧ 0 < a.2 ∧ a.2 ≤ H)
    (hJ : ∀ a ∈ S, rationalPairHeight ((a.2 : ℚ) / a.1) ≤ J) :
    S.card ≤ J * H * maxDivisorCount H := by
  classical
  have hs : S ⊆ S.filter (fun a ↦ ((a.2 : ℚ) / a.1).den ≤ J) := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨ha, (le_max_right _ _).trans (hJ a ha)⟩
  exact (Finset.card_le_card hs).trans (card_small_denominator_pairs_le hS)

/-- Split a positive pair family at canonical height J. Bound the small-height
part by the divisor encoding and retain reciprocal-height weights above J.
The remaining sum can be partitioned into finitely many product-growth layers. -/
theorem card_positive_pairs_le_height_split {S : Finset (ℕ × ℕ)} {H J : ℕ}
    (hS : ∀ a ∈ S, 0 < a.1 ∧ a.1 ≤ H ∧ 0 < a.2 ∧ a.2 ≤ H) :
    S.card ≤
      J * H * maxDivisorCount H +
        ∑ q ∈ (S.image (fun a ↦ (a.2 : ℚ) / a.1)).filter (fun q ↦ J < rationalPairHeight q),
          H / rationalPairHeight q := by
  classical
  have hs :=
    card_positive_pairs_le_of_height_upper (J := J) (fun a ha ↦ hS a (Finset.mem_filter.mp ha).1)
      (fun a ha ↦ (Finset.mem_filter.mp ha).2)
  have hl :=
    card_positive_pairs_le_height_sum (H := H) (S :=
      S.filter (fun a ↦ ¬rationalPairHeight ((a.2 : ℚ) / a.1) ≤ J))
      (fun a ha ↦ hS a (Finset.mem_filter.mp ha).1)
  simp only [not_le] at hl
  rw [←
    Finset.filter_image (f := fun a : ℕ × ℕ ↦ (a.2 : ℚ) / a.1) (p := fun q : ℚ ↦
      J < rationalPairHeight q)] at hl
  rw [←
    Finset.card_filter_add_card_filter_not (s := S)
      (fun a ↦ rationalPairHeight ((a.2 : ℚ) / a.1) ≤ J)]
  simpa only [not_le] using Nat.add_le_add hs hl

/-- For odd p and H<p, split the actual signed congruence count into a
small-height divisor term and the remaining reciprocal-height sum. This is
the finite counting interface for the layered exponent improvement. -/
theorem boundedCongruenceCount_le_height_split {p H J : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hHp : H < p) :
    boundedCongruenceCount p H ≤
      4 *
        (J * H * maxDivisorCount H +
          ∑ q ∈ (positiveRatioSet p H).filter (fun q ↦ J < rationalPairHeight q),
            H / rationalPairHeight q) := by
  have hs :=
    card_positive_pairs_le_height_split (J := J)
      (positiveNaturalRatioPairs_bounds (p := p) (H := H))
  rw [card_positiveNaturalRatioPairs, positiveNaturalRatioPairs_image] at hs
  rw [boundedCongruenceCount_eq_ratioPairs_card hHp]
  exact (boundedRatioPairs_card_le_four_positive hodd).trans (Nat.mul_le_mul_left 4 hs)

end PseudoPrime.NumberTheory.Heilbronn
