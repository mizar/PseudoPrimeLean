/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.RationalPairNormalization
public import PseudoPrime.NumberTheory.Heilbronn.RationalDivisorIncidence

/-! # Integer-pair multiplicities from a denominator cutoff -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For positive natural pairs bounded by H, the number whose ratio has canonical denominator
at most J is at most J*H*maxDivisorCount(H). Encode a pair by that denominator, its raw second
coordinate and its canonical numerator, which divides the second coordinate. -/
theorem card_small_denominator_pairs_le {S : Finset (ℕ × ℕ)} {H J : ℕ}
    (hS : ∀ a ∈ S, 0 < a.1 ∧ a.1 ≤ H ∧ 0 < a.2 ∧ a.2 ≤ H) :
    (S.filter (fun a ↦ ((a.2 : ℚ) / a.1).den ≤ J)).card ≤ J * H * maxDivisorCount H := by
  classical
  let F : (ℕ × ℕ) → Σ _ : ℕ × ℕ, ℕ := fun a ↦
    ⟨(((a.2 : ℚ) / a.1).den, a.2), ((a.2 : ℚ) / a.1).num.natAbs⟩
  have hc :=
    Finset.card_le_card_of_injOn (s := S.filter (fun a ↦ ((a.2 : ℚ) / a.1).den ≤ J)) (t :=
      (Finset.Icc 1 J ×ˢ Finset.Icc 1 H).sigma (fun a ↦ a.2.divisors)) F
      (by
        intro a ha
        have hm := Finset.mem_filter.mp ha
        have h := hS a hm.1
        apply Finset.mem_sigma.mpr
        refine
          ⟨Finset.mem_product.mpr
              ⟨Finset.mem_Icc.mpr ⟨Rat.den_pos _, hm.2⟩, Finset.mem_Icc.mpr ⟨h.2.2.1, h.2.2.2⟩⟩,
            ?_⟩
        exact
          Nat.mem_divisors.mpr
            ⟨(fraction_component_dvd_of_den_pos (a := a.2) h.1).1, ne_of_gt h.2.2.1⟩)
      (by
        intro a ha b hb he
        have hsa := hS a (Finset.mem_filter.mp ha).1
        have hsb := hS b (Finset.mem_filter.mp hb).1
        have hd : ((a.2 : ℚ) / a.1).den = ((b.2 : ℚ) / b.1).den :=
          congrArg (fun z : Σ _ : ℕ × ℕ, ℕ ↦ z.1.1) he
        have hy : a.2 = b.2 := congrArg (fun z : Σ _ : ℕ × ℕ, ℕ ↦ z.1.2) he
        have hn : ((a.2 : ℚ) / a.1).num.natAbs = ((b.2 : ℚ) / b.1).num.natAbs :=
          congrArg Sigma.snd he
        exact
          nat_pair_eq_of_ratio_and_second hsa.1 hsb.1 hsa.2.2.1
            (positive_rat_eq_of_num_den
              (div_pos (Nat.cast_pos.mpr hsa.2.2.1) (Nat.cast_pos.mpr hsa.1))
              (div_pos (Nat.cast_pos.mpr hsb.2.2.1) (Nat.cast_pos.mpr hsb.1)) hn hd)
            hy)
  rw [Finset.card_sigma] at hc
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 J ×ˢ Finset.Icc 1 H, a.2.divisors.card := hc
    _ ≤ ∑ _a ∈ Finset.Icc 1 J ×ˢ Finset.Icc 1 H, maxDivisorCount H := by
      exact
        Finset.sum_le_sum
          (fun a ha ↦
            divisors_card_le_maxDivisorCount (Finset.mem_Icc.mp (Finset.mem_product.mp ha).2).2)
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_product, Nat.card_Icc,
        Nat.add_sub_cancel, Nat.cast_id]

/-- For positive natural pairs bounded by H, those whose ratio denominator exceeds J number
at most card(ratios)*floor(H/(J+1)). Encode each by its rational ratio and the positive
quotient of its first coordinate by the canonical denominator; reconstruct both coordinates. -/
theorem card_large_denominator_pairs_le {S : Finset (ℕ × ℕ)} {H J : ℕ}
    (hS : ∀ a ∈ S, 0 < a.1 ∧ a.1 ≤ H ∧ 0 < a.2 ∧ a.2 ≤ H) :
    (S.filter (fun a ↦ ¬((a.2 : ℚ) / a.1).den ≤ J)).card ≤
      (S.image (fun a ↦ (a.2 : ℚ) / a.1)).card * (H / (J + 1)) := by
  classical
  let F : (ℕ × ℕ) → Σ _ : ℚ, ℕ := fun a ↦ ⟨(a.2 : ℚ) / a.1, a.1 / ((a.2 : ℚ) / a.1).den⟩
  have hc :=
    Finset.card_le_card_of_injOn (s := S.filter (fun a ↦ ¬((a.2 : ℚ) / a.1).den ≤ J)) (t :=
      (S.image (fun a ↦ (a.2 : ℚ) / a.1)).sigma (fun _ ↦ Finset.Icc 1 (H / (J + 1)))) F
      (by
        intro a ha
        have hm := Finset.mem_filter.mp ha
        have h := hS a hm.1
        have hd := (fraction_component_dvd_of_den_pos (a := a.2) h.1).2
        apply Finset.mem_sigma.mpr
        refine ⟨Finset.mem_image.mpr ⟨a, hm.1, rfl⟩, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
        · exact Nat.div_pos (Nat.le_of_dvd h.1 hd) (Rat.den_pos _)
        · exact
            (Nat.div_le_div_right h.2.1).trans
              (Nat.div_le_div_left (Nat.lt_of_not_ge hm.2) (Nat.succ_pos J)))
      (by
        intro a ha b hb he
        have hsa := hS a (Finset.mem_filter.mp ha).1
        have hsb := hS b (Finset.mem_filter.mp hb).1
        have hq : (a.2 : ℚ) / a.1 = (b.2 : ℚ) / b.1 := congrArg Sigma.fst he
        have hg : a.1 / ((a.2 : ℚ) / a.1).den = b.1 / ((b.2 : ℚ) / b.1).den := congrArg Sigma.snd he
        have hd := congrArg Rat.den hq
        have hda := (fraction_component_dvd_of_den_pos (a := a.2) hsa.1).2
        have hdb := (fraction_component_dvd_of_den_pos (a := b.2) hsb.1).2
        have hx : a.1 = b.1 := by
          calc
            _ = ((a.2 : ℚ) / a.1).den * (a.1 / ((a.2 : ℚ) / a.1).den) :=
              (Nat.mul_div_cancel' hda).symm
            _ = ((b.2 : ℚ) / b.1).den * (b.1 / ((b.2 : ℚ) / b.1).den) := by rw [hg, hd]
            _ = _ := Nat.mul_div_cancel' hdb
        apply Prod.ext hx
        rw [hx] at hq
        exact Nat.cast_inj.mp ((div_left_inj' (Nat.cast_ne_zero.mpr (ne_of_gt hsb.1))).mp hq))
  simpa only [Finset.card_sigma, Nat.card_Icc, Nat.add_sub_cancel, Finset.sum_const, nsmul_eq_mul,
    Nat.cast_id] using hc

/-- For any finite family of positive natural pairs in the H-square and any natural J, bound
its cardinality by J*H*T(H)+card(ratios)*floor(H/(J+1)). Partition by canonical denominator
and combine the two injective encodings, retaining multiplicities of equal rational values. -/
theorem card_positive_pairs_le_denominator_split {S : Finset (ℕ × ℕ)} {H J : ℕ}
    (hS : ∀ a ∈ S, 0 < a.1 ∧ a.1 ≤ H ∧ 0 < a.2 ∧ a.2 ≤ H) :
    S.card ≤
      J * H * maxDivisorCount H + (S.image (fun a ↦ (a.2 : ℚ) / a.1)).card * (H / (J + 1)) := by
  classical
  rw [← Finset.card_filter_add_card_filter_not (s := S) (fun a ↦ ((a.2 : ℚ) / a.1).den ≤ J)]
  exact Nat.add_le_add (card_small_denominator_pairs_le hS) (card_large_denominator_pairs_le hS)

/-- For natural R,H, the product R*floor(H/(sqrt(R)+1)) is at most H*(sqrt(R)+1).
Multiply by the positive denominator, apply the integer square-root inequality and cancel. -/
theorem sqrt_division_product_bound (R H : ℕ) :
    R * (H / (Nat.sqrt R + 1)) ≤ H * (Nat.sqrt R + 1) := by
  apply Nat.le_of_mul_le_mul_right (c := Nat.sqrt R + 1) _ (Nat.succ_pos _)
  have h1 := Nat.mul_le_mul_left R (Nat.div_mul_le_self H (Nat.sqrt R + 1))
  have h2 := Nat.mul_le_mul_right H (Nat.lt_succ_sqrt R).le
  nlinarith only [h1, h2]

/-- For positive H and a finite family S of positive pairs in the H-square, its cardinality
squared is at most 9*H^2*T(H)^2*card(ratios). Set the denominator cutoff to the integer
square root of card(ratios).
Handle an empty ratio set separately and retain all integer-pair multiplicities. -/
theorem card_positive_pairs_sq_le {S : Finset (ℕ × ℕ)} {H : ℕ} (hH : 0 < H)
    (hS : ∀ a ∈ S, 0 < a.1 ∧ a.1 ≤ H ∧ 0 < a.2 ∧ a.2 ≤ H) :
    S.card ^ 2 ≤ 9 * H ^ 2 * maxDivisorCount H ^ 2 * (S.image (fun a ↦ (a.2 : ℚ) / a.1)).card := by
  classical
  let R := (S.image (fun a ↦ (a.2 : ℚ) / a.1)).card
  have ht : 1 ≤ maxDivisorCount H := by
    simpa only [Nat.divisors_one, Finset.card_singleton] using
      (divisors_card_le_maxDivisorCount (d := 1) hH)
  by_cases hR : R = 0
  · have he : S = ∅ := Finset.image_eq_empty.mp (Finset.card_eq_zero.mp hR)
    rw [he, Finset.card_empty, zero_pow (by decide : 2 ≠ 0)]
    exact Nat.zero_le _
  · have hj : 1 ≤ Nat.sqrt R := Nat.le_sqrt.mpr (Nat.pos_of_ne_zero hR)
    have hc := card_positive_pairs_le_denominator_split (J := Nat.sqrt R) hS
    have hd := sqrt_division_product_bound R H
    have hprod := Nat.mul_le_mul_left (H * Nat.sqrt R) ht
    have hroot := Nat.mul_le_mul_left H hj
    have hb : S.card ≤ 3 * H * maxDivisorCount H * Nat.sqrt R := by
      dsimp only [R] at hd hprod hroot ⊢
      nlinarith only [hc, hd, hprod, hroot]
    have hs := Nat.pow_le_pow_left hb 2
    have hr := Nat.mul_le_mul_left (9 * H ^ 2 * maxDivisorCount H ^ 2) (Nat.sqrt_le R)
    nlinarith only [hs, hr]

end PseudoPrime.NumberTheory.Heilbronn
