/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.RationalSliceDescent

/-! # Initial quotient-set bound for bounded rational families -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For positive rationals with canonical numerator at most Q and denominator at most D,
bound their finite cardinality by Q*D. The canonical numerator-denominator pair gives an
injection into the product of the two positive integer intervals. -/
theorem card_bounded_positive_rationals_le {A : Finset ℚ} {Q D : ℕ}
    (hA : ∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D) : A.card ≤ Q * D := by
  classical
  have hc :=
    Finset.card_le_card_of_injOn (s := A) (t := Finset.Icc 1 Q ×ˢ Finset.Icc 1 D)
      (fun q : ℚ ↦ (q.num.natAbs, q.den))
      (by
        intro q hq
        have h := hA q hq
        exact
          Finset.mem_product.mpr
            ⟨Finset.mem_Icc.mpr ⟨Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr h.1)), h.2.1⟩,
              Finset.mem_Icc.mpr ⟨q.den_pos, h.2.2⟩⟩)
      (by
        intro q hq t ht he
        have hn : q.num.natAbs = t.num.natAbs := congrArg Prod.fst he
        have hd : q.den = t.den := congrArg Prod.snd he
        calc
          q = (q.num.natAbs : ℚ) / q.den := positive_rat_nat_fraction (hA q hq).1
          _ = (t.num.natAbs : ℚ) / t.den := by rw [hn, hd]
          _ = t := (positive_rat_nat_fraction (hA t ht).1).symm)
  simpa only [Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel] using hc

/-- If B contains a nonzero rational, the quotient set A/B has at least as many elements as A.
Divide each element of A by that fixed element of B and use cancellation. -/
theorem card_left_le_quotientSet {A B : Finset ℚ} {b : ℚ} (hb : b ∈ B) (hb0 : b ≠ 0) :
    A.card ≤ (rationalQuotientSet A B).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun q : ℚ ↦ q / b)
  · intro q hq
    exact Finset.mem_image.mpr ⟨(q, b), Finset.mem_product.mpr ⟨hq, hb⟩, rfl⟩
  · intro q hq t ht he
    exact (div_left_inj' hb0).mp he

/-- If B is a family of positive rationals of heights Q,D, then
card(A)*card(B) is at most Q*D*card(A/B), without a positivity assumption on A.
For nonempty B combine the height count with injection into A/B; the empty case is immediate.
This is the initial quotient estimate for the Cilleruelo induction. -/
theorem rational_quotient_base_bound {A B : Finset ℚ} {Q D : ℕ}
    (hB : ∀ q ∈ B, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D) :
    A.card * B.card ≤ Q * D * (rationalQuotientSet A B).card := by
  classical
  by_cases hb : B = ∅
  · rw [hb, Finset.card_empty, mul_zero]
    exact Nat.zero_le _
  · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hb
    have ha := card_left_le_quotientSet (A := A) hb (ne_of_gt (hB b hb).1)
    have hc := Nat.mul_le_mul ha (card_bounded_positive_rationals_le hB)
    simpa only [Nat.mul_comm] using hc

end PseudoPrime.NumberTheory.Heilbronn
