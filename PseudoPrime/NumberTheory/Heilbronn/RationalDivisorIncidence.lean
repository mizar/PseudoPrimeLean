/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.RationalQuotientCells

/-! # Divisor counting for rational quotient sets -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For a positive rational family A and any finite divisor-index set, the total
slice incidence is at most sum_q tau(num(q)*den(q)). Interchange the two finite counts,
embed each index fiber into the divisor product, and use reduced coprimality. -/
theorem sum_card_divisorSlice_le {A : Finset ℚ} (hA : ∀ q ∈ A, 0 < q) (S : Finset (ℕ × ℕ)) :
    (∑ rs ∈ S, (divisorSlice A rs.1 rs.2).card) ≤
      ∑ q ∈ A, (q.num.natAbs * q.den).divisors.card := by
  classical
  have he :
    (∑ rs ∈ S, (divisorSlice A rs.1 rs.2).card) =
      ∑ q ∈ A, (S.filter (fun rs ↦ rs.1 ∣ q.num.natAbs ∧ rs.2 ∣ q.den)).card := by
    simp only [divisorSlice, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [he]
  apply Finset.sum_le_sum
  intro q hq
  have hn : q.num.natAbs ≠ 0 :=
    Nat.ne_of_gt (Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr (hA q hq))))
  have hs :
    S.filter (fun rs ↦ rs.1 ∣ q.num.natAbs ∧ rs.2 ∣ q.den) ⊆
      q.num.natAbs.divisors ×ˢ q.den.divisors := by
    intro rs hrs
    have hd := (Finset.mem_filter.mp hrs).2
    exact
      Finset.mem_product.mpr
        ⟨Nat.mem_divisors.mpr ⟨hd.1, hn⟩, Nat.mem_divisors.mpr ⟨hd.2, q.den_ne_zero⟩⟩
  exact
    (Finset.card_le_card hs).trans_eq
      ((Finset.card_product _ _).trans q.reduced.card_divisors_mul.symm)

/-- Maximum number of positive divisors among natural integers at most U.
This analytic bound is defined by a finite supremum; no large numeral is evaluated. -/
def maxDivisorCount (U : ℕ) : ℕ :=
  (Finset.range (U + 1)).sup (fun n ↦ n.divisors.card)

/-- For d<=U, its actual divisor count is at most the finite maximum at U. -/
theorem divisors_card_le_maxDivisorCount {d U : ℕ} (hd : d ≤ U) :
    d.divisors.card ≤ maxDivisorCount U :=
  Finset.le_sup (f := fun n : ℕ ↦ n.divisors.card) (Finset.mem_range.mpr (Nat.lt_succ_of_le hd))

/-- For positive rational inputs with numerators at most Q and denominators at most D,
the canonical quotient numerator and denominator are at most Q*D. Use the gcd-cofactor formulas. -/
theorem quotient_height_le {q t : ℚ} (hq : 0 < q) (ht : 0 < t) {Q D : ℕ} (hqn : q.num.natAbs ≤ Q)
    (hqd : q.den ≤ D) (htn : t.num.natAbs ≤ Q) (htd : t.den ≤ D) :
    (q / t).num.natAbs ≤ Q * D ∧ (q / t).den ≤ Q * D := by
  have hf := positive_quotient_num_den hq ht
  rw [hf.1, hf.2]
  exact
    ⟨Nat.mul_le_mul ((Nat.div_le_self _ _).trans hqn) ((Nat.div_le_self _ _).trans htd),
      Nat.mul_le_mul ((Nat.div_le_self _ _).trans htn) ((Nat.div_le_self _ _).trans hqd)⟩

/-- For two bounded positive families, every quotient has both canonical divisor
counts bounded by maxDivisorCount(Q*D), using the proved quotient height control. -/
theorem quotientSet_divisor_bound {A B : Finset ℚ} {Q D : ℕ}
    (hA : ∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D)
    (hB : ∀ q ∈ B, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D) :
    ∀ z ∈ rationalQuotientSet A B,
      z.num.natAbs.divisors.card ≤ maxDivisorCount (Q * D) ∧
        z.den.divisors.card ≤ maxDivisorCount (Q * D) := by
  classical
  intro z hz
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hq
  have hqa := hA q.1 ha
  have hqb := hB q.2 hb
  have hh := quotient_height_le hqa.1 hqb.1 hqa.2.1 hqa.2.2 hqb.2.1 hqb.2.2
  exact ⟨divisors_card_le_maxDivisorCount hh.1, divisors_card_le_maxDivisorCount hh.2⟩

/-- For bounded positive rational families, every gcd class has at most
card(A/B)*maxDivisorCount(Q*D)^2 elements. Insert the actual finite divisor maximum. -/
theorem card_quotientGcdClass_le_maxDivisor {A B : Finset ℚ} {Q D r s : ℕ}
    (hA : ∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D)
    (hB : ∀ q ∈ B, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D) :
    (quotientGcdClass A B r s).card ≤
      (rationalQuotientSet A B).card * maxDivisorCount (Q * D) ^ 2 :=
  card_quotientGcdClass_le_of_divisor_bound (fun q hq ↦ (hA q hq).1) (fun q hq ↦ (hB q hq).1)
    (quotientSet_divisor_bound hA hB)

/-- For a bounded positive rational family, the total incidence over any finite
set of divisor pairs is at most card(A)*maxDivisorCount(Q*D).
Use the exact reduced divisor product. -/
theorem sum_card_divisorSlice_le_maxDivisor {A : Finset ℚ} {Q D : ℕ}
    (hA : ∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D) (S : Finset (ℕ × ℕ)) :
    (∑ rs ∈ S, (divisorSlice A rs.1 rs.2).card) ≤ A.card * maxDivisorCount (Q * D) := by
  calc
    _ ≤ ∑ q ∈ A, (q.num.natAbs * q.den).divisors.card :=
      sum_card_divisorSlice_le (fun q hq ↦ (hA q hq).1) S
    _ ≤ ∑ _q ∈ A, maxDivisorCount (Q * D) := by
      apply Finset.sum_le_sum
      intro q hq
      exact divisors_card_le_maxDivisorCount (Nat.mul_le_mul (hA q hq).2.1 (hA q hq).2.2)
    _ = _ := Finset.sum_const_nat (fun _ _ ↦ rfl)

/-- The finite set of numerator-gcd and denominator-gcd pairs actually occurring in A times B.
It indexes a disjoint exhaustive partition, including empty input families. -/
noncomputable def quotientGcdIndex (A B : Finset ℚ) : Finset (ℕ × ℕ) := by
  classical exact (A ×ˢ B).image (fun q ↦ (q.1.num.natAbs.gcd q.2.num.natAbs, q.1.den.gcd q.2.den))

/-- The gcd classes indexed by occurring gcd pairs partition A times B exactly.
Apply finite fiber counting to obtain total cardinality card(A)*card(B). -/
theorem sum_card_quotientGcdClass (A B : Finset ℚ) :
    (∑ rs ∈ quotientGcdIndex A B, (quotientGcdClass A B rs.1 rs.2).card) = A.card * B.card := by
  classical
  have hf :
    ∀ rs : ℕ × ℕ,
      quotientGcdClass A B rs.1 rs.2 =
        (A ×ˢ B).filter
          (fun q ↦ (q.1.num.natAbs.gcd q.2.num.natAbs, q.1.den.gcd q.2.den) = rs) := by
    rintro ⟨r, s⟩
    ext q
    simp only [quotientGcdClass, Finset.mem_filter, Prod.mk.injEq]
  have he :=
    Finset.sum_card_fiberwise_eq_card_filter (A ×ˢ B) (quotientGcdIndex A B)
      (fun q ↦ (q.1.num.natAbs.gcd q.2.num.natAbs, q.1.den.gcd q.2.den))
  have ht :
    (A ×ˢ B).filter
        (fun q ↦ (q.1.num.natAbs.gcd q.2.num.natAbs, q.1.den.gcd q.2.den) ∈ quotientGcdIndex A B) =
      A ×ˢ B :=
    Finset.filter_eq_self.mpr (fun q hq ↦ Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  simp only [← hf, ht, Finset.card_product] at he
  exact he

/-- For bounded positive rational families and natural cutoff x, bound card(A)*card(B)
by the number of small gcd indices times card(A/B)*T^2 plus the large-index slice-product sum.
Partition exactly, apply the divisor bound to small indices and the slice bound to large ones. -/
theorem rational_quotient_cutoff_bound {A B : Finset ℚ} {Q D x : ℕ}
    (hA : ∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D)
    (hB : ∀ q ∈ B, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D) :
    A.card * B.card ≤
      ((quotientGcdIndex A B).filter (fun rs ↦ rs.1 * rs.2 ≤ x)).card *
          ((rationalQuotientSet A B).card * maxDivisorCount (Q * D) ^ 2) +
        ∑ rs ∈ (quotientGcdIndex A B).filter (fun rs ↦ ¬rs.1 * rs.2 ≤ x),
          (divisorSlice A rs.1 rs.2).card * (divisorSlice B rs.1 rs.2).card := by
  classical
  rw [← sum_card_quotientGcdClass]
  have he :=
    Finset.sum_filter_add_sum_filter_not (quotientGcdIndex A B) (fun rs ↦ rs.1 * rs.2 ≤ x)
      (fun rs ↦ (quotientGcdClass A B rs.1 rs.2).card)
  rw [← he]
  apply Nat.add_le_add
  · calc
      _ ≤
          ∑ _rs ∈ (quotientGcdIndex A B).filter (fun rs ↦ rs.1 * rs.2 ≤ x),
            ((rationalQuotientSet A B).card * maxDivisorCount (Q * D) ^ 2) :=
        by exact Finset.sum_le_sum (fun rs hrs ↦ card_quotientGcdClass_le_maxDivisor hA hB)
      _ = _ := Finset.sum_const_nat (fun _ _ ↦ rfl)
  · exact Finset.sum_le_sum (fun rs hrs ↦ card_quotientGcdClass_le_slices A B rs.1 rs.2)

end PseudoPrime.NumberTheory.Heilbronn
