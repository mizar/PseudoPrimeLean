/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.RationalHyperbolaBounds

/-! # Cauchy--Schwarz bounds for large divisor slices -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For two nonnegative real families whose pointwise products are at most C, bound the square
of the sum of their products by C times the product of their separate sums.
Apply the finite Cauchy--Schwarz inequality with weights C*a and b. -/
theorem sum_products_sq_le {ι : Type*} (S : Finset ι) (a b : ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ i ∈ S, 0 ≤ a i) (hb : ∀ i ∈ S, 0 ≤ b i) (hab : ∀ i ∈ S, a i * b i ≤ C) :
    (∑ i ∈ S, a i * b i) ^ 2 ≤ C * (∑ i ∈ S, a i) * (∑ i ∈ S, b i) := by
  have h :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S (f := fun i ↦ C * a i) (g := b) (r := fun i ↦
      a i * b i) (fun i hi ↦ mul_nonneg hC (ha i hi)) hb
      (by
        intro i hi
        have ht := mul_le_mul_of_nonneg_right (hab i hi) (mul_nonneg (ha i hi) (hb i hi))
        nlinarith only [ht])
  simpa only [← Finset.mul_sum] using h

/-- For bounded positive rational families and any finite set of divisor indices, a uniform
bound C on slice-cardinality products gives a squared tail bound C*card(A)*T*card(B)*T.
Combine Cauchy--Schwarz with the two divisor-incidence sum bounds. -/
theorem divisor_slice_tail_sq_le {A B : Finset ℚ} {Q D : ℕ}
    (hA : ∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D)
    (hB : ∀ q ∈ B, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D) (S : Finset (ℕ × ℕ)) {C : ℝ} (hC : 0 ≤ C)
    (hsmall :
      ∀ rs ∈ S, ((divisorSlice A rs.1 rs.2).card : ℝ) * (divisorSlice B rs.1 rs.2).card ≤ C) :
    (∑ rs ∈ S, ((divisorSlice A rs.1 rs.2).card : ℝ) * (divisorSlice B rs.1 rs.2).card) ^ 2 ≤
      C * ((A.card : ℝ) * maxDivisorCount (Q * D)) * ((B.card : ℝ) * maxDivisorCount (Q * D)) := by
  have ha :
    (∑ rs ∈ S, ((divisorSlice A rs.1 rs.2).card : ℝ)) ≤ (A.card : ℝ) * maxDivisorCount (Q * D) := by
    have h := Nat.cast_le (α := ℝ).mpr (sum_card_divisorSlice_le_maxDivisor hA S)
    simpa only [Nat.cast_sum, Nat.cast_mul] using h
  have hb :
    (∑ rs ∈ S, ((divisorSlice B rs.1 rs.2).card : ℝ)) ≤ (B.card : ℝ) * maxDivisorCount (Q * D) := by
    have h := Nat.cast_le (α := ℝ).mpr (sum_card_divisorSlice_le_maxDivisor hB S)
    simpa only [Nat.cast_sum, Nat.cast_mul] using h
  have ht :=
    sum_products_sq_le S (fun rs ↦ ((divisorSlice A rs.1 rs.2).card : ℝ))
      (fun rs ↦ ((divisorSlice B rs.1 rs.2).card : ℝ)) hC (fun _ _ ↦ Nat.cast_nonneg _)
      (fun _ _ ↦ Nat.cast_nonneg _) hsmall
  exact
    ht.trans
      (mul_le_mul (mul_le_mul_of_nonneg_left ha hC) hb
        (Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _))
        (mul_nonneg hC (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))))

/-- For bounded positive rational families, suppose all slice products beyond cutoff x are
at most C and the squared tail budget is at most (card(A)*card(B)/2)^2.
Then the small-index logarithmic quotient term is at least half the cardinality product.
Compare the nonnegative half-product with the squared tail bound and subtract the tail.
This supplies the small-slices branch of the quotient-set induction. -/
theorem rational_quotient_lower_of_small_slices {A B : Finset ℚ} {Q D x : ℕ}
    (hA : ∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D)
    (hB : ∀ q ∈ B, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D) {C : ℝ} (hC : 0 ≤ C)
    (hsmall :
      ∀ rs ∈ (quotientGcdIndex A B).filter (fun rs ↦ ¬rs.1 * rs.2 ≤ x),
        ((divisorSlice A rs.1 rs.2).card : ℝ) * (divisorSlice B rs.1 rs.2).card ≤ C)
    (hbudget :
      C * ((A.card : ℝ) * maxDivisorCount (Q * D)) * ((B.card : ℝ) * maxDivisorCount (Q * D)) ≤
        ((A.card : ℝ) * B.card / 2) ^ 2) :
    (A.card : ℝ) * B.card / 2 ≤
      ((x : ℝ) * (1 + Real.log x)) *
        ((rationalQuotientSet A B).card * (maxDivisorCount (Q * D) : ℝ) ^ 2) := by
  classical
  have ht :=
    (divisor_slice_tail_sq_le hA hB ((quotientGcdIndex A B).filter (fun rs ↦ ¬rs.1 * rs.2 ≤ x)) hC
          hsmall).trans
      hbudget
  have hc := rational_quotient_log_cutoff_bound (x := x) hA hB
  have hp : 0 ≤ (A.card : ℝ) * B.card / 2 :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by norm_num only)
  have htail :
    (∑ rs ∈ (quotientGcdIndex A B).filter (fun rs ↦ ¬rs.1 * rs.2 ≤ x),
        ((divisorSlice A rs.1 rs.2).card : ℝ) * (divisorSlice B rs.1 rs.2).card) ≤
      (A.card : ℝ) * B.card / 2 := by
    nlinarith only [ht, hp]
  linarith only [hc, htail]

end PseudoPrime.NumberTheory.Heilbronn
