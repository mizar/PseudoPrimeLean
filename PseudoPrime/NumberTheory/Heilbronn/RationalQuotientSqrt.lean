/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.RationalSliceTail
import PseudoPrime.NumberTheory.Heilbronn.RationalQuotientBase

/-! # A square-root-height quotient-set bound -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For positive rational families of heights Q,D and positive r,s, their slice-cardinality
product times r*s is at most Q*D*card(A/B). Apply the initial quotient estimate to the
scaled slices and retain the decrease in height before multiplying by the indices. -/
theorem slice_product_mul_indices_le {A B : Finset ℚ} {Q D r s : ℕ}
    (hA : ∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D)
    (hB : ∀ q ∈ B, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D) (hr : 0 < r) (hs : 0 < s) :
    ((divisorSlice A r s).card * (divisorSlice B r s).card) * (r * s) ≤
      (Q * D) * (rationalQuotientSet A B).card := by
  have h :=
    slice_product_le_of_recursive_bound hA hB hr hs
      (fun A' B' hA' hB' ↦ rational_quotient_base_bound hB')
  have hh := Nat.mul_le_mul (Nat.div_mul_le_self Q r) (Nat.div_mul_le_self D s)
  have ht := Nat.mul_le_mul_right (r * s) h
  have hu := Nat.mul_le_mul_right (rationalQuotientSet A B).card hh
  nlinarith only [ht, hu]

/-- For an occurring gcd pair beyond a positive cutoff x, bound its slice-cardinality product
by Q*D*card(A/B)/x. The indices are positive and their product exceeds the cutoff;
cast the weighted natural slice bound and divide by x. -/
theorem large_slice_product_le {A B : Finset ℚ} {Q D x : ℕ}
    (hA : ∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D)
    (hB : ∀ q ∈ B, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D) (hx : 0 < x) {rs : ℕ × ℕ}
    (hrs : rs ∈ (quotientGcdIndex A B).filter (fun rs ↦ ¬rs.1 * rs.2 ≤ x)) :
    ((divisorSlice A rs.1 rs.2).card : ℝ) * (divisorSlice B rs.1 rs.2).card ≤
      ((Q * D : ℕ) : ℝ) * (rationalQuotientSet A B).card / x := by
  classical
  have hm := Finset.mem_filter.mp hrs
  have hp := quotientGcdIndex_pos (fun q hq ↦ (hA q hq).1) hm.1
  have hi := slice_product_mul_indices_le hA hB hp.1 hp.2
  have hn :=
    (Nat.mul_le_mul_left ((divisorSlice A rs.1 rs.2).card * (divisorSlice B rs.1 rs.2).card)
          (Nat.le_of_lt (Nat.lt_of_not_ge hm.2))).trans
      hi
  apply (le_div_iff₀ (Nat.cast_pos.mpr hx)).mpr
  have hc := Nat.cast_le (α := ℝ).mpr hn
  simpa only [Nat.cast_mul] using hc

/-- For positive rational families of heights Q,D, choose a positive natural cutoff x with
Q*D at most x^2. Then card(A)*card(B) is at most
4*x*(1+log x)*card(A/B)*maxDivisorCount(Q*D)^2.
The scaled initial quotient bound controls the large slices; Cauchy--Schwarz makes their
sum at most half the total if the displayed conclusion fails, contradicting the cutoff bound.
This gives the square-root-height stage without assuming the full Cilleruelo induction. -/
theorem rational_quotient_sqrt_cutoff_bound {A B : Finset ℚ} {Q D x : ℕ}
    (hA : ∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D)
    (hB : ∀ q ∈ B, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D) (hx : 0 < x) (hheight : Q * D ≤ x ^ 2) :
    (A.card : ℝ) * B.card ≤
      4 *
        (((x : ℝ) * (1 + Real.log x)) *
          ((rationalQuotientSet A B).card * (maxDivisorCount (Q * D) : ℝ) ^ 2)) := by
  classical
  let R : ℝ := (rationalQuotientSet A B).card
  let T : ℝ := maxDivisorCount (Q * D)
  let U : ℝ := (Q * D : ℕ)
  let P : ℝ := (x : ℝ) * (1 + Real.log x) * (R * T ^ 2)
  let C : ℝ := U * R / x
  have hxR : (0 : ℝ) < x := Nat.cast_pos.mpr hx
  have hl : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hx)
  have hR : 0 ≤ R := Nat.cast_nonneg _
  have hU : 0 ≤ U := Nat.cast_nonneg _
  have hC : 0 ≤ C := div_nonneg (mul_nonneg hU hR) (le_of_lt hxR)
  have hP : 0 ≤ P :=
    mul_nonneg (mul_nonneg (le_of_lt hxR) (by linarith only [hl])) (mul_nonneg hR (sq_nonneg T))
  have hu : U ≤ (x : ℝ) ^ 2 := by
    have h := Nat.cast_le (α := ℝ).mpr hheight
    simpa only [Nat.cast_pow] using h
  have hdiv : U / (x : ℝ) ≤ (x : ℝ) * (1 + Real.log x) := by
    apply (div_le_iff₀ hxR).mpr
    nlinarith only [hu, mul_nonneg (sq_nonneg (x : ℝ)) hl]
  have hCT : C * T ^ 2 ≤ P := by
    have h := mul_le_mul_of_nonneg_right hdiv (mul_nonneg hR (sq_nonneg T))
    dsimp only [C, P]
    calc
      _ = (U / (x : ℝ)) * (R * T ^ 2) := by ring
      _ ≤ _ := h
  by_contra hn
  have hneg : 4 * P < (A.card : ℝ) * B.card := lt_of_not_ge hn
  have hab : 0 ≤ (A.card : ℝ) * B.card := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hbudget : C * ((A.card : ℝ) * T) * ((B.card : ℝ) * T) ≤ ((A.card : ℝ) * B.card / 2) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hCT hab
    nlinarith only [h, mul_le_mul_of_nonneg_right (le_of_lt hneg) hab]
  have hout :=
    rational_quotient_lower_of_small_slices hA hB hC
      (fun rs hrs ↦ large_slice_product_le hA hB hx hrs) hbudget
  change (A.card : ℝ) * B.card / 2 ≤ P at hout
  linarith only [hout, hneg, hP]

/-- At equal positive numerator and denominator height H, use cutoff H to obtain
card(A)*card(B) at most 4*H*(1+log H)*card(A/B)*maxDivisorCount(H^2)^2.
This is the explicit equal-height consequence of the square-root-height cutoff theorem. -/
theorem rational_quotient_equal_height_bound {A B : Finset ℚ} {H : ℕ}
    (hA : ∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ H ∧ q.den ≤ H)
    (hB : ∀ q ∈ B, 0 < q ∧ q.num.natAbs ≤ H ∧ q.den ≤ H) (hH : 0 < H) :
    (A.card : ℝ) * B.card ≤
      4 *
        (((H : ℝ) * (1 + Real.log H)) *
          ((rationalQuotientSet A B).card * (maxDivisorCount (H * H) : ℝ) ^ 2)) := by
  exact rational_quotient_sqrt_cutoff_bound hA hB hH (by rw [pow_two])

end PseudoPrime.NumberTheory.Heilbronn
