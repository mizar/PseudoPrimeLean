/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.RationalDivisorIncidence
public import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Logarithmic cutoff bounds for rational quotient sets -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For a finite family of positive integer pairs with product at most x, bound its cardinality
by the sum of floor(x/r). Inject into the finite hyperbola using the two coordinates. -/
theorem card_positive_product_indices_le {x : ℕ} (S : Finset (ℕ × ℕ))
    (hS : ∀ rs ∈ S, 0 < rs.1 ∧ 0 < rs.2 ∧ rs.1 * rs.2 ≤ x) :
    S.card ≤ ∑ r ∈ Finset.Icc 1 x, x / r := by
  classical
  have hc :=
    Finset.card_le_card_of_injOn (s := S) (t :=
      (Finset.Icc 1 x).sigma (fun r ↦ Finset.Icc 1 (x / r)))
      (fun rs : ℕ × ℕ ↦ (⟨rs.1, rs.2⟩ : Σ _ : ℕ, ℕ))
      (by
        intro rs hrs
        have h := hS rs hrs
        apply Finset.mem_sigma.mpr
        exact
          ⟨Finset.mem_Icc.mpr ⟨h.1, (Nat.le_mul_of_pos_right rs.1 h.2.1).trans h.2.2⟩,
            Finset.mem_Icc.mpr
              ⟨h.2.1, (Nat.le_div_iff_mul_le h.1).mpr ((Nat.mul_comm rs.2 rs.1) ▸ h.2.2)⟩⟩)
      (by
        intro a ha b hb he
        exact Prod.ext (congrArg Sigma.fst he) (congrArg Sigma.snd he))
  simpa only [Finset.card_sigma, Nat.card_Icc, Nat.add_sub_cancel] using hc

/-- For every natural cutoff x, bound the floor-division sum by x*(1+log x).
Compare termwise with the harmonic sum, including the zero-cutoff case. -/
theorem sum_nat_div_le_log (x : ℕ) :
    ((∑ r ∈ Finset.Icc 1 x, x / r : ℕ) : ℝ) ≤ (x : ℝ) * (1 + Real.log x) := by
  calc
    _ = ∑ r ∈ Finset.Icc 1 x, ((x / r : ℕ) : ℝ) := Nat.cast_sum _ _
    _ ≤ ∑ r ∈ Finset.Icc 1 x, (x : ℝ) / r := Finset.sum_le_sum (fun r hr ↦ Nat.cast_div_le)
    _ = (x : ℝ) * (harmonic x : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, div_eq_mul_inv,
        Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log x) (Nat.cast_nonneg x)

/-- For positive first rational family, every occurring numerator and denominator gcd is positive.
Extract its representing pair; positivity permits hyperbola counting. -/
theorem quotientGcdIndex_pos {A B : Finset ℚ} (hA : ∀ q ∈ A, 0 < q) {rs : ℕ × ℕ}
    (hrs : rs ∈ quotientGcdIndex A B) : 0 < rs.1 ∧ 0 < rs.2 := by
  classical
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hrs
  have hqa := hA q.1 (Finset.mem_product.mp hq).1
  exact
    ⟨Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hqa))),
      Nat.gcd_pos_of_pos_left _ q.1.den_pos⟩

/-- For positive first family, count occurring gcd pairs whose product is at most x.
Combine their positivity with the harmonic hyperbola bound. -/
theorem card_small_quotientGcdIndex_le_log {A B : Finset ℚ} {x : ℕ} (hA : ∀ q ∈ A, 0 < q) :
    (((quotientGcdIndex A B).filter (fun rs ↦ rs.1 * rs.2 ≤ x)).card : ℝ) ≤
      (x : ℝ) * (1 + Real.log x) := by
  classical
  have hc :=
    card_positive_product_indices_le ((quotientGcdIndex A B).filter (fun rs ↦ rs.1 * rs.2 ≤ x))
      (by
        intro rs hrs
        have hm := Finset.mem_filter.mp hrs
        have hp := quotientGcdIndex_pos hA hm.1
        exact ⟨hp.1, hp.2, hm.2⟩)
  exact (Nat.cast_le.mpr hc).trans (sum_nat_div_le_log x)

/-- For positive rational families bounded by numerator Q and denominator D, bound their
cardinality product by x*(1+log x)*card(A/B)*T^2 plus the large-gcd slice-product sum.
Cast the exact finite partition bound and apply logarithmic hyperbola counting.
This is the cutoff inequality used before the inductive quotient-set lower bound. -/
theorem rational_quotient_log_cutoff_bound {A B : Finset ℚ} {Q D x : ℕ}
    (hA : ∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D)
    (hB : ∀ q ∈ B, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D) :
    (A.card : ℝ) * B.card ≤
      ((x : ℝ) * (1 + Real.log x)) *
          ((rationalQuotientSet A B).card * (maxDivisorCount (Q * D) : ℝ) ^ 2) +
        ∑ rs ∈ (quotientGcdIndex A B).filter (fun rs ↦ ¬rs.1 * rs.2 ≤ x),
          ((divisorSlice A rs.1 rs.2).card : ℝ) * (divisorSlice B rs.1 rs.2).card := by
  classical
  have hc : ((A.card * B.card : ℕ) : ℝ) ≤ _ :=
    Nat.cast_le.mpr (rational_quotient_cutoff_bound (x := x) hA hB)
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_sum, Nat.cast_pow] at hc
  exact
    hc.trans
      (add_le_add
        (mul_le_mul_of_nonneg_right (card_small_quotientGcdIndex_le_log (fun q hq ↦ (hA q hq).1))
          (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
        (le_refl _))

end PseudoPrime.NumberTheory.Heilbronn
