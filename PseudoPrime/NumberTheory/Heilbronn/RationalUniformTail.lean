/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.RationalQuotientSqrt

/-! # Natural coefficient bounds from uniform large-slice estimates -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For nonnegative total a and main term P, a cutoff inequality a at most P+t and squared
tail bound t^2 at most P*a imply a at most 4*P. If the conclusion fails, the tail is at
least a/2, contradicting the squared bound. This is the common numerical cutoff step. -/
theorem four_mul_main_of_cutoff {a P t : ℝ} (ha : 0 ≤ a) (hP : 0 ≤ P) (hcut : a ≤ P + t)
    (ht : t ^ 2 ≤ P * a) : a ≤ 4 * P := by
  by_contra hn
  have hn' : 4 * P < a := lt_of_not_ge hn
  have hhalf : 0 ≤ a / 2 := div_nonneg ha (by norm_num only)
  have hlow : a / 2 ≤ t := by linarith only [hcut, hn', hP]
  have hs := mul_self_le_mul_self hhalf hlow
  have hp := mul_le_mul_of_nonneg_right (le_of_lt hn') ha
  nlinarith only [hs, ht, hp, hn', hP]

/-- For bounded positive rational families, positive cutoff x, integer logarithm bound K,
and divisor-count bound T, suppose every large-index slice product is at most x*card(A/B).
Then card(A)*card(B) is at most 4*x*K*T^2*card(A/B).
Use Cauchy--Schwarz, the logarithmic cutoff inequality and the common numerical step.
All parameters remain natural, allowing the induction to use integer powers and cutoffs. -/
theorem quotient_bound_of_uniform_tail {A B : Finset ℚ} {Q D x K T : ℕ}
    (hA : ∀ q ∈ A, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D)
    (hB : ∀ q ∈ B, 0 < q ∧ q.num.natAbs ≤ Q ∧ q.den ≤ D) (hx : 0 < x)
    (hlog : 1 + Real.log (x : ℝ) ≤ K) (hT : maxDivisorCount (Q * D) ≤ T)
    (hsmall :
      ∀ rs ∈ (quotientGcdIndex A B).filter (fun rs ↦ ¬rs.1 * rs.2 ≤ x),
        (divisorSlice A rs.1 rs.2).card * (divisorSlice B rs.1 rs.2).card ≤
          x * (rationalQuotientSet A B).card) :
    A.card * B.card ≤ 4 * x * K * T ^ 2 * (rationalQuotientSet A B).card := by
  classical
  let S := (quotientGcdIndex A B).filter (fun rs ↦ ¬rs.1 * rs.2 ≤ x)
  let R : ℝ := (rationalQuotientSet A B).card
  let T0 : ℝ := maxDivisorCount (Q * D)
  let a : ℝ := (A.card : ℝ) * B.card
  let P : ℝ := (x : ℝ) * K * T0 ^ 2 * R
  let t : ℝ := ∑ rs ∈ S, ((divisorSlice A rs.1 rs.2).card : ℝ) * (divisorSlice B rs.1 rs.2).card
  have hR : 0 ≤ R := Nat.cast_nonneg _
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hP : 0 ≤ P :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg T0)) hR
  have hlog0 : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hx)
  have hK : (1 : ℝ) ≤ K := by linarith only [hlog, hlog0]
  have hcut : a ≤ P + t := by
    have h := rational_quotient_log_cutoff_bound hA hB (x := x)
    have he :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg x))
        (mul_nonneg hR (sq_nonneg T0))
    dsimp only [a, P, t, S, R, T0] at *
    nlinarith only [h, he]
  have ht : t ^ 2 ≤ P * a := by
    have h :=
      divisor_slice_tail_sq_le hA hB S (mul_nonneg (Nat.cast_nonneg x) hR)
        (by
          intro rs hrs
          have hc := Nat.cast_le (α := ℝ).mpr (hsmall rs hrs)
          simpa only [Nat.cast_mul] using hc)
    have he :=
      mul_le_mul_of_nonneg_right hK
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg x) hR) (mul_nonneg ha (sq_nonneg T0)))
    dsimp only [t, P, a, T0, R] at *
    nlinarith only [h, he]
  have hc := four_mul_main_of_cutoff ha hP hcut ht
  have hTreal := Nat.cast_le (α := ℝ).mpr hT
  have hs := mul_self_le_mul_self (Nat.cast_nonneg (maxDivisorCount (Q * D))) hTreal
  have hm :=
    mul_le_mul_of_nonneg_right hs
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) (Nat.cast_nonneg x))
          (Nat.cast_nonneg K))
        hR)
  have hout : (A.card : ℝ) * B.card ≤ 4 * (x : ℝ) * K * (T : ℝ) ^ 2 * R := by
    dsimp only [a, P] at hc
    nlinarith only [hc, hm]
  apply Nat.cast_le (α := ℝ).mp
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, R] using hout

end PseudoPrime.NumberTheory.Heilbronn
