/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TwoAdicCorrections

/-! # Retained finite-cutoff savings in reciprocal prime-power corrections -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For a nonzero real base p, arbitrary weights a,x and finite exponent set S,
the tapered sum equals the untapered sum minus card(S)*a/x. Expand each term
using totalized division. This retains finite savings for full or odd exponents. -/
theorem sum_tapered_powers_eq {p : ℝ} (hp : p ≠ 0) (a x : ℝ) (S : Finset ℕ) :
    (∑ k ∈ S, a / p ^ k * (1 - p ^ k / x)) = (∑ k ∈ S, a / p ^ k) - S.card * a / x := by
  have he : ∀ k : ℕ, a / p ^ k * (1 - p ^ k / x) = a / p ^ k - a / x := by
    intro k
    rw [mul_sub, mul_one, ← mul_div_assoc, div_mul_cancel₀ _ (pow_ne_zero k hp)]
  rw [Finset.sum_congr rfl (fun k _ ↦ he k), Finset.sum_sub_distrib, Finset.sum_const]
  simp only [nsmul_eq_mul]
  ring

/-- For any real cutoff and primitive value zero at two, the reciprocal
correction is at most log 2 minus K*log 2/x, where K=floor(log x/log 2).
Retain the taper subtraction before bounding the geometric sum. -/
theorem twoAdicReciprocalCorrection_le_tapered_zero {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q)
    (h2 : χ.primitiveCharacter 2 = 0) :
    twoAdicReciprocalCorrection x χ ≤
      Real.log 2 - (⌊Real.log x / Real.log 2⌋₊ : ℝ) * Real.log 2 / x := by
  let K := ⌊Real.log x / Real.log 2⌋₊
  have he :
    twoAdicReciprocalCorrection x χ =
      ∑ k ∈ Finset.Icc 1 K, Real.log 2 / (2 : ℝ) ^ k * (1 - (2 : ℝ) ^ k / x) := by
    rw [twoAdicReciprocalCorrection_eq_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : k ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hk).1
    simp only [h2, zero_pow hk0, Complex.zero_re, mul_zero, sub_zero]
  rw [he, sum_tapered_powers_eq (by norm_num only), Nat.card_Icc, Nat.add_sub_cancel]
  have hs := sum_log_div_prime_pow_le (N := K) Nat.prime_two
  norm_num only [Nat.cast_ofNat, div_one] at hs
  exact sub_le_sub_right hs _

/-- For primitive value minus one at two, the reciprocal correction is at most
(4/3)log 2 minus 2*log 2/x for each odd exponent through floor(log x/log 2).
Use the exact odd-exponent formula and retain the taper before the geometric bound. -/
theorem twoAdicReciprocalCorrection_le_tapered_neg_one {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q)
    (h2 : χ.primitiveCharacter 2 = -1) :
    twoAdicReciprocalCorrection x χ ≤
      (4 / 3 : ℝ) * Real.log 2 -
        ((Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊).filter Odd).card * (2 * Real.log 2) / x := by
  let K := ⌊Real.log x / Real.log 2⌋₊
  let S := (Finset.Icc 1 K).filter Odd
  have he :
    twoAdicReciprocalCorrection x χ =
      ∑ k ∈ S, (2 * Real.log 2) / (2 : ℝ) ^ k * (1 - (2 : ℝ) ^ k / x) := by
    rw [twoAdicReciprocalCorrection_eq_odd_sum_of_apply_two_eq_neg_one x χ h2]
    rw [show S = (Finset.Icc 1 K).filter Odd from rfl, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs
    · ring
    · rfl
  rw [he, sum_tapered_powers_eq (by norm_num only)]
  have hsum :
    (∑ k ∈ S, (2 * Real.log 2) / (2 : ℝ) ^ k) =
      2 * Real.log 2 * (∑ k ∈ Finset.Icc 1 K, if Odd k then (1 : ℝ) / (2 : ℝ) ^ k else 0) := by
    rw [← Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum]
  have hs :=
    mul_le_mul_of_nonneg_left (sum_odd_inv_two_pow_le K)
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2)
        (Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 2)))
  have hb :
    2 * Real.log 2 * (∑ k ∈ Finset.Icc 1 K, if Odd k then (1 : ℝ) / (2 : ℝ) ^ k else 0) ≤
      (4 / 3 : ℝ) * Real.log 2 := by
    linarith only [hs]
  exact sub_le_sub_right hb _

end PseudoPrime.AnalyticNumberTheory.Arithmetic
