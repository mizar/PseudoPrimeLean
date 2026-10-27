/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaEulerCorrected256

/-! # Contractive normalized finite Euler products -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a complex exponent and finite order.
Output: the product of j/(s+j) for 1<=j<=n, with empty product one.
Role: normalize the Euler approximation into contractive factors. -/
noncomputable def eulerUnitProduct (s : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => eulerUnitProduct s n * ((n + 1 : ℕ) : ℂ) / (s + ((n + 1 : ℕ) : ℂ))

/-- Input: Re(s)>=0 and a natural index.
Claim: the factor (n+1)/(s+n+1) has norm at most one.
Proof: the real part of the denominator is at least the positive numerator.
Role: keep sequential multiplication errors additive. -/
theorem eulerUnitFactor_norm_le_one {s : ℂ} (hs : 0 ≤ s.re) (n : ℕ) :
    ‖((n + 1 : ℕ) : ℂ) / (s + ((n + 1 : ℕ) : ℂ))‖ ≤ 1 := by
  have hp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have hre : (s + ((n + 1 : ℕ) : ℂ)).re = s.re + (n + 1 : ℕ) := by
    simp only [Complex.add_re, Complex.natCast_re]
  have hd : (0 : ℝ) < ‖s + ((n + 1 : ℕ) : ℂ)‖ :=
    lt_of_lt_of_le (by linarith only [hp, hs] : (0 : ℝ) < s.re + (n + 1 : ℕ))
      (hre ▸ (le_abs_self _).trans (Complex.abs_re_le_norm _))
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_one hd).mpr
  have h := (le_abs_self (s + ((n + 1 : ℕ) : ℂ)).re).trans (Complex.abs_re_le_norm _)
  rw [hre] at h
  linarith only [h, hs]

/-- Input: s different from zero and an order.
Claim: the normalized product equals n!*s divided by the Euler denominator product.
Proof: induct on the order using the factorial and finite-product recurrences.
Role: connect the stable product to the existing GammaSeq definition. -/
theorem eulerUnitProduct_eq_factorial_div (s : ℂ) (hs : s ≠ 0) (n : ℕ) :
    eulerUnitProduct s n = (n.factorial : ℂ) * s / (∏ j ∈ Finset.range (n + 1), (s + (j : ℂ))) := by
  induction n with
  | zero =>
    simp only [eulerUnitProduct, Nat.factorial_zero, Nat.cast_one, zero_add, Finset.prod_range_succ,
      Finset.prod_range_zero, Nat.cast_zero, add_zero, one_mul, div_self hs]
  | succ n ih =>
    rw [eulerUnitProduct, ih, Nat.factorial_succ, Nat.cast_mul]
    rw [Finset.prod_range_succ (n := n + 1)]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- Input: a contractive complex factor and a local multiplication error at most epsilon.
Claim: the total error after the step is at most epsilon plus the previous error.
Proof: factor the previous error and apply the triangle inequality.
Role: propagate numerical rounding without multiplying its bound at each step. -/
theorem norm_rounded_mul_error_le (z w a b : ℂ) {ε : ℝ} (ha : ‖a‖ ≤ 1) (hb : ‖b - z * a‖ ≤ ε) :
    ‖b - w * a‖ ≤ ε + ‖z - w‖ := by
  have he : b - w * a = (b - z * a) + (z - w) * a := by ring
  rw [he]
  exact
    (norm_add_le _ _).trans
      (add_le_add hb ((norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) ha)))

/-- Input: Re(s)>=0, an approximation starting at one and local errors at most epsilon.
Claim: the order-n product error is at most n*epsilon.
Proof: induct using the contractive-factor error propagation.
Role: justify bounded-size rounded product certificates. -/
theorem norm_approx_eulerUnitProduct_le {s : ℂ} (hs : 0 ≤ s.re) (z : ℕ → ℂ) (hz : z 0 = 1) {ε : ℝ}
    (hstep : ∀ n, ‖z (n + 1) - z n * (((n + 1 : ℕ) : ℂ) / (s + ((n + 1 : ℕ) : ℂ)))‖ ≤ ε) (n : ℕ) :
    ‖z n - eulerUnitProduct s n‖ ≤ (n : ℝ) * ε := by
  induction n with
  | zero => rw [hz, eulerUnitProduct, sub_self, norm_zero, Nat.cast_zero, zero_mul]
  | succ n ih =>
    rw [eulerUnitProduct, mul_div_assoc]
    have h :=
      norm_rounded_mul_error_le (z n) (eulerUnitProduct s n)
        (((n + 1 : ℕ) : ℂ) / (s + ((n + 1 : ℕ) : ℂ))) (z (n + 1)) (eulerUnitFactor_norm_le_one hs n)
        (hstep n)
    norm_num only [Nat.cast_add, Nat.cast_one] at h ⊢
    linarith only [h, ih]

/-- Input: a nonzero complex exponent and an order.
Claim: GammaSeq equals n^s/s times the normalized product.
Proof: apply the factorial quotient identity and cancel the nonzero exponent.
Role: transfer certified normalized products to the actual finite Gamma approximation. -/
theorem GammaSeq_eq_eulerUnitProduct (s : ℂ) (hs : s ≠ 0) (n : ℕ) :
    Complex.GammaSeq s n = (n : ℂ) ^ s / s * eulerUnitProduct s n := by
  rw [Complex.GammaSeq, eulerUnitProduct_eq_factorial_div s hs n]
  field_simp (discharger := exact hs)

end PseudoPrime.Analysis
