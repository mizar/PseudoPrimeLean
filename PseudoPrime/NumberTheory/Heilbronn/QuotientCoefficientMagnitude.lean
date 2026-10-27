/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.DivisorPowerBounds

/-! # Symbolic double-exponential bounds for factorial coefficients -/

public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Every natural factorial is at most 2^(r²). Bound r by 2^r before
raising to r; no factorial is evaluated. This controls the two factorials
in the explicit quotient-growth coefficient. -/
theorem factorial_le_two_pow_square (r : ℕ) : r.factorial ≤ 2 ^ (r * r) := by
  calc
    _ ≤ r ^ r := Nat.factorial_le_pow r
    _ ≤ (2 ^ r) ^ r := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := r)).le r
    _ = _ := (pow_mul 2 r r).symm

/-- Bound the factorial using the binary length of its argument. Since
`r < 2^(log2 r + 1)`, the elementary estimate `r! ≤ r^r` gives an exponent
`r (log2 r + 1)` instead of `r^2`. This sharper input reduces the exponent
in the quotient coefficient bound. -/
theorem factorial_le_two_pow_log (r : ℕ) : r.factorial ≤ 2 ^ (r * (Nat.log2 r + 1)) := by
  have hlog : r < 2 ^ (Nat.log2 r + 1) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self Nat.one_lt_two r
  have hpow : r ^ r ≤ (2 ^ (Nat.log2 r + 1)) ^ r := Nat.pow_le_pow_left hlog.le r
  calc
    r.factorial ≤ r ^ r := Nat.factorial_le_pow r
    _ ≤ (2 ^ (Nat.log2 r + 1)) ^ r := hpow
    _ = 2 ^ ((Nat.log2 r + 1) * r) := by rw [← pow_mul]
    _ = 2 ^ (r * (Nat.log2 r + 1)) := by rw [Nat.mul_comm]

/-- For r≥4, the polynomial 5r²+5r+4 is at most 4^r. Induct from four
and use that its next value is at most four times its current value.
This absorbs all polynomial factors in the quotient coefficient exponent. -/
theorem coefficient_quadratic_le_four_pow {r : ℕ} (hr : 4 ≤ r) : 5 * r ^ 2 + 5 * r + 4 ≤ 4 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num only
  | succ n _hn ih =>
    rw [pow_succ 4 n]
    nlinarith only [ih, Nat.zero_le n]

/-- For r≥4, the quotient-coefficient polynomial is at most 2^(2r-1).
Induct from four and use that the next polynomial value is at most four
times the current one. -/
theorem coefficient_quadratic_le_half_four_pow {r : ℕ} (hr : 4 ≤ r) :
    5 * r ^ 2 + 5 * r + 4 ≤ 2 ^ (2 * r - 1) := by
  induction r, hr using Nat.le_induction with
  | base => norm_num only
  | succ n hn
    ih =>
    have hpoly : 5 * (n + 1) ^ 2 + 5 * (n + 1) + 4 ≤ 4 * (5 * n ^ 2 + 5 * n + 4) := by
      nlinarith only
    calc
      _ ≤ 4 * (5 * n ^ 2 + 5 * n + 4) := hpoly
      _ ≤ 4 * 2 ^ (2 * n - 1) := Nat.mul_le_mul_left _ ih
      _ = 2 ^ ((2 * n - 1) + 2) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num only, ← pow_add]
        congr 1
        omega
      _ = 2 ^ (2 * (n + 1) - 1) := by
        congr 1
        omega

/-- For r≥7, the quotient-coefficient polynomial is at most 2^(2r-2).
Induct from seven and use the factor-four growth of the polynomial. -/
theorem coefficient_quadratic_le_quarter_four_pow {r : ℕ} (hr : 7 ≤ r) :
    5 * r ^ 2 + 5 * r + 4 ≤ 2 ^ (2 * r - 2) := by
  induction r, hr using Nat.le_induction with
  | base => norm_num only
  | succ n hn
    ih =>
    have hpoly : 5 * (n + 1) ^ 2 + 5 * (n + 1) + 4 ≤ 4 * (5 * n ^ 2 + 5 * n + 4) := by
      nlinarith only
    calc
      _ ≤ 4 * (5 * n ^ 2 + 5 * n + 4) := hpoly
      _ ≤ 4 * 2 ^ (2 * n - 2) := Nat.mul_le_mul_left _ ih
      _ = 2 ^ ((2 * n - 2) + 2) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num only, ← pow_add, Nat.add_comm]
      _ = 2 ^ (2 * (n + 1) - 2) := by
        congr 1
        omega

/-- For r≥4, the explicit quotient coefficient Q_r is at most 2^(2^(4r)).
Keep the factorials and powers symbolic, bound factorials by powers of two,
and absorb the resulting quadratic in 2^(2r). This is the magnitude bound
needed for a concrete finite-fiber prime threshold. -/
theorem quotientPowerBoundConstant_le_double_exp {r : ℕ} (hr : 4 ≤ r) :
    quotientPowerBoundConstant r ≤ 2 ^ (2 ^ (4 * r)) := by
  have hf := factorial_le_two_pow_square r
  have hf2 := factorial_le_two_pow_square (2 * r)
  have hbase : (2 * r).factorial * 2 ^ (2 * r) ≤ 2 ^ (4 * r ^ 2 + 2 * r) := by
    calc
      _ ≤ 2 ^ ((2 * r) * (2 * r)) * 2 ^ (2 * r) := Nat.mul_le_mul_right _ hf2
      _ = _ := by
        rw [← pow_add]; congr 1; ring
  have hdiv : divisorPowerBoundConstant (2 * r) ≤ 2 ^ ((4 * r ^ 2 + 2 * r) * 2 ^ (2 * r)) := by
    have hexp : 2 ^ (2 * r - 1) ≤ 2 ^ (2 * r) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le _ _)
    calc
      _ ≤ ((2 * r).factorial * 2 ^ (2 * r)) ^ (2 ^ (2 * r - 1)) :=
        divisorPowerBoundConstant_le_half (2 * r)
      _ ≤ (2 ^ (4 * r ^ 2 + 2 * r)) ^ (2 ^ (2 * r - 1)) := Nat.pow_le_pow_left hbase _
      _ = 2 ^ ((4 * r ^ 2 + 2 * r) * 2 ^ (2 * r - 1)) := by rw [pow_mul]
      _ ≤ 2 ^ ((4 * r ^ 2 + 2 * r) * 2 ^ (2 * r)) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.mul_le_mul_left _ hexp)
  have h8 : (8 : ℕ) ^ r = 2 ^ (3 * r) := by rw [show (8 : ℕ) = 2 ^ 3 by norm_num only, ← pow_mul]
  have hfront : 8 ^ r * (9 * r.factorial) ≤ 2 ^ (3 * r + 4 + r ^ 2) := by
    rw [h8]
    calc
      _ ≤ 2 ^ (3 * r) * (2 ^ 4 * 2 ^ (r * r)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (by norm_num only : 9 ≤ (2 : ℕ) ^ 4) hf)
      _ = _ := by
        rw [← pow_add, ← pow_add]; congr 1; ring
  have hQ :
    quotientPowerBoundConstant r ≤
      2 ^ ((3 * r + 4 + r ^ 2) + (4 * r ^ 2 + 2 * r) * 2 ^ (2 * r)) := by
    exact (Nat.mul_le_mul hfront hdiv).trans_eq (pow_add 2 _ _).symm
  have hquad : (3 * r + 4 + r ^ 2) + (4 * r ^ 2 + 2 * r) ≤ 2 ^ (2 * r) := by
    have h := coefficient_quadratic_le_four_pow hr
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num only, ← pow_mul] at h
    nlinarith only [h]
  have hT : 1 ≤ (2 : ℕ) ^ (2 * r) := Nat.one_le_pow _ _ (by decide)
  have hA := Nat.mul_le_mul_left (3 * r + 4 + r ^ 2) hT
  have hexp : (3 * r + 4 + r ^ 2) + (4 * r ^ 2 + 2 * r) * 2 ^ (2 * r) ≤ 2 ^ (4 * r) := by
    calc
      _ ≤ ((3 * r + 4 + r ^ 2) + (4 * r ^ 2 + 2 * r)) * 2 ^ (2 * r) := by nlinarith only [hA]
      _ ≤ 2 ^ (2 * r) * 2 ^ (2 * r) := Nat.mul_le_mul_right _ hquad
      _ = _ := by
        rw [← pow_add]; congr 1; ring
  exact hQ.trans (Nat.pow_le_pow_right (by decide : 0 < 2) hexp)

/-- Bound the quotient coefficient using logarithmic factorial estimates and the
half-sized set of small prime factors. -/
theorem quotientPowerBoundConstant_le_double_exp_log {r : ℕ} (hr : 4 ≤ r) :
    quotientPowerBoundConstant r ≤
      2 ^ (2 ^ (2 * r + Nat.log2 (2 * r * (Nat.log2 (2 * r) + 1) + 2 * r))) := by
  let P : ℕ := 2 * r * (Nat.log2 (2 * r) + 1) + 2 * r
  let s : ℕ := Nat.log2 P + 1
  have hf := factorial_le_two_pow_log r
  have hf2 := factorial_le_two_pow_log (2 * r)
  have hbase : (2 * r).factorial * 2 ^ (2 * r) ≤ 2 ^ P := by
    calc
      _ ≤ 2 ^ ((2 * r) * (Nat.log2 (2 * r) + 1)) * 2 ^ (2 * r) := Nat.mul_le_mul_right _ hf2
      _ = _ := by rw [← pow_add]
  have hdiv : divisorPowerBoundConstant (2 * r) ≤ 2 ^ (P * 2 ^ (2 * r - 1)) := by
    calc
      _ ≤ ((2 * r).factorial * 2 ^ (2 * r)) ^ (2 ^ (2 * r - 1)) :=
        divisorPowerBoundConstant_le_half (2 * r)
      _ ≤ (2 ^ P) ^ (2 ^ (2 * r - 1)) := Nat.pow_le_pow_left hbase _
      _ = 2 ^ (P * 2 ^ (2 * r - 1)) := by rw [pow_mul]
  have h8 : (8 : ℕ) ^ r = 2 ^ (3 * r) := by rw [show (8 : ℕ) = 2 ^ 3 by norm_num only, ← pow_mul]
  have hfront : 8 ^ r * (9 * r.factorial) ≤ 2 ^ (3 * r + 4 + r * (Nat.log2 r + 1)) := by
    rw [h8]
    calc
      _ ≤ 2 ^ (3 * r) * (2 ^ 4 * 2 ^ (r * (Nat.log2 r + 1))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (by norm_num only : 9 ≤ (2 : ℕ) ^ 4) hf)
      _ = _ := by
        rw [← pow_add, ← pow_add]; congr 1; ring
  have hQ :
    quotientPowerBoundConstant r ≤
      2 ^ ((3 * r + 4 + r * (Nat.log2 r + 1)) + P * 2 ^ (2 * r - 1)) := by
    exact (Nat.mul_le_mul hfront hdiv).trans_eq (pow_add 2 _ _).symm
  have hlogr : Nat.log2 r + 1 ≤ r := by
    have h := Nat.log_lt_self 2 (by omega : r ≠ 0)
    rw [← Nat.log2_eq_log_two] at h
    omega
  have hlog2r : Nat.log2 (2 * r) + 1 ≤ 2 * r := by
    have h := Nat.log_lt_self 2 (by omega : 2 * r ≠ 0)
    rw [← Nat.log2_eq_log_two] at h
    omega
  have hfrontPoly : 3 * r + 4 + r * (Nat.log2 r + 1) ≤ 3 * r + 4 + r ^ 2 := by
    have h := Nat.mul_le_mul_left r hlogr
    nlinarith only [h]
  have hPPoly : P ≤ 4 * r ^ 2 + 2 * r := by
    have h := Nat.mul_le_mul_left (2 * r) hlog2r
    dsimp only [P]
    nlinarith only [h]
  have hquad : (3 * r + 4 + r * (Nat.log2 r + 1)) + P ≤ 2 ^ (2 * r - 1) := by
    calc
      _ ≤ (3 * r + 4 + r ^ 2) + (4 * r ^ 2 + 2 * r) := Nat.add_le_add hfrontPoly hPPoly
      _ ≤ 2 ^ (2 * r - 1) := by
        have h := coefficient_quadratic_le_half_four_pow hr
        nlinarith only [h]
  have hfront_le : 3 * r + 4 + r * (Nat.log2 r + 1) ≤ 2 ^ (2 * r - 1) := by
    exact (Nat.le_add_right _ _).trans hquad
  have hP : P < 2 ^ s := by
    dsimp only [s]
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self Nat.one_lt_two P
  have hPs : P + 1 ≤ 2 ^ s := Nat.succ_le_of_lt hP
  have hexp : (3 * r + 4 + r * (Nat.log2 r + 1)) + P * 2 ^ (2 * r - 1) ≤ 2 ^ (2 * r - 1 + s) := by
    calc
      _ ≤ 2 ^ (2 * r - 1) + P * 2 ^ (2 * r - 1) := Nat.add_le_add_right hfront_le _
      _ = (P + 1) * 2 ^ (2 * r - 1) := by ring
      _ ≤ 2 ^ s * 2 ^ (2 * r - 1) := Nat.mul_le_mul_right _ hPs
      _ = 2 ^ (2 * r - 1 + s) := by rw [← pow_add, Nat.add_comm]
  have hexp' :
    (3 * r + 4 + r * (Nat.log2 r + 1)) + P * 2 ^ (2 * r - 1) ≤ 2 ^ (2 * r + Nat.log2 P) := by
    dsimp only [s] at hexp ⊢
    convert hexp using 1
    congr 1
    omega
  have hexp'' :
    (3 * r + 4 + r * (Nat.log2 r + 1)) + P * 2 ^ (2 * r - 1) ≤
      2 ^ (2 * r + Nat.log2 (2 * r * (Nat.log2 (2 * r) + 1) + 2 * r)) := by
    simpa only [P] using hexp'
  exact hQ.trans (Nat.pow_le_pow_right (by decide : 0 < 2) hexp'')

/-- For r≥7, retain the quarter-sized prime range in the divisor factor and
save one unit in the double-exponential exponent of the quotient coefficient. -/
theorem quotientPowerBoundConstant_le_double_exp_log_quarter {r : ℕ} (hr : 7 ≤ r) :
    quotientPowerBoundConstant r ≤
      2 ^ (2 ^ (2 * r - 1 + Nat.log2 (2 * r * (Nat.log2 (2 * r) + 1) + 2 * r))) := by
  let P : ℕ := 2 * r * (Nat.log2 (2 * r) + 1) + 2 * r
  let s : ℕ := Nat.log2 P + 1
  have hf := factorial_le_two_pow_log r
  have hf2 := factorial_le_two_pow_log (2 * r)
  have hbase : (2 * r).factorial * 2 ^ (2 * r) ≤ 2 ^ P := by
    calc
      _ ≤ 2 ^ ((2 * r) * (Nat.log2 (2 * r) + 1)) * 2 ^ (2 * r) := Nat.mul_le_mul_right _ hf2
      _ = _ := by rw [← pow_add]
  have hdiv : divisorPowerBoundConstant (2 * r) ≤ 2 ^ (P * 2 ^ (2 * r - 2)) := by
    have hquarter : 14 ≤ 2 * r := by omega
    unfold divisorPowerBoundConstant
    rw [divisorPowerBoundExponent, ite_eq_left hquarter]
    calc
      _ ≤ (2 ^ P) ^ (2 ^ (2 * r - 2)) := Nat.pow_le_pow_left hbase _
      _ = 2 ^ (P * 2 ^ (2 * r - 2)) := by rw [pow_mul]
  have h8 : (8 : ℕ) ^ r = 2 ^ (3 * r) := by rw [show (8 : ℕ) = 2 ^ 3 by norm_num only, ← pow_mul]
  have hfront : 8 ^ r * (9 * r.factorial) ≤ 2 ^ (3 * r + 4 + r * (Nat.log2 r + 1)) := by
    rw [h8]
    calc
      _ ≤ 2 ^ (3 * r) * (2 ^ 4 * 2 ^ (r * (Nat.log2 r + 1))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (by norm_num only : 9 ≤ (2 : ℕ) ^ 4) hf)
      _ = _ := by
        rw [← pow_add, ← pow_add]; congr 1; ring
  have hQ :
    quotientPowerBoundConstant r ≤
      2 ^ ((3 * r + 4 + r * (Nat.log2 r + 1)) + P * 2 ^ (2 * r - 2)) := by
    exact (Nat.mul_le_mul hfront hdiv).trans_eq (pow_add 2 _ _).symm
  have hlogr : Nat.log2 r + 1 ≤ r := by
    have h := Nat.log_lt_self 2 (by omega : r ≠ 0)
    rw [← Nat.log2_eq_log_two] at h
    omega
  have hlog2r : Nat.log2 (2 * r) + 1 ≤ 2 * r := by
    have h := Nat.log_lt_self 2 (by omega : 2 * r ≠ 0)
    rw [← Nat.log2_eq_log_two] at h
    omega
  have hfrontPoly : 3 * r + 4 + r * (Nat.log2 r + 1) ≤ 3 * r + 4 + r ^ 2 := by
    have h := Nat.mul_le_mul_left r hlogr
    nlinarith only [h]
  have hPPoly : P ≤ 4 * r ^ 2 + 2 * r := by
    have h := Nat.mul_le_mul_left (2 * r) hlog2r
    dsimp only [P]
    nlinarith only [h]
  have hquad : (3 * r + 4 + r * (Nat.log2 r + 1)) + P ≤ 2 ^ (2 * r - 2) := by
    calc
      _ ≤ (3 * r + 4 + r ^ 2) + (4 * r ^ 2 + 2 * r) := Nat.add_le_add hfrontPoly hPPoly
      _ ≤ 2 ^ (2 * r - 2) := by
        have h := coefficient_quadratic_le_quarter_four_pow hr
        nlinarith only [h]
  have hfront_le : 3 * r + 4 + r * (Nat.log2 r + 1) ≤ 2 ^ (2 * r - 2) := by
    exact (Nat.le_add_right _ _).trans hquad
  have hP : P < 2 ^ s := by
    dsimp only [s]
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self Nat.one_lt_two P
  have hPs : P + 1 ≤ 2 ^ s := Nat.succ_le_of_lt hP
  have hexp : (3 * r + 4 + r * (Nat.log2 r + 1)) + P * 2 ^ (2 * r - 2) ≤ 2 ^ (2 * r - 2 + s) := by
    calc
      _ ≤ 2 ^ (2 * r - 2) + P * 2 ^ (2 * r - 2) := Nat.add_le_add_right hfront_le _
      _ = (P + 1) * 2 ^ (2 * r - 2) := by ring
      _ ≤ 2 ^ s * 2 ^ (2 * r - 2) := Nat.mul_le_mul_right _ hPs
      _ = 2 ^ (2 * r - 2 + s) := by rw [← pow_add, Nat.add_comm]
  have hexp' :
    (3 * r + 4 + r * (Nat.log2 r + 1)) + P * 2 ^ (2 * r - 2) ≤ 2 ^ (2 * r - 1 + Nat.log2 P) := by
    dsimp only [s] at hexp ⊢
    convert hexp using 1
    congr 1
    omega
  have hexp'' :
    (3 * r + 4 + r * (Nat.log2 r + 1)) + P * 2 ^ (2 * r - 2) ≤
      2 ^ (2 * r - 1 + Nat.log2 (2 * r * (Nat.log2 (2 * r) + 1) + 2 * r)) := by
    simpa only [P] using hexp'
  exact hQ.trans (Nat.pow_le_pow_right (by decide : 0 < 2) hexp'')

end PseudoPrime.NumberTheory.Heilbronn
