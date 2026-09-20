/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ElementaryOmegaPowTwoBridge
import PseudoPrime.NumberTheory.PrimorialCertificates

/-!
# Finite certificates for `ElementaryOmegaFiniteStatement`, `1 <= m <= 162`

Each `elementaryCertificate_at_m` verifies
`(m + 1 : R) <= PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryOmegaRhsReal`
`(PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryAnchor m)` for one concrete `m`,
via the power-of-two reduction
`PseudoPrime.AnalyticNumberTheory.Arithmetic.certificate_of_powTwo_le_anchor`:
instead of a two-stage `Real.log` Taylor expansion on the exact (often hundreds-of-digits)
anchor value, each certificate only needs a `norm_num`-checkable power-of-two lower bound
`2 ^ e <= PseudoPrime.AnalyticNumberTheory.Arithmetic.elementaryAnchor m` (reusing
the cumulative primorial values from `PseudoPrime.NumberTheory.PrimorialCertificates` via
`PseudoPrime.AnalyticNumberTheory.Arithmetic.primePrimorialCount_succ_eq_two_mul_oddPrimorial`)
and a purely rational cross-multiplied inequality in `e`, `k`, and `m`.
Fixed rational denominators are cleared once by
`PseudoPrime.AnalyticNumberTheory.Arithmetic.certificate_rational_of_nat`;
each generated application checks a natural-number inequality.
The final dispatch names the corresponding certificate directly, avoiding a search through 162
local hypotheses. Regenerate marked blocks with `python tools/generate_omega_certificates.py`.
Each `(e, k)` pair is verified here through the power comparison and the natural inequality
`(m+1) * (3470*k*2^k + 3470*e) ≤ 4851*e*2^k + 5000*(m+1)*2^k`.
These checks prove the certificate without trusting the choice procedure for `(e, k)`.

The long-line linter is disabled for the generated certificate applications in this file.
-/

set_option linter.style.longLine false

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Clear the fixed rational denominators once; generated certificates check only naturals. -/
private theorem certificate_rational_of_nat {m e k : ℕ}
    (h : (m + 1) * (3470 * k * 2 ^ k + 3470 * e) ≤ 4851 * e * 2 ^ k + 5000 * (m + 1) * 2 ^ k) :
    ((m + 1 : ℕ) : ℝ) *
        ((k : ℝ) * ElementaryOmegaPowTwoBridgeInternal.logTwoUpper +
            (e : ℝ) * ElementaryOmegaPowTwoBridgeInternal.logTwoUpper / 2 ^ k -
          1) ≤
      elementaryOmegaConstant * ((e : ℝ) * ElementaryOmegaPowTwoBridgeInternal.logTwoLower) := by
  have hR :
    ((m : ℝ) + 1) * (3470 * k * (2 : ℝ) ^ k + 3470 * e) ≤
      4851 * e * (2 : ℝ) ^ k + 5000 * (m + 1) * (2 : ℝ) ^ k := by
    exact_mod_cast h
  norm_num only [ElementaryOmegaPowTwoBridgeInternal.logTwoUpper,
    ElementaryOmegaPowTwoBridgeInternal.logTwoLower, elementaryOmegaConstant, Nat.cast_add,
    Nat.cast_one]
  apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < 2 ^ k by positivity)).mp
  have hp : (2 : ℝ) ^ k ≠ 0 := by positivity
  field_simp
  nlinarith only [hR]

set_option exponentiation.threshold 3000 in
theorem elementaryCertificate_at_1 :
    ((1 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 1) := by
  have hOP : oddPrimorial 1 = 3 := by rw [oddPrimorial_succ, oddPrimorial_zero, oddPrime_zero]
  apply certificate_of_powTwo_le_anchor (e := 11) (k := 3) (by decide)
  · unfold elementaryAnchor
    rw [hOP]
    rw [max_eq_right (by norm_num only)]
    norm_num only
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
theorem elementaryCertificate_at_2 :
    ((2 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 2) := by
  have hOP : oddPrimorial 2 = 15 := by
    rw [oddPrimorial_succ, oddPrimorial_succ, oddPrimorial_zero, oddPrime_zero,
      oddPrime_eq_primeByIndex_succ, NumberTheory.primeByIndex_two]
  apply certificate_of_powTwo_le_anchor (e := 11) (k := 3) (by decide)
  · unfold elementaryAnchor
    rw [hOP]
    rw [max_eq_right (by norm_num only)]
    norm_num only
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
theorem elementaryCertificate_at_3 :
    ((3 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 3) := by
  have hOP : oddPrimorial 3 = 105 := by
    rw [oddPrimorial_succ, oddPrimorial_succ, oddPrimorial_succ, oddPrimorial_zero, oddPrime_zero,
      oddPrime_eq_primeByIndex_succ, NumberTheory.primeByIndex_two, oddPrime_eq_primeByIndex_succ,
      NumberTheory.primeByIndex_three]
  apply certificate_of_powTwo_le_anchor (e := 11) (k := 3) (by decide)
  · unfold elementaryAnchor
    rw [hOP]
    rw [max_eq_right (by norm_num only)]
    norm_num only
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
theorem elementaryCertificate_at_4 :
    ((4 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 4) := by
  have hOP : oddPrimorial 4 = 1155 := by
    rw [oddPrimorial_succ, oddPrimorial_succ, oddPrimorial_succ, oddPrimorial_succ,
      oddPrimorial_zero, oddPrime_zero, oddPrime_eq_primeByIndex_succ,
      NumberTheory.primeByIndex_two, oddPrime_eq_primeByIndex_succ, NumberTheory.primeByIndex_three,
      oddPrime_eq_primeByIndex_succ, NumberTheory.primeByIndex_four]
  apply certificate_of_powTwo_le_anchor (e := 12) (k := 3) (by decide)
  · unfold elementaryAnchor
    rw [hOP]
    rw [max_eq_left (by norm_num only)]
    norm_num only
  · exact certificate_rational_of_nat (by decide)

-- BEGIN GENERATED OMEGA CERTIFICATES
set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 5, from a generated integer certificate. -/
theorem elementaryCertificate_at_5 :
    ((5 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 5) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_six_eq) (e := 15) (k := 3)
      (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 6, from a generated integer certificate. -/
theorem elementaryCertificate_at_6 :
    ((6 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 6) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_7) (e := 19) (k :=
      4) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 7, from a generated integer certificate. -/
theorem elementaryCertificate_at_7 :
    ((7 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 7) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_8) (e := 24) (k :=
      4) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 8, from a generated integer certificate. -/
theorem elementaryCertificate_at_8 :
    ((8 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 8) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_9) (e := 28) (k :=
      4) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 9, from a generated integer certificate. -/
theorem elementaryCertificate_at_9 :
    ((9 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 9) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_10) (e := 33) (k :=
      5) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 10, from a generated integer certificate. -/
theorem elementaryCertificate_at_10 :
    ((10 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 10) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_11) (e := 38) (k :=
      5) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 11, from a generated integer certificate. -/
theorem elementaryCertificate_at_11 :
    ((11 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 11) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_12) (e := 43) (k :=
      5) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 12, from a generated integer certificate. -/
theorem elementaryCertificate_at_12 :
    ((12 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 12) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_13) (e := 49) (k :=
      5) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 13, from a generated integer certificate. -/
theorem elementaryCertificate_at_13 :
    ((13 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 13) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_14) (e := 54) (k :=
      5) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 14, from a generated integer certificate. -/
theorem elementaryCertificate_at_14 :
    ((14 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 14) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_15) (e := 60) (k :=
      5) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 15, from a generated integer certificate. -/
theorem elementaryCertificate_at_15 :
    ((15 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 15) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_16) (e := 65) (k :=
      6) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 16, from a generated integer certificate. -/
theorem elementaryCertificate_at_16 :
    ((16 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 16) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_17) (e := 71) (k :=
      6) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 17, from a generated integer certificate. -/
theorem elementaryCertificate_at_17 :
    ((17 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 17) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_18) (e := 77) (k :=
      6) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 18, from a generated integer certificate. -/
theorem elementaryCertificate_at_18 :
    ((18 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 18) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_19) (e := 83) (k :=
      6) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 19, from a generated integer certificate. -/
theorem elementaryCertificate_at_19 :
    ((19 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 19) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_20) (e := 89) (k :=
      6) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 20, from a generated integer certificate. -/
theorem elementaryCertificate_at_20 :
    ((20 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 20) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_21) (e := 96) (k :=
      6) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 21, from a generated integer certificate. -/
theorem elementaryCertificate_at_21 :
    ((21 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 21) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_22) (e := 102) (k :=
      6) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 22, from a generated integer certificate. -/
theorem elementaryCertificate_at_22 :
    ((22 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 22) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_23) (e := 108) (k :=
      6) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 23, from a generated integer certificate. -/
theorem elementaryCertificate_at_23 :
    ((23 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 23) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_24) (e := 115) (k :=
      6) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 24, from a generated integer certificate. -/
theorem elementaryCertificate_at_24 :
    ((24 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 24) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_25) (e := 121) (k :=
      6) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 25, from a generated integer certificate. -/
theorem elementaryCertificate_at_25 :
    ((25 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 25) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_26) (e := 128) (k :=
      7) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 26, from a generated integer certificate. -/
theorem elementaryCertificate_at_26 :
    ((26 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 26) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_27) (e := 135) (k :=
      7) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 27, from a generated integer certificate. -/
theorem elementaryCertificate_at_27 :
    ((27 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 27) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_28) (e := 141) (k :=
      7) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 28, from a generated integer certificate. -/
theorem elementaryCertificate_at_28 :
    ((28 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 28) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_29) (e := 148) (k :=
      7) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 29, from a generated integer certificate. -/
theorem elementaryCertificate_at_29 :
    ((29 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 29) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_30) (e := 155) (k :=
      7) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 30, from a generated integer certificate. -/
theorem elementaryCertificate_at_30 :
    ((30 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 30) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_31) (e := 162) (k :=
      7) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 31, from a generated integer certificate. -/
theorem elementaryCertificate_at_31 :
    ((31 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 31) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_32) (e := 169) (k :=
      7) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 32, from a generated integer certificate. -/
theorem elementaryCertificate_at_32 :
    ((32 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 32) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_33) (e := 176) (k :=
      7) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 33, from a generated integer certificate. -/
theorem elementaryCertificate_at_33 :
    ((33 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 33) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_34) (e := 183) (k :=
      7) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 34, from a generated integer certificate. -/
theorem elementaryCertificate_at_34 :
    ((34 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 34) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_35) (e := 190) (k :=
      7) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 35, from a generated integer certificate. -/
theorem elementaryCertificate_at_35 :
    ((35 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 35) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_36) (e := 198) (k :=
      7) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 36, from a generated integer certificate. -/
theorem elementaryCertificate_at_36 :
    ((36 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 36) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_37) (e := 205) (k :=
      7) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 37, from a generated integer certificate. -/
theorem elementaryCertificate_at_37 :
    ((37 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 37) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_38) (e := 212) (k :=
      7) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 38, from a generated integer certificate. -/
theorem elementaryCertificate_at_38 :
    ((38 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 38) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_39) (e := 220) (k :=
      7) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 39, from a generated integer certificate. -/
theorem elementaryCertificate_at_39 :
    ((39 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 39) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_40) (e := 227) (k :=
      7) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 40, from a generated integer certificate. -/
theorem elementaryCertificate_at_40 :
    ((40 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 40) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_41) (e := 235) (k :=
      7) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 41, from a generated integer certificate. -/
theorem elementaryCertificate_at_41 :
    ((41 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 41) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_42) (e := 242) (k :=
      7) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 42, from a generated integer certificate. -/
theorem elementaryCertificate_at_42 :
    ((42 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 42) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_43) (e := 250) (k :=
      7) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 43, from a generated integer certificate. -/
theorem elementaryCertificate_at_43 :
    ((43 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 43) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_44) (e := 257) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 44, from a generated integer certificate. -/
theorem elementaryCertificate_at_44 :
    ((44 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 44) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_45) (e := 265) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 45, from a generated integer certificate. -/
theorem elementaryCertificate_at_45 :
    ((45 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 45) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_46) (e := 273) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 46, from a generated integer certificate. -/
theorem elementaryCertificate_at_46 :
    ((46 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 46) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_47) (e := 280) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 47, from a generated integer certificate. -/
theorem elementaryCertificate_at_47 :
    ((47 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 47) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_48) (e := 288) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 48, from a generated integer certificate. -/
theorem elementaryCertificate_at_48 :
    ((48 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 48) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_49) (e := 296) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 49, from a generated integer certificate. -/
theorem elementaryCertificate_at_49 :
    ((49 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 49) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_50) (e := 304) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 50, from a generated integer certificate. -/
theorem elementaryCertificate_at_50 :
    ((50 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 50) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_51) (e := 312) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 51, from a generated integer certificate. -/
theorem elementaryCertificate_at_51 :
    ((51 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 51) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_52) (e := 319) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 52, from a generated integer certificate. -/
theorem elementaryCertificate_at_52 :
    ((52 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 52) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_53) (e := 327) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 53, from a generated integer certificate. -/
theorem elementaryCertificate_at_53 :
    ((53 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 53) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_54) (e := 335) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 54, from a generated integer certificate. -/
theorem elementaryCertificate_at_54 :
    ((54 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 54) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_55) (e := 343) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 55, from a generated integer certificate. -/
theorem elementaryCertificate_at_55 :
    ((55 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 55) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_56) (e := 351) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 56, from a generated integer certificate. -/
theorem elementaryCertificate_at_56 :
    ((56 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 56) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_57) (e := 359) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 57, from a generated integer certificate. -/
theorem elementaryCertificate_at_57 :
    ((57 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 57) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_58) (e := 368) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 58, from a generated integer certificate. -/
theorem elementaryCertificate_at_58 :
    ((58 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 58) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_59) (e := 376) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 59, from a generated integer certificate. -/
theorem elementaryCertificate_at_59 :
    ((59 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 59) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_60) (e := 384) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 60, from a generated integer certificate. -/
theorem elementaryCertificate_at_60 :
    ((60 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 60) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_61) (e := 392) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 61, from a generated integer certificate. -/
theorem elementaryCertificate_at_61 :
    ((61 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 61) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_62) (e := 400) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 62, from a generated integer certificate. -/
theorem elementaryCertificate_at_62 :
    ((62 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 62) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_63) (e := 408) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 63, from a generated integer certificate. -/
theorem elementaryCertificate_at_63 :
    ((63 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 63) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_64) (e := 417) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 64, from a generated integer certificate. -/
theorem elementaryCertificate_at_64 :
    ((64 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 64) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_65) (e := 425) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 65, from a generated integer certificate. -/
theorem elementaryCertificate_at_65 :
    ((65 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 65) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_66) (e := 433) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 66, from a generated integer certificate. -/
theorem elementaryCertificate_at_66 :
    ((66 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 66) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_67) (e := 442) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 67, from a generated integer certificate. -/
theorem elementaryCertificate_at_67 :
    ((67 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 67) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_68) (e := 450) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 68, from a generated integer certificate. -/
theorem elementaryCertificate_at_68 :
    ((68 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 68) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_69) (e := 459) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 69, from a generated integer certificate. -/
theorem elementaryCertificate_at_69 :
    ((69 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 69) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_70) (e := 467) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 70, from a generated integer certificate. -/
theorem elementaryCertificate_at_70 :
    ((70 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 70) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_71) (e := 475) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 71, from a generated integer certificate. -/
theorem elementaryCertificate_at_71 :
    ((71 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 71) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_72) (e := 484) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 72, from a generated integer certificate. -/
theorem elementaryCertificate_at_72 :
    ((72 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 72) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_73) (e := 492) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 73, from a generated integer certificate. -/
theorem elementaryCertificate_at_73 :
    ((73 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 73) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_74) (e := 501) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 74, from a generated integer certificate. -/
theorem elementaryCertificate_at_74 :
    ((74 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 74) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_75) (e := 510) (k :=
      8) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 75, from a generated integer certificate. -/
theorem elementaryCertificate_at_75 :
    ((75 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 75) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_76) (e := 518) (k :=
      9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 76, from a generated integer certificate. -/
theorem elementaryCertificate_at_76 :
    ((76 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 76) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_77) (e := 527) (k :=
      9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 77, from a generated integer certificate. -/
theorem elementaryCertificate_at_77 :
    ((77 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 77) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_78) (e := 535) (k :=
      9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 78, from a generated integer certificate. -/
theorem elementaryCertificate_at_78 :
    ((78 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 78) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_79) (e := 544) (k :=
      9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 79, from a generated integer certificate. -/
theorem elementaryCertificate_at_79 :
    ((79 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 79) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_80) (e := 553) (k :=
      9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 80, from a generated integer certificate. -/
theorem elementaryCertificate_at_80 :
    ((80 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 80) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_81) (e := 561) (k :=
      9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 81, from a generated integer certificate. -/
theorem elementaryCertificate_at_81 :
    ((81 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 81) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_82) (e := 570) (k :=
      9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 82, from a generated integer certificate. -/
theorem elementaryCertificate_at_82 :
    ((82 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 82) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_83) (e := 579) (k :=
      9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 83, from a generated integer certificate. -/
theorem elementaryCertificate_at_83 :
    ((83 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 83) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_84) (e := 588) (k :=
      9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 84, from a generated integer certificate. -/
theorem elementaryCertificate_at_84 :
    ((84 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 84) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_85) (e := 596) (k :=
      9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 85, from a generated integer certificate. -/
theorem elementaryCertificate_at_85 :
    ((85 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 85) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_86) (e := 605) (k :=
      9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 86, from a generated integer certificate. -/
theorem elementaryCertificate_at_86 :
    ((86 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 86) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_87) (e := 614) (k :=
      9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 87, from a generated integer certificate. -/
theorem elementaryCertificate_at_87 :
    ((87 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 87) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_88) (e := 623) (k :=
      9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 88, from a generated integer certificate. -/
theorem elementaryCertificate_at_88 :
    ((88 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 88) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_89) (e := 632) (k :=
      9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 89, from a generated integer certificate. -/
theorem elementaryCertificate_at_89 :
    ((89 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 89) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_90) (e := 641) (k :=
      9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 90, from a generated integer certificate. -/
theorem elementaryCertificate_at_90 :
    ((90 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 90) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_91) (e := 649) (k :=
      9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 91, from a generated integer certificate. -/
theorem elementaryCertificate_at_91 :
    ((91 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 91) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_92) (e := 658) (k :=
      9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 92, from a generated integer certificate. -/
theorem elementaryCertificate_at_92 :
    ((92 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 92) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_93) (e := 667) (k :=
      9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 93, from a generated integer certificate. -/
theorem elementaryCertificate_at_93 :
    ((93 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 93) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_94) (e := 676) (k :=
      9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 94, from a generated integer certificate. -/
theorem elementaryCertificate_at_94 :
    ((94 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 94) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_95) (e := 685) (k :=
      9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 95, from a generated integer certificate. -/
theorem elementaryCertificate_at_95 :
    ((95 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 95) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_96) (e := 694) (k :=
      9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 96, from a generated integer certificate. -/
theorem elementaryCertificate_at_96 :
    ((96 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 96) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_97) (e := 703) (k :=
      9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 97, from a generated integer certificate. -/
theorem elementaryCertificate_at_97 :
    ((97 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 97) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_98) (e := 712) (k :=
      9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 98, from a generated integer certificate. -/
theorem elementaryCertificate_at_98 :
    ((98 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 98) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_99) (e := 721) (k :=
      9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 99, from a generated integer certificate. -/
theorem elementaryCertificate_at_99 :
    ((99 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 99) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_100) (e := 730)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 100, from a generated integer certificate. -/
theorem elementaryCertificate_at_100 :
    ((100 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 100) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_101) (e := 739)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 101, from a generated integer certificate. -/
theorem elementaryCertificate_at_101 :
    ((101 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 101) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_102) (e := 748)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 102, from a generated integer certificate. -/
theorem elementaryCertificate_at_102 :
    ((102 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 102) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_103) (e := 758)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 103, from a generated integer certificate. -/
theorem elementaryCertificate_at_103 :
    ((103 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 103) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_104) (e := 767)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 104, from a generated integer certificate. -/
theorem elementaryCertificate_at_104 :
    ((104 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 104) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_105) (e := 776)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 105, from a generated integer certificate. -/
theorem elementaryCertificate_at_105 :
    ((105 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 105) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_106) (e := 785)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 106, from a generated integer certificate. -/
theorem elementaryCertificate_at_106 :
    ((106 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 106) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_107) (e := 794)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 107, from a generated integer certificate. -/
theorem elementaryCertificate_at_107 :
    ((107 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 107) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_108) (e := 803)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 108, from a generated integer certificate. -/
theorem elementaryCertificate_at_108 :
    ((108 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 108) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_109) (e := 813)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 109, from a generated integer certificate. -/
theorem elementaryCertificate_at_109 :
    ((109 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 109) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_110) (e := 822)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 110, from a generated integer certificate. -/
theorem elementaryCertificate_at_110 :
    ((110 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 110) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_111) (e := 831)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 111, from a generated integer certificate. -/
theorem elementaryCertificate_at_111 :
    ((111 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 111) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_112) (e := 840)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 112, from a generated integer certificate. -/
theorem elementaryCertificate_at_112 :
    ((112 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 112) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_113) (e := 850)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 113, from a generated integer certificate. -/
theorem elementaryCertificate_at_113 :
    ((113 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 113) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_114) (e := 859)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 114, from a generated integer certificate. -/
theorem elementaryCertificate_at_114 :
    ((114 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 114) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_115) (e := 868)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 115, from a generated integer certificate. -/
theorem elementaryCertificate_at_115 :
    ((115 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 115) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_116) (e := 878)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 116, from a generated integer certificate. -/
theorem elementaryCertificate_at_116 :
    ((116 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 116) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_117) (e := 887)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 117, from a generated integer certificate. -/
theorem elementaryCertificate_at_117 :
    ((117 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 117) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_118) (e := 896)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 118, from a generated integer certificate. -/
theorem elementaryCertificate_at_118 :
    ((118 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 118) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_119) (e := 906)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 119, from a generated integer certificate. -/
theorem elementaryCertificate_at_119 :
    ((119 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 119) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_120) (e := 915)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 120, from a generated integer certificate. -/
theorem elementaryCertificate_at_120 :
    ((120 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 120) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_121) (e := 924)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 121, from a generated integer certificate. -/
theorem elementaryCertificate_at_121 :
    ((121 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 121) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_122) (e := 934)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 122, from a generated integer certificate. -/
theorem elementaryCertificate_at_122 :
    ((122 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 122) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_123) (e := 943)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 123, from a generated integer certificate. -/
theorem elementaryCertificate_at_123 :
    ((123 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 123) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_124) (e := 953)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 124, from a generated integer certificate. -/
theorem elementaryCertificate_at_124 :
    ((124 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 124) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_125) (e := 962)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 125, from a generated integer certificate. -/
theorem elementaryCertificate_at_125 :
    ((125 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 125) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_126) (e := 971)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 126, from a generated integer certificate. -/
theorem elementaryCertificate_at_126 :
    ((126 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 126) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_127) (e := 981)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 127, from a generated integer certificate. -/
theorem elementaryCertificate_at_127 :
    ((127 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 127) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_128) (e := 990)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 128, from a generated integer certificate. -/
theorem elementaryCertificate_at_128 :
    ((128 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 128) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_129) (e := 1000)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 129, from a generated integer certificate. -/
theorem elementaryCertificate_at_129 :
    ((129 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 129) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_130) (e := 1009)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 130, from a generated integer certificate. -/
theorem elementaryCertificate_at_130 :
    ((130 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 130) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_131) (e := 1019)
      (k := 9) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 131, from a generated integer certificate. -/
theorem elementaryCertificate_at_131 :
    ((131 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 131) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_132) (e := 1029)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 132, from a generated integer certificate. -/
theorem elementaryCertificate_at_132 :
    ((132 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 132) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_133) (e := 1038)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 133, from a generated integer certificate. -/
theorem elementaryCertificate_at_133 :
    ((133 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 133) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_134) (e := 1048)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 134, from a generated integer certificate. -/
theorem elementaryCertificate_at_134 :
    ((134 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 134) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_135) (e := 1057)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 135, from a generated integer certificate. -/
theorem elementaryCertificate_at_135 :
    ((135 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 135) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_136) (e := 1067)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 136, from a generated integer certificate. -/
theorem elementaryCertificate_at_136 :
    ((136 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 136) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_137) (e := 1076)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 137, from a generated integer certificate. -/
theorem elementaryCertificate_at_137 :
    ((137 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 137) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_138) (e := 1086)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 138, from a generated integer certificate. -/
theorem elementaryCertificate_at_138 :
    ((138 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 138) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_139) (e := 1096)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 139, from a generated integer certificate. -/
theorem elementaryCertificate_at_139 :
    ((139 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 139) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_140) (e := 1105)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 140, from a generated integer certificate. -/
theorem elementaryCertificate_at_140 :
    ((140 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 140) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_141) (e := 1115)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 141, from a generated integer certificate. -/
theorem elementaryCertificate_at_141 :
    ((141 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 141) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_142) (e := 1125)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 142, from a generated integer certificate. -/
theorem elementaryCertificate_at_142 :
    ((142 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 142) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_143) (e := 1134)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 143, from a generated integer certificate. -/
theorem elementaryCertificate_at_143 :
    ((143 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 143) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_144) (e := 1144)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 144, from a generated integer certificate. -/
theorem elementaryCertificate_at_144 :
    ((144 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 144) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_145) (e := 1154)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 145, from a generated integer certificate. -/
theorem elementaryCertificate_at_145 :
    ((145 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 145) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_146) (e := 1163)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 146, from a generated integer certificate. -/
theorem elementaryCertificate_at_146 :
    ((146 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 146) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_147) (e := 1173)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 147, from a generated integer certificate. -/
theorem elementaryCertificate_at_147 :
    ((147 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 147) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_148) (e := 1183)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 148, from a generated integer certificate. -/
theorem elementaryCertificate_at_148 :
    ((148 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 148) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_149) (e := 1193)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 149, from a generated integer certificate. -/
theorem elementaryCertificate_at_149 :
    ((149 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 149) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_150) (e := 1202)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 150, from a generated integer certificate. -/
theorem elementaryCertificate_at_150 :
    ((150 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 150) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_151) (e := 1212)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 151, from a generated integer certificate. -/
theorem elementaryCertificate_at_151 :
    ((151 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 151) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_152) (e := 1222)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 152, from a generated integer certificate. -/
theorem elementaryCertificate_at_152 :
    ((152 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 152) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_153) (e := 1232)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 153, from a generated integer certificate. -/
theorem elementaryCertificate_at_153 :
    ((153 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 153) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_154) (e := 1242)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 154, from a generated integer certificate. -/
theorem elementaryCertificate_at_154 :
    ((154 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 154) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_155) (e := 1251)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 155, from a generated integer certificate. -/
theorem elementaryCertificate_at_155 :
    ((155 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 155) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_156) (e := 1261)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 156, from a generated integer certificate. -/
theorem elementaryCertificate_at_156 :
    ((156 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 156) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_157) (e := 1271)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 157, from a generated integer certificate. -/
theorem elementaryCertificate_at_157 :
    ((157 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 157) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_158) (e := 1281)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 158, from a generated integer certificate. -/
theorem elementaryCertificate_at_158 :
    ((158 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 158) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_159) (e := 1291)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 159, from a generated integer certificate. -/
theorem elementaryCertificate_at_159 :
    ((159 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 159) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_160) (e := 1301)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 160, from a generated integer certificate. -/
theorem elementaryCertificate_at_160 :
    ((160 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 160) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_161) (e := 1311)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 161, from a generated integer certificate. -/
theorem elementaryCertificate_at_161 :
    ((161 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 161) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_162) (e := 1320)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

set_option exponentiation.threshold 3000 in
/-- The finite omega bound at index 162, from a generated integer certificate. -/
theorem elementaryCertificate_at_162 :
    ((162 : ℕ) + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor 162) := by
  apply
    certificate_of_primorial (hP := NumberTheory.primePrimorialCount_cumulative_163) (e := 1330)
      (k := 10) (by norm_num only) (by norm_num only)
  · exact certificate_rational_of_nat (by decide)

-- END GENERATED OMEGA CERTIFICATES

theorem elementaryOmegaFiniteCertificates :
    ∀ m : ℕ, 1 ≤ m → m < 163 → (m + 1 : ℝ) ≤ elementaryOmegaRhsReal (elementaryAnchor m) := by
  -- BEGIN GENERATED OMEGA DISPATCH
  intro m hm1 hm163
  interval_cases m
  · exact elementaryCertificate_at_1
  · exact elementaryCertificate_at_2
  · exact elementaryCertificate_at_3
  · exact elementaryCertificate_at_4
  · exact elementaryCertificate_at_5
  · exact elementaryCertificate_at_6
  · exact elementaryCertificate_at_7
  · exact elementaryCertificate_at_8
  · exact elementaryCertificate_at_9
  · exact elementaryCertificate_at_10
  · exact elementaryCertificate_at_11
  · exact elementaryCertificate_at_12
  · exact elementaryCertificate_at_13
  · exact elementaryCertificate_at_14
  · exact elementaryCertificate_at_15
  · exact elementaryCertificate_at_16
  · exact elementaryCertificate_at_17
  · exact elementaryCertificate_at_18
  · exact elementaryCertificate_at_19
  · exact elementaryCertificate_at_20
  · exact elementaryCertificate_at_21
  · exact elementaryCertificate_at_22
  · exact elementaryCertificate_at_23
  · exact elementaryCertificate_at_24
  · exact elementaryCertificate_at_25
  · exact elementaryCertificate_at_26
  · exact elementaryCertificate_at_27
  · exact elementaryCertificate_at_28
  · exact elementaryCertificate_at_29
  · exact elementaryCertificate_at_30
  · exact elementaryCertificate_at_31
  · exact elementaryCertificate_at_32
  · exact elementaryCertificate_at_33
  · exact elementaryCertificate_at_34
  · exact elementaryCertificate_at_35
  · exact elementaryCertificate_at_36
  · exact elementaryCertificate_at_37
  · exact elementaryCertificate_at_38
  · exact elementaryCertificate_at_39
  · exact elementaryCertificate_at_40
  · exact elementaryCertificate_at_41
  · exact elementaryCertificate_at_42
  · exact elementaryCertificate_at_43
  · exact elementaryCertificate_at_44
  · exact elementaryCertificate_at_45
  · exact elementaryCertificate_at_46
  · exact elementaryCertificate_at_47
  · exact elementaryCertificate_at_48
  · exact elementaryCertificate_at_49
  · exact elementaryCertificate_at_50
  · exact elementaryCertificate_at_51
  · exact elementaryCertificate_at_52
  · exact elementaryCertificate_at_53
  · exact elementaryCertificate_at_54
  · exact elementaryCertificate_at_55
  · exact elementaryCertificate_at_56
  · exact elementaryCertificate_at_57
  · exact elementaryCertificate_at_58
  · exact elementaryCertificate_at_59
  · exact elementaryCertificate_at_60
  · exact elementaryCertificate_at_61
  · exact elementaryCertificate_at_62
  · exact elementaryCertificate_at_63
  · exact elementaryCertificate_at_64
  · exact elementaryCertificate_at_65
  · exact elementaryCertificate_at_66
  · exact elementaryCertificate_at_67
  · exact elementaryCertificate_at_68
  · exact elementaryCertificate_at_69
  · exact elementaryCertificate_at_70
  · exact elementaryCertificate_at_71
  · exact elementaryCertificate_at_72
  · exact elementaryCertificate_at_73
  · exact elementaryCertificate_at_74
  · exact elementaryCertificate_at_75
  · exact elementaryCertificate_at_76
  · exact elementaryCertificate_at_77
  · exact elementaryCertificate_at_78
  · exact elementaryCertificate_at_79
  · exact elementaryCertificate_at_80
  · exact elementaryCertificate_at_81
  · exact elementaryCertificate_at_82
  · exact elementaryCertificate_at_83
  · exact elementaryCertificate_at_84
  · exact elementaryCertificate_at_85
  · exact elementaryCertificate_at_86
  · exact elementaryCertificate_at_87
  · exact elementaryCertificate_at_88
  · exact elementaryCertificate_at_89
  · exact elementaryCertificate_at_90
  · exact elementaryCertificate_at_91
  · exact elementaryCertificate_at_92
  · exact elementaryCertificate_at_93
  · exact elementaryCertificate_at_94
  · exact elementaryCertificate_at_95
  · exact elementaryCertificate_at_96
  · exact elementaryCertificate_at_97
  · exact elementaryCertificate_at_98
  · exact elementaryCertificate_at_99
  · exact elementaryCertificate_at_100
  · exact elementaryCertificate_at_101
  · exact elementaryCertificate_at_102
  · exact elementaryCertificate_at_103
  · exact elementaryCertificate_at_104
  · exact elementaryCertificate_at_105
  · exact elementaryCertificate_at_106
  · exact elementaryCertificate_at_107
  · exact elementaryCertificate_at_108
  · exact elementaryCertificate_at_109
  · exact elementaryCertificate_at_110
  · exact elementaryCertificate_at_111
  · exact elementaryCertificate_at_112
  · exact elementaryCertificate_at_113
  · exact elementaryCertificate_at_114
  · exact elementaryCertificate_at_115
  · exact elementaryCertificate_at_116
  · exact elementaryCertificate_at_117
  · exact elementaryCertificate_at_118
  · exact elementaryCertificate_at_119
  · exact elementaryCertificate_at_120
  · exact elementaryCertificate_at_121
  · exact elementaryCertificate_at_122
  · exact elementaryCertificate_at_123
  · exact elementaryCertificate_at_124
  · exact elementaryCertificate_at_125
  · exact elementaryCertificate_at_126
  · exact elementaryCertificate_at_127
  · exact elementaryCertificate_at_128
  · exact elementaryCertificate_at_129
  · exact elementaryCertificate_at_130
  · exact elementaryCertificate_at_131
  · exact elementaryCertificate_at_132
  · exact elementaryCertificate_at_133
  · exact elementaryCertificate_at_134
  · exact elementaryCertificate_at_135
  · exact elementaryCertificate_at_136
  · exact elementaryCertificate_at_137
  · exact elementaryCertificate_at_138
  · exact elementaryCertificate_at_139
  · exact elementaryCertificate_at_140
  · exact elementaryCertificate_at_141
  · exact elementaryCertificate_at_142
  · exact elementaryCertificate_at_143
  · exact elementaryCertificate_at_144
  · exact elementaryCertificate_at_145
  · exact elementaryCertificate_at_146
  · exact elementaryCertificate_at_147
  · exact elementaryCertificate_at_148
  · exact elementaryCertificate_at_149
  · exact elementaryCertificate_at_150
  · exact elementaryCertificate_at_151
  · exact elementaryCertificate_at_152
  · exact elementaryCertificate_at_153
  · exact elementaryCertificate_at_154
  · exact elementaryCertificate_at_155
  · exact elementaryCertificate_at_156
  · exact elementaryCertificate_at_157
  · exact elementaryCertificate_at_158
  · exact elementaryCertificate_at_159
  · exact elementaryCertificate_at_160
  · exact elementaryCertificate_at_161
  · exact elementaryCertificate_at_162

-- END GENERATED OMEGA DISPATCH

/-- **`PseudoPrime.AnalyticNumberTheory.Arithmetic.ElementaryOmegaStatement`, unconditionally.** -/
theorem elementaryOmegaStatement : ElementaryOmegaStatement :=
  elementaryOmegaStatement_of_finite
    (elementaryOmegaFiniteStatement_of_certificates elementaryOmegaFiniteCertificates)

end PseudoPrime.AnalyticNumberTheory.Arithmetic
