/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ShiftedOddEndpointDoubleLogRoot
public import PseudoPrime.Analysis.ShiftedLogQuadraticRemainderLowerRange

/-! # The 37/5 double-logarithm radius from scale fifty -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For y≥49, z≥0, a positive shifted remainder and the coupled
37/5 level inequality force positivity of the zero branch. The rational
remainder coefficients are already nonnegative at this smaller height.
The same exact decomposition supplies the lower analytic starting scale. -/
theorem shiftedOddEndpoint_zero_polynomial_pos_of_remainder_of_49 {L y z : ℝ} (hy : 49 ≤ y)
    (hz : 0 ≤ z) (hF : 0 < (79 / 2000 : ℝ) * y + 14 + (15 / 2 : ℝ) * z - 2 * z ^ 2)
    (hlink : (y - 2) * L ≤ (y - 2) * y + y * (2 * z - 37 / 5)) :
    0 <
      oddEndpointTwoCostPolynomial (L + 7 / 5) (2096 / 1831) y z (7 / 10)
        (2 * z ^ 2 - (69 / 100 : ℝ) * z + 49 / 800) := by
  have hy0 : 0 ≤ y := by linarith only [hy]
  have h2 : 49 * y ≤ y ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hy hy0
    nlinarith only [hm]
  have h3 : 49 * y ^ 2 ≤ y ^ 3 := by
    have hm := mul_le_mul_of_nonneg_right hy (sq_nonneg y)
    nlinarith only [hm]
  have hc2 : 0 ≤ 4 * y ^ 2 - 10 * y + 4 := by nlinarith only [h2, hy0]
  have hc1 :
    0 ≤
      (1860839 / 18310000 : ℝ) * y ^ 3 - (42362559 / 9155000 : ℝ) * y ^ 2 -
          (557756 / 45775 : ℝ) * y +
        1205132 / 228875 := by
    nlinarith only [h2, h3, hy0]
  have hc0 :
    0 ≤
      (1187 / 9155000 : ℝ) * y ^ 4 + (10953787 / 36620000 : ℝ) * y ^ 3 +
            (94621553 / 4577500 : ℝ) * y ^ 2 -
          (11018671 / 292960 : ℝ) * y +
        7845439 / 732400 := by
    nlinarith only [h2, hy0, pow_nonneg hy0 3, pow_nonneg hy0 4]
  have hK : 0 ≤ (y - 1) ^ 2 * z + (2 * y + 2 * z + 2) * ((1 / 2 : ℝ) * (y ^ 2 - 1)) := by
    have hs : 0 ≤ y ^ 2 - 1 := by nlinarith only [hy]
    exact
      add_nonneg (mul_nonneg (sq_nonneg _) hz)
        (mul_nonneg (by linarith only [hy, hz]) (mul_nonneg (by norm_num only) hs))
  have hmK := mul_nonneg hK (sub_nonneg.mpr hlink)
  have hm2 := mul_nonneg hc2 (sq_nonneg z)
  have hm1 := mul_nonneg hc1 hz
  have hp := mul_pos (pow_pos (by linarith only [hy] : 0 < y) 3) hF
  have he :
    (y - 2) *
        oddEndpointTwoCostPolynomial (L + 7 / 5) (2096 / 1831) y z (7 / 10)
          (2 * z ^ 2 - (69 / 100 : ℝ) * z + 49 / 800) =
      y ^ 3 * ((79 / 2000 : ℝ) * y + 14 + (15 / 2 : ℝ) * z - 2 * z ^ 2) +
        ((y - 1) ^ 2 * z + (2 * y + 2 * z + 2) * ((1 / 2 : ℝ) * (y ^ 2 - 1))) *
          ((y - 2) * y + y * (2 * z - 37 / 5) - (y - 2) * L) +
        (4 * y ^ 2 - 10 * y + 4) * z ^ 2 +
        ((1860839 / 18310000 : ℝ) * y ^ 3 - (42362559 / 9155000 : ℝ) * y ^ 2 -
              (557756 / 45775 : ℝ) * y +
            1205132 / 228875) *
          z +
        ((1187 / 9155000 : ℝ) * y ^ 4 + (10953787 / 36620000 : ℝ) * y ^ 3 +
              (94621553 / 4577500 : ℝ) * y ^ 2 -
            (11018671 / 292960 : ℝ) * y +
          7845439 / 732400) := by
    dsimp only [oddEndpointTwoCostPolynomial, fullEndpointPolynomial]
    ring
  have hpos :
    0 <
      (y - 2) *
        oddEndpointTwoCostPolynomial (L + 7 / 5) (2096 / 1831) y z (7 / 10)
          (2 * z ^ 2 - (69 / 100 : ℝ) * z + 49 / 800) := by
    rw [he]
    linarith only [hp, hmK, hm2, hm1, hc0]
  exact (mul_pos_iff_of_pos_left (by linarith only [hy] : 0 < y - 2)).mp hpos

/-- For y≥49 and z≥0 the nonzero branch polynomial dominates the
shifted zero branch. Expand the exact difference and bound its two
coefficients using the lower height; this transfers the same positive certificate. -/
theorem shiftedOddEndpoint_nonzero_polynomial_ge_zero_of_49 {L y z : ℝ} (hy : 49 ≤ y) (hz : 0 ≤ z) :
    oddEndpointTwoCostPolynomial (L + 7 / 5) (2096 / 1831) y z (7 / 10)
        (2 * z ^ 2 - (69 / 100 : ℝ) * z + 49 / 800) ≤
      oddEndpointTwoCostPolynomial L (2096 / 1831) y z (14 / 15) (2 * z ^ 2) := by
  have hy0 : 0 ≤ y := by linarith only [hy]
  have h2 : 49 * y ≤ y ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hy hy0
    nlinarith only [hh]
  have h3 : 49 * y ^ 2 ≤ y ^ 3 := by
    have hh := mul_le_mul_of_nonneg_right hy (sq_nonneg y)
    nlinarith only [hh]
  have hc1 : 0 ≤ (493 / 300 : ℝ) * y ^ 2 - (71 / 50 : ℝ) * y - 69 / 100 := by
    nlinarith only [h2, hy]
  have hc0 :
    0 ≤ (14 / 15 : ℝ) * y ^ 3 + (2387 / 2400 : ℝ) * y ^ 2 - (609 / 400 : ℝ) * y - 1071 / 800 := by
    nlinarith only [h2, h3, hy]
  have hh := mul_nonneg hc1 hz
  have he :
    oddEndpointTwoCostPolynomial L (2096 / 1831) y z (14 / 15) (2 * z ^ 2) -
        oddEndpointTwoCostPolynomial (L + 7 / 5) (2096 / 1831) y z (7 / 10)
          (2 * z ^ 2 - (69 / 100 : ℝ) * z + 49 / 800) =
      ((493 / 300 : ℝ) * y ^ 2 - (71 / 50 : ℝ) * y - 69 / 100) * z +
        ((14 / 15 : ℝ) * y ^ 3 + (2387 / 2400 : ℝ) * y ^ 2 - (609 / 400 : ℝ) * y - 1071 / 800) := by
    dsimp only [oddEndpointTwoCostPolynomial, fullEndpointPolynomial]
    ring
  linarith only [he, hh, hc0]

/-- For L≥50 the 37/5 radius is at least 49 and satisfies the coupled
level relation. Bound log 50 by log 64 and use the logarithmic tangent at 50,
then the tangent at the radius. This lowers the scale without enumeration. -/
theorem shiftedOddEndpointDoubleLogRoot_data_from_fifty {L : ℝ} (hL : 50 ≤ L) :
    let y := shiftedOddEndpointDoubleLogRoot L
    49 ≤ y ∧ (y - 2) * L ≤ (y - 2) * y + y * (2 * Real.log y - 37 / 5) := by
  let y := shiftedOddEndpointDoubleLogRoot L
  have hL0 : 0 < L := by linarith only [hL]
  have h50 : Real.log (50 : ℝ) ≤ 21 / 5 := by
    have hh :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 50) (by norm_num only : (50 : ℝ) ≤ 2 ^ 6)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh, Real.log_two_lt_d9]
  have ht := Analysis.log_le_log_add_sub_div (by norm_num only : (0 : ℝ) < 50) hL0
  have hy : 49 ≤ y := by
    dsimp only [y, shiftedOddEndpointDoubleLogRoot]
    linarith only [ht, h50, hL]
  have hy0 : 0 < y := by linarith only [hy]
  have ht' := Analysis.log_le_log_add_sub_div hy0 hL0
  have hd : Real.log L - Real.log y ≤ (L - y) / y := by linarith only [ht']
  have hm := (le_div_iff₀ hy0).mp hd
  have he := congrArg (fun t : ℝ ↦ y * t) (show y = L - 2 * Real.log L + 37 / 5 from rfl)
  exact ⟨hy, by nlinarith only [hm, he]⟩

/-- For L≥50 and 69/100≤b≤7/10, both conductor-correlated branch
polynomials are positive at the 37/5 radius. Use remainder positivity from one
and the y≥49 comparison, retaining the half-square shift at two.
Substitution of b=log two supplies the odd-prime Jacobi certificates. -/
theorem shiftedOddEndpoint_doubleLog_branch_polynomials_pos_from_fifty {L b : ℝ} (hL : 50 ≤ L)
    (hbl : 69 / 100 ≤ b) (hbu : b ≤ 7 / 10) :
    let y := shiftedOddEndpointDoubleLogRoot L
    0 <
        oddEndpointTwoCostPolynomial (L + 2 * b) (2096 / 1831) y (Real.log y) b
          ((2 * Real.log y - b / 2) ^ 2 / 2) ∧
      0 <
        oddEndpointTwoCostPolynomial L (2096 / 1831) y (Real.log y) ((4 / 3 : ℝ) * b)
          (2 * (Real.log y) ^ 2) := by
  let y := shiftedOddEndpointDoubleLogRoot L
  have hd := shiftedOddEndpointDoubleLogRoot_data_from_fifty hL
  have hy1 : 1 ≤ y := by linarith only [hd.1]
  have hz := Real.log_nonneg hy1
  have hp :=
    shiftedOddEndpoint_zero_polynomial_pos_of_remainder_of_49 hd.1 hz
      (Analysis.shiftedLogQuadraticRemainder_pos_of_one hy1) hd.2
  have hm := mul_le_mul_of_nonneg_right hbl hz
  have hb0 : 0 ≤ b := by linarith only [hbl]
  have hb2 := mul_self_le_mul_self hb0 hbu
  have hD :
    (2 * Real.log y - b / 2) ^ 2 / 2 ≤
      2 * (Real.log y) ^ 2 - (69 / 100 : ℝ) * Real.log y + 49 / 800 := by
    nlinarith only [hm, hb2]
  have hlevel :=
    oddEndpointTwoCostPolynomial_antitone_level (P := (2096 / 1831 : ℝ)) (c := (7 / 10 : ℝ)) (D :=
      2 * (Real.log y) ^ 2 - (69 / 100 : ℝ) * Real.log y + 49 / 800) hy1 hz
      (show L + 2 * b ≤ L + 7 / 5 by linarith only [hbu])
  have hcost0 :=
    oddEndpointTwoCostPolynomial_antitone_cost (L := L + 2 * b) (P := (2096 / 1831 : ℝ)) hy1 hz hbu
      hD
  have hbranch := shiftedOddEndpoint_nonzero_polynomial_ge_zero_of_49 (L := L) hd.1 hz
  have hcost1 :=
    oddEndpointTwoCostPolynomial_antitone_cost (L := L) (P := (2096 / 1831 : ℝ)) (D :=
      2 * (Real.log y) ^ 2) hy1 hz (show (4 / 3 : ℝ) * b ≤ 14 / 15 by linarith only [hbu]) le_rfl
  exact ⟨hp.trans_le (hlevel.trans hcost0), hp.trans_le (hbranch.trans hcost1)⟩

end PseudoPrime.LLS.PaperStatements
