/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SharpOddEndpointDoubleLogRoot
public import PseudoPrime.Analysis.ShiftedLogQuadraticRemainder

/-! # A double-logarithm radius with constant 37/5 retaining the two-adic shift -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For y≥94 and z≥0, a positive logarithmic remainder and the coupled
37/5 level inequality imply positivity of the zero-at-two branch polynomial.
An exact rational decomposition retains the half-log shift in the defect.
The remaining coefficients are nonnegative on the entire analytic range. -/
theorem shiftedOddEndpoint_zero_polynomial_pos_of_remainder {L y z : ℝ} (hy : 94 ≤ y) (hz : 0 ≤ z)
    (hF : 0 < (79 / 2000 : ℝ) * y + 14 + (15 / 2 : ℝ) * z - 2 * z ^ 2)
    (hlink : (y - 2) * L ≤ (y - 2) * y + y * (2 * z - 37 / 5)) :
    0 <
      oddEndpointTwoCostPolynomial (L + 7 / 5) (2096 / 1831) y z (7 / 10)
        (2 * z ^ 2 - (69 / 100 : ℝ) * z + 49 / 800) := by
  have hy0 : 0 ≤ y := by linarith only [hy]
  have h2 : 94 * y ≤ y ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hy hy0
    nlinarith only [hm]
  have h3 : 94 * y ^ 2 ≤ y ^ 3 := by
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

/-- Radius L-2log L+37/5. For L≥96 it bounds the odd-prime non-one Jacobi
witness through the shifted zero-at-two and sharp nonzero branch estimates.
The result uses no enumeration of the integer inputs. -/
noncomputable def shiftedOddEndpointDoubleLogRoot (L : ℝ) : ℝ :=
  L - 2 * Real.log L + 37 / 5

/-- For L ≥ 96, the improved radius is at least 94 and satisfies the tangent-coupled
level relation with constant 37/5. Bound log L at 96, then use the logarithmic
tangent at the radius. These are the scale inputs to the polynomial certificate. -/
theorem shiftedOddEndpointDoubleLogRoot_data {L : ℝ} (hL : 96 ≤ L) :
    let y := shiftedOddEndpointDoubleLogRoot L
    94 ≤ y ∧ (y - 2) * L ≤ (y - 2) * y + y * (2 * Real.log y - 37 / 5) := by
  let y := shiftedOddEndpointDoubleLogRoot L
  have hL0 : 0 < L := by linarith only [hL]
  have h96 : Real.log (96 : ℝ) ≤ 23 / 5 := by
    rw [show (96 : ℝ) = 2 ^ 5 * 3 by norm_num only,
      Real.log_mul (by norm_num only : (2 : ℝ) ^ 5 ≠ 0) (by norm_num only : (3 : ℝ) ≠ 0),
      Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9, Real.log_three_lt_d9]
  have ht := Analysis.log_le_log_add_sub_div (by norm_num only : (0 : ℝ) < 96) hL0
  have hy : 94 ≤ y := by
    dsimp only [y, shiftedOddEndpointDoubleLogRoot]
    linarith only [ht, h96, hL]
  have hy0 : 0 < y := by linarith only [hy]
  have ht' := Analysis.log_le_log_add_sub_div hy0 hL0
  have hd : Real.log L - Real.log y ≤ (L - y) / y := by linarith only [ht']
  have hm := (le_div_iff₀ hy0).mp hd
  have he := congrArg (fun t : ℝ ↦ y * t) (show y = L - 2 * Real.log L + 37 / 5 from rfl)
  exact ⟨hy, by nlinarith only [hm, he]⟩

/-- The sharp nonzero branch polynomial dominates the shifted zero branch
for y≥94 and z≥0. Expand their difference and prove the two coefficient
polynomials nonnegative using the height lower bound. -/
theorem shiftedOddEndpoint_nonzero_polynomial_ge_zero {L y z : ℝ} (hy : 94 ≤ y) (hz : 0 ≤ z) :
    oddEndpointTwoCostPolynomial (L + 7 / 5) (2096 / 1831) y z (7 / 10)
        (2 * z ^ 2 - (69 / 100 : ℝ) * z + 49 / 800) ≤
      oddEndpointTwoCostPolynomial L (2096 / 1831) y z (14 / 15) (2 * z ^ 2) := by
  have hy0 : 0 ≤ y := by linarith only [hy]
  have h2 : 94 * y ≤ y ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hy hy0
    nlinarith only [hh]
  have h3 : 94 * y ^ 2 ≤ y ^ 3 := by
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

/-- For L≥96 and 69/100≤b≤7/10, both conductor-correlated branch
polynomials are positive at the 37/5 radius. Use the analytic remainder,
cost monotonicity, and the sharper half-square defect in the nonzero branch.
Substituting b=log two supplies the actual arithmetic certificates. -/
theorem shiftedOddEndpoint_doubleLog_branch_polynomials_pos {L b : ℝ} (hL : 96 ≤ L)
    (hbl : 69 / 100 ≤ b) (hbu : b ≤ 7 / 10) :
    let y := shiftedOddEndpointDoubleLogRoot L
    0 <
        oddEndpointTwoCostPolynomial (L + 2 * b) (2096 / 1831) y (Real.log y) b
          ((2 * Real.log y - b / 2) ^ 2 / 2) ∧
      0 <
        oddEndpointTwoCostPolynomial L (2096 / 1831) y (Real.log y) ((4 / 3 : ℝ) * b)
          (2 * (Real.log y) ^ 2) := by
  let y := shiftedOddEndpointDoubleLogRoot L
  have hd := shiftedOddEndpointDoubleLogRoot_data hL
  have hy1 : 1 ≤ y := by linarith only [hd.1]
  have hz := Real.log_nonneg hy1
  have hp :=
    shiftedOddEndpoint_zero_polynomial_pos_of_remainder hd.1 hz
      (Analysis.shiftedLogQuadraticRemainder_pos_of_94 hd.1) hd.2
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
  have hbranch := shiftedOddEndpoint_nonzero_polynomial_ge_zero (L := L) hd.1 hz
  have hcost1 :=
    oddEndpointTwoCostPolynomial_antitone_cost (L := L) (P := (2096 / 1831 : ℝ)) (D :=
      2 * (Real.log y) ^ 2) hy1 hz (show (4 / 3 : ℝ) * b ≤ 14 / 15 by linarith only [hbu]) le_rfl
  exact ⟨hp.trans_le (hlevel.trans hcost0), hp.trans_le (hbranch.trans hcost1)⟩

end PseudoPrime.LLS.PaperStatements
