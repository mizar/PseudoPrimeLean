/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SharpLogQuadraticRemainder
public import PseudoPrime.LLS.OddEndpointDoubleLogRoot

/-! # A double-logarithm witness radius with additive constant 149/20 -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For y ≥ 94 and nonnegative z, the stronger positive logarithmic remainder
and tangent-coupled level relation with constant 149/20 imply positivity of the
zero-value endpoint polynomial. Expand its numerator into nonnegative pieces.
This separates numerical certification from the actual logarithmic radius. -/
theorem sharpOddEndpoint_zero_polynomial_pos_of_remainder {L y z : ℝ} (hy : 94 ≤ y) (hz : 0 ≤ z)
    (hF : 0 < (17 / 200 : ℝ) * y + 14 + (69 / 10 : ℝ) * z - 2 * z ^ 2)
    (hlink : (y - 2) * L ≤ (y - 2) * y + y * (2 * z - 149 / 20)) :
    0 < oddEndpointTwoCostPolynomial (L + 7 / 5) (2096 / 1831) y z (7 / 10) (2 * z ^ 2) := by
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
      (2043939 / 18310000 : ℝ) * y ^ 3 - (18010259 / 9155000 : ℝ) * y ^ 2 -
          (2862719 / 183100 : ℝ) * y +
        3041959 / 457750 := by
    nlinarith only [h2, h3, hy0]
  have hc0 :
    0 ≤
      (84769 / 18310000 : ℝ) * y ^ 4 + (7513881 / 18310000 : ℝ) * y ^ 3 +
            (186542381 / 9155000 : ℝ) * y ^ 2 -
          (136795 / 3662 : ℝ) * y +
        193893 / 18310 := by
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
    (y - 2) * oddEndpointTwoCostPolynomial (L + 7 / 5) (2096 / 1831) y z (7 / 10) (2 * z ^ 2) =
      y ^ 3 * ((17 / 200 : ℝ) * y + 14 + (69 / 10 : ℝ) * z - 2 * z ^ 2) +
        ((y - 1) ^ 2 * z + (2 * y + 2 * z + 2) * ((1 / 2 : ℝ) * (y ^ 2 - 1))) *
          ((y - 2) * y + y * (2 * z - 149 / 20) - (y - 2) * L) +
        (4 * y ^ 2 - 10 * y + 4) * z ^ 2 +
        ((2043939 / 18310000 : ℝ) * y ^ 3 - (18010259 / 9155000 : ℝ) * y ^ 2 -
              (2862719 / 183100 : ℝ) * y +
            3041959 / 457750) *
          z +
        ((84769 / 18310000 : ℝ) * y ^ 4 + (7513881 / 18310000 : ℝ) * y ^ 3 +
              (186542381 / 9155000 : ℝ) * y ^ 2 -
            (136795 / 3662 : ℝ) * y +
          193893 / 18310) := by
    dsimp only [oddEndpointTwoCostPolynomial, fullEndpointPolynomial]
    ring
  have hpos :
    0 <
      (y - 2) *
        oddEndpointTwoCostPolynomial (L + 7 / 5) (2096 / 1831) y z (7 / 10) (2 * z ^ 2) := by
    rw [he]
    linarith only [hp, hmK, hm2, hm1, hc0]
  exact (mul_pos_iff_of_pos_left (by linarith only [hy] : 0 < y - 2)).mp hpos

/-- The radius L-2log L+149/20 for real logarithmic scale L. For L ≥ 96,
its square will bound odd non-one Jacobi witnesses. It is smaller than the old
double-logarithm radius by 1/20; other public bounds require separate comparisons. -/
noncomputable def sharpOddEndpointDoubleLogRoot (L : ℝ) : ℝ :=
  L - 2 * Real.log L + 149 / 20

/-- For L ≥ 96, the improved radius is at least 94 and satisfies the tangent-coupled
level relation with constant 149/20. Bound log L at 96, then use the logarithmic
tangent at the radius. These are the scale inputs to the polynomial certificate. -/
theorem sharpOddEndpointDoubleLogRoot_data {L : ℝ} (hL : 96 ≤ L) :
    let y := sharpOddEndpointDoubleLogRoot L
    94 ≤ y ∧ (y - 2) * L ≤ (y - 2) * y + y * (2 * Real.log y - 149 / 20) := by
  let y := sharpOddEndpointDoubleLogRoot L
  have hL0 : 0 < L := by linarith only [hL]
  have h96 : Real.log (96 : ℝ) ≤ 23 / 5 := by
    rw [show (96 : ℝ) = 2 ^ 5 * 3 by norm_num only,
      Real.log_mul (by norm_num only : (2 : ℝ) ^ 5 ≠ 0) (by norm_num only : (3 : ℝ) ≠ 0),
      Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9, Real.log_three_lt_d9]
  have ht := Analysis.log_le_log_add_sub_div (by norm_num only : (0 : ℝ) < 96) hL0
  have hy : 94 ≤ y := by
    dsimp only [y, sharpOddEndpointDoubleLogRoot]
    linarith only [ht, h96, hL]
  have hy0 : 0 < y := by linarith only [hy]
  have ht' := Analysis.log_le_log_add_sub_div hy0 hL0
  have hd : Real.log L - Real.log y ≤ (L - y) / y := by linarith only [ht']
  have hm := (le_div_iff₀ hy0).mp hd
  have he := congrArg (fun t : ℝ ↦ y * t) (show y = L - 2 * Real.log L + 149 / 20 from rfl)
  exact ⟨hy, by nlinarith only [hm, he]⟩

/-- For L>=96 and any real b<=7/10, both correlated branch polynomials at
the double-logarithm root are positive. Apply the uniform remainder, conductor-cost
correlation and cost monotonicity. Substituting b=log two gives the actual Jacobi
non-one criteria without independent numerical gap assumptions. -/
theorem sharpOddEndpoint_doubleLog_branch_polynomials_pos {L b : ℝ} (hL : 96 ≤ L)
    (hb : b ≤ 7 / 10) :
    let y := sharpOddEndpointDoubleLogRoot L
    0 <
        oddEndpointTwoCostPolynomial (L + 2 * b) (2096 / 1831) y (Real.log y) b
          (2 * (Real.log y) ^ 2) ∧
      0 <
        oddEndpointTwoCostPolynomial L (2096 / 1831) y (Real.log y) ((4 / 3) * b)
          (2 * (Real.log y) ^ 2 + b * (2 * Real.log y - b)) := by
  let y := sharpOddEndpointDoubleLogRoot L
  have hd := sharpOddEndpointDoubleLogRoot_data hL
  have hy1 : 1 ≤ y := by linarith only [hd.1]
  have hz : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hp :=
    sharpOddEndpoint_zero_polynomial_pos_of_remainder hd.1 hz
      (Analysis.sharpLogQuadraticRemainder_pos_of_94 hd.1) hd.2
  have hlevel :=
    oddEndpointTwoCostPolynomial_antitone_level (P := (2096 / 1831 : ℝ)) (c := (7 / 10 : ℝ)) (D :=
      2 * (Real.log y) ^ 2) hy1 hz (by linarith only [hb] : L + 2 * b ≤ L + 7 / 5)
  have hcost0 :=
    oddEndpointTwoCostPolynomial_antitone_cost (L := L + 2 * b) (P := (2096 / 1831 : ℝ)) (D :=
      2 * (Real.log y) ^ 2) hy1 hz hb le_rfl
  have hnz :=
    oddEndpoint_nonzero_polynomial_ge_zero (L := L) (P := (2096 / 1831 : ℝ))
      (by linarith only [hd.1] : 2 ≤ y) hz
  have hm := mul_le_mul_of_nonneg_right hb hz
  have hD :
    2 * (Real.log y) ^ 2 + b * (2 * Real.log y - b) ≤
      2 * (Real.log y) ^ 2 + (7 / 5 : ℝ) * Real.log y := by
    nlinarith only [hm, sq_nonneg b]
  have hC : (4 / 3 : ℝ) * b ≤ 14 / 15 := by linarith only [hb]
  have hcost1 :=
    oddEndpointTwoCostPolynomial_antitone_cost (L := L) (P := (2096 / 1831 : ℝ)) hy1 hz hC hD
  exact ⟨hp.trans_le (hlevel.trans hcost0), hp.trans_le (hnz.trans hcost1)⟩

end PseudoPrime.LLS.PaperStatements
