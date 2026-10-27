/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.OddEndpointTwoCostPolynomial

/-! # Continuous polynomial separation for the eleven-fourths logarithmic shift -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For nonnegative t and u the shifted branch certificate is positive.
All nonconstant monomials are nonnegative and the constant is strictly positive.
This supplies continuous, rather than finite-input, polynomial separation. -/
theorem oddEndpoint_shifted_branch_0_pos {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 <
      73240000 * t ^ 4 * u ^ 1 + 10226476 * t ^ 4 + 35199995756 * t ^ 3 * u ^ 1 +
        5293602321 * t ^ 3 +
        292960000 * t ^ 2 * u ^ 2 +
        6347178421844 * t ^ 2 * u ^ 1 +
        1031588357683 * t ^ 2 +
        69870960000 * t ^ 1 * u ^ 2 +
        508913015681200 * t ^ 1 * u ^ 1 +
        89568284834460 * t ^ 1 +
        4166037680000 * u ^ 2 +
        15308740508475120 * u ^ 1 +
        2920109425513420 := by
  have h0 : 0 ≤ t ^ 4 * u ^ 1 := mul_nonneg (pow_nonneg ht 4) (pow_nonneg hu 1)
  have h1 : 0 ≤ t ^ 4 * u ^ 0 := mul_nonneg (pow_nonneg ht 4) (pow_nonneg hu 0)
  have h2 : 0 ≤ t ^ 3 * u ^ 1 := mul_nonneg (pow_nonneg ht 3) (pow_nonneg hu 1)
  have h3 : 0 ≤ t ^ 3 * u ^ 0 := mul_nonneg (pow_nonneg ht 3) (pow_nonneg hu 0)
  have h4 : 0 ≤ t ^ 2 * u ^ 2 := mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 2)
  have h5 : 0 ≤ t ^ 2 * u ^ 1 := mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 1)
  have h6 : 0 ≤ t ^ 2 * u ^ 0 := mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 0)
  have h7 : 0 ≤ t ^ 1 * u ^ 2 := mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 2)
  have h8 : 0 ≤ t ^ 1 * u ^ 1 := mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 1)
  have h9 : 0 ≤ t ^ 1 * u ^ 0 := mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 0)
  have h10 : 0 ≤ t ^ 0 * u ^ 2 := mul_nonneg (pow_nonneg ht 0) (pow_nonneg hu 2)
  have h11 : 0 ≤ t ^ 0 * u ^ 1 := mul_nonneg (pow_nonneg ht 0) (pow_nonneg hu 1)
  nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

/-- For nonnegative t and u the shifted branch certificate is positive.
All nonconstant monomials are nonnegative and the constant is strictly positive.
This supplies continuous, rather than finite-input, polynomial separation. -/
theorem oddEndpoint_shifted_branch_1_pos {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 <
      219720000 * t ^ 4 * u ^ 1 + 235751428 * t ^ 4 + 105805059268 * t ^ 3 * u ^ 1 +
        115289458963 * t ^ 3 +
        878880000 * t ^ 2 * u ^ 2 +
        19115156113532 * t ^ 2 * u ^ 1 +
        21162172221049 * t ^ 2 +
        209612880000 * t ^ 1 * u ^ 2 +
        1535548632555600 * t ^ 1 * u ^ 1 +
        1727885006485380 * t ^ 1 +
        12498113040000 * u ^ 2 +
        46277596299273360 * u ^ 1 +
        52945706087926260 := by
  have h0 : 0 ≤ t ^ 4 * u ^ 1 := mul_nonneg (pow_nonneg ht 4) (pow_nonneg hu 1)
  have h1 : 0 ≤ t ^ 4 * u ^ 0 := mul_nonneg (pow_nonneg ht 4) (pow_nonneg hu 0)
  have h2 : 0 ≤ t ^ 3 * u ^ 1 := mul_nonneg (pow_nonneg ht 3) (pow_nonneg hu 1)
  have h3 : 0 ≤ t ^ 3 * u ^ 0 := mul_nonneg (pow_nonneg ht 3) (pow_nonneg hu 0)
  have h4 : 0 ≤ t ^ 2 * u ^ 2 := mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 2)
  have h5 : 0 ≤ t ^ 2 * u ^ 1 := mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 1)
  have h6 : 0 ≤ t ^ 2 * u ^ 0 := mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 0)
  have h7 : 0 ≤ t ^ 1 * u ^ 2 := mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 2)
  have h8 : 0 ≤ t ^ 1 * u ^ 1 := mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 1)
  have h9 : 0 ≤ t ^ 1 * u ^ 0 := mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 0)
  have h10 : 0 ≤ t ^ 0 * u ^ 2 := mul_nonneg (pow_nonneg ht 0) (pow_nonneg hu 2)
  have h11 : 0 ≤ t ^ 0 * u ^ 1 := mul_nonneg (pow_nonneg ht 0) (pow_nonneg hu 1)
  nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

/-- At y>=120,z>=19/4 and the tangent coupling for correction 11/4,
the rational branch polynomial is positive. A ring identity separates a positive
shifted polynomial and a nonnegative multiple of the coupling slack. -/
theorem oddEndpoint_branch_0_polynomial_pos {L y z : ℝ} (hy : 120 ≤ y) (hz : 19 / 4 ≤ z)
    (hlink : (y - 1) * L ≤ (y - 1) * y + y * (z - 11 / 4)) :
    0 < oddEndpointTwoCostPolynomial (L + 7 / 5) (2096 / 1831) y z (7 / 10) (2 * z ^ 2) := by
  have hy1 : 1 ≤ y := by linarith only [hy]
  have hs : 0 ≤ y ^ 2 - 1 := by nlinarith only [hy1]
  have hc : 0 ≤ (y - 1) ^ 2 * z + (2 * y + 2 * z + 2) * ((1 / 2 : ℝ) * (y ^ 2 - 1)) :=
    add_nonneg (mul_nonneg (sq_nonneg _) (by linarith only [hz]))
      (mul_nonneg (by linarith only [hy, hz]) (mul_nonneg (by norm_num only) hs))
  have hm := mul_nonneg hc (sub_nonneg.mpr hlink)
  have hp :=
    oddEndpoint_shifted_branch_0_pos (by linarith only [hy] : 0 ≤ y - 120)
      (by linarith only [hz] : 0 ≤ z - 19 / 4)
  have he :
    73240000 * (y - 1) *
        oddEndpointTwoCostPolynomial (L + 7 / 5) (2096 / 1831) y z (7 / 10) (2 * z ^ 2) =
      (73240000 * (y - 120) ^ 4 * (z - 19 / 4) ^ 1 + 10226476 * (y - 120) ^ 4 +
          35199995756 * (y - 120) ^ 3 * (z - 19 / 4) ^ 1 +
          5293602321 * (y - 120) ^ 3 +
          292960000 * (y - 120) ^ 2 * (z - 19 / 4) ^ 2 +
          6347178421844 * (y - 120) ^ 2 * (z - 19 / 4) ^ 1 +
          1031588357683 * (y - 120) ^ 2 +
          69870960000 * (y - 120) ^ 1 * (z - 19 / 4) ^ 2 +
          508913015681200 * (y - 120) ^ 1 * (z - 19 / 4) ^ 1 +
          89568284834460 * (y - 120) ^ 1 +
          4166037680000 * (z - 19 / 4) ^ 2 +
          15308740508475120 * (z - 19 / 4) ^ 1 +
          2920109425513420) +
        73240000 * ((y - 1) ^ 2 * z + (2 * y + 2 * z + 2) * ((1 / 2 : ℝ) * (y ^ 2 - 1))) *
          ((y - 1) * y + y * (z - 11 / 4) - (y - 1) * L) := by
    unfold oddEndpointTwoCostPolynomial fullEndpointPolynomial
    ring
  have hpos :
    0 <
      73240000 * (y - 1) *
        oddEndpointTwoCostPolynomial (L + 7 / 5) (2096 / 1831) y z (7 / 10) (2 * z ^ 2) := by
    nlinarith only [he, hp, hm]
  exact (mul_pos_iff_of_pos_left (by linarith only [hy] : 0 < (73240000 : ℝ) * (y - 1))).mp hpos

/-- At y>=120,z>=19/4 and the tangent coupling for correction 11/4,
the rational branch polynomial is positive. A ring identity separates a positive
shifted polynomial and a nonnegative multiple of the coupling slack. -/
theorem oddEndpoint_branch_1_polynomial_pos {L y z : ℝ} (hy : 120 ≤ y) (hz : 19 / 4 ≤ z)
    (hlink : (y - 1) * L ≤ (y - 1) * y + y * (z - 11 / 4)) :
    0 < oddEndpointTwoCostPolynomial (L) (2096 / 1831) y z (14 / 15) (2 * z ^ 2 + 7 / 5 * z) := by
  have hy1 : 1 ≤ y := by linarith only [hy]
  have hs : 0 ≤ y ^ 2 - 1 := by nlinarith only [hy1]
  have hc : 0 ≤ (y - 1) ^ 2 * z + (2 * y + 2 * z + 2) * ((1 / 2 : ℝ) * (y ^ 2 - 1)) :=
    add_nonneg (mul_nonneg (sq_nonneg _) (by linarith only [hz]))
      (mul_nonneg (by linarith only [hy, hz]) (mul_nonneg (by norm_num only) hs))
  have hm := mul_nonneg hc (sub_nonneg.mpr hlink)
  have hp :=
    oddEndpoint_shifted_branch_1_pos (by linarith only [hy] : 0 ≤ y - 120)
      (by linarith only [hz] : 0 ≤ z - 19 / 4)
  have he :
    219720000 * (y - 1) *
        oddEndpointTwoCostPolynomial (L) (2096 / 1831) y z (14 / 15) (2 * z ^ 2 + 7 / 5 * z) =
      (219720000 * (y - 120) ^ 4 * (z - 19 / 4) ^ 1 + 235751428 * (y - 120) ^ 4 +
          105805059268 * (y - 120) ^ 3 * (z - 19 / 4) ^ 1 +
          115289458963 * (y - 120) ^ 3 +
          878880000 * (y - 120) ^ 2 * (z - 19 / 4) ^ 2 +
          19115156113532 * (y - 120) ^ 2 * (z - 19 / 4) ^ 1 +
          21162172221049 * (y - 120) ^ 2 +
          209612880000 * (y - 120) ^ 1 * (z - 19 / 4) ^ 2 +
          1535548632555600 * (y - 120) ^ 1 * (z - 19 / 4) ^ 1 +
          1727885006485380 * (y - 120) ^ 1 +
          12498113040000 * (z - 19 / 4) ^ 2 +
          46277596299273360 * (z - 19 / 4) ^ 1 +
          52945706087926260) +
        219720000 * ((y - 1) ^ 2 * z + (2 * y + 2 * z + 2) * ((1 / 2 : ℝ) * (y ^ 2 - 1))) *
          ((y - 1) * y + y * (z - 11 / 4) - (y - 1) * L) := by
    unfold oddEndpointTwoCostPolynomial fullEndpointPolynomial
    ring
  have hpos :
    0 <
      219720000 * (y - 1) *
        oddEndpointTwoCostPolynomial (L) (2096 / 1831) y z (14 / 15) (2 * z ^ 2 + 7 / 5 * z) := by
    nlinarith only [he, hp, hm]
  exact (mul_pos_iff_of_pos_left (by linarith only [hy] : 0 < (219720000 : ℝ) * (y - 1))).mp hpos

/-- For y>=1,z>=0, increasing conductor logarithm or either cost decreases
the polynomial. Factor the differences into nonnegative products. This transfers
rational upper budgets to exact logarithmic branch parameters. -/
theorem oddEndpointTwoCostPolynomial_antitone_inputs {L₁ L₂ P y z c₁ c₂ D₁ D₂ : ℝ} (hy : 1 ≤ y)
    (hz : 0 ≤ z) (hL : L₁ ≤ L₂) (hc : c₁ ≤ c₂) (hD : D₁ ≤ D₂) :
    oddEndpointTwoCostPolynomial L₂ P y z c₂ D₂ ≤ oddEndpointTwoCostPolynomial L₁ P y z c₁ D₁ := by
  have hs : 0 ≤ y ^ 2 - 1 := by nlinarith only [hy]
  have ha : 0 ≤ 2 * y + 2 * z + 2 := by linarith only [hy, hz]
  have hcoef : 0 ≤ (y - 1) ^ 2 * z + (2 * y + 2 * z + 2) * ((1 / 2 : ℝ) * (y ^ 2 - 1)) :=
    add_nonneg (mul_nonneg (sq_nonneg _) hz) (mul_nonneg ha (mul_nonneg (by norm_num only) hs))
  have hmL := mul_nonneg hcoef (sub_nonneg.mpr hL)
  have hmc := mul_nonneg (mul_nonneg ha (sq_nonneg y)) (sub_nonneg.mpr hc)
  have hmD := mul_nonneg (sq_nonneg (y - 1)) (sub_nonneg.mpr hD)
  unfold oddEndpointTwoCostPolynomial fullEndpointPolynomial
  nlinarith only [hmL, hmc, hmD]

end PseudoPrime.LLS.PaperStatements
