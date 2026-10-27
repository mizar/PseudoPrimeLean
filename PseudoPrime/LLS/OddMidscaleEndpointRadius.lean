/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.OddMidscaleEndpointCertificate
public import PseudoPrime.LLS.SharpOddEndpointDoubleLogRoot

/-! # An affine intermediate radius for odd-prime non-one witnesses -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For any level L, radius y>=2 and b<=7/10, a positive rational
zero-at-two polynomial implies both correlated conductor-branch inequalities.
Preserve the conductor saving and use monotonicity in the arithmetic costs.
The lemma is independent of the choice of radius and its certification. -/
theorem oddEndpoint_branches_pos_of_zero_pos {L y b : ℝ} (hy : 2 ≤ y) (hb : b ≤ 7 / 10)
    (hp :
      0 <
        oddEndpointTwoCostPolynomial (L + 7 / 5) (2096 / 1831) y (Real.log y) (7 / 10)
          (2 * (Real.log y) ^ 2)) :
    0 <
        oddEndpointTwoCostPolynomial (L + 2 * b) (2096 / 1831) y (Real.log y) b
          (2 * (Real.log y) ^ 2) ∧
      0 <
        oddEndpointTwoCostPolynomial L (2096 / 1831) y (Real.log y) ((4 / 3) * b)
          (2 * (Real.log y) ^ 2 + b * (2 * Real.log y - b)) := by
  have hy1 : 1 ≤ y := by linarith only [hy]
  have hz : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hlevel :=
    oddEndpointTwoCostPolynomial_antitone_level (P := (2096 / 1831 : ℝ)) (c := (7 / 10 : ℝ)) (D :=
      2 * (Real.log y) ^ 2) hy1 hz (by linarith only [hb] : L + 2 * b ≤ L + 7 / 5)
  have hcost0 :=
    oddEndpointTwoCostPolynomial_antitone_cost (L := L + 2 * b) (P := (2096 / 1831 : ℝ)) (D :=
      2 * (Real.log y) ^ 2) hy1 hz hb le_rfl
  have hnz := oddEndpoint_nonzero_polynomial_ge_zero (L := L) (P := (2096 / 1831 : ℝ)) hy hz
  have hm := mul_le_mul_of_nonneg_right hb hz
  have hD :
    2 * (Real.log y) ^ 2 + b * (2 * Real.log y - b) ≤
      2 * (Real.log y) ^ 2 + (7 / 5 : ℝ) * Real.log y := by
    nlinarith only [hm, sq_nonneg b]
  have hC : (4 / 3 : ℝ) * b ≤ 14 / 15 := by linarith only [hb]
  have hcost1 :=
    oddEndpointTwoCostPolynomial_antitone_cost (L := L) (P := (2096 / 1831 : ℝ)) hy1 hz hC hD
  exact ⟨hp.trans_le (hlevel.trans hcost0), hp.trans_le (hnz.trans hcost1)⟩

/-- The affine radius 3200(L-18/25)/3241. Its certified domain is
3259/25<=L<=16277/100, where the radius lies in [128,160].
It is used for odd-prime non-one Jacobi witnesses, independently of the
general prime-witness radius which may admit prime 2. -/
noncomputable def oddMidscaleEndpointRadius (L : ℝ) : ℝ :=
  (3200 / 3241) * (L - 18 / 25)

/-- On its certified level interval, the affine odd-prime radius is in
[128,160] and its zero-at-two polynomial is positive. Invert the affine
level exactly and reuse the logarithmic window certificate. -/
theorem oddMidscaleEndpointRadius_data {L : ℝ} (hlo : 3259 / 25 ≤ L) (hhi : L ≤ 16277 / 100) :
    128 ≤ oddMidscaleEndpointRadius L ∧
      oddMidscaleEndpointRadius L ≤ 160 ∧
      0 <
        oddEndpointTwoCostPolynomial (L + 7 / 5) (2096 / 1831) (oddMidscaleEndpointRadius L)
          (Real.log (oddMidscaleEndpointRadius L)) (7 / 10)
          (2 * (Real.log (oddMidscaleEndpointRadius L)) ^ 2) := by
  have ha : 128 ≤ oddMidscaleEndpointRadius L := by
    dsimp only [oddMidscaleEndpointRadius]
    linarith only [hlo]
  have hb : oddMidscaleEndpointRadius L ≤ 160 := by
    dsimp only [oddMidscaleEndpointRadius]
    linarith only [hhi]
  have hp := oddMidscaleEndpoint_zero_pos ha hb
  have he : (3241 / 3200 : ℝ) * oddMidscaleEndpointRadius L + 18 / 25 = L := by
    dsimp only [oddMidscaleEndpointRadius]
    ring
  rw [he] at hp
  exact ⟨ha, hb, hp⟩

/-- On its certified level interval, the affine radius is strictly below
the previous double-logarithm radius. Use the logarithmic tangent at 144;
the final affine difference has a positive rational lower bound. -/
theorem oddMidscaleEndpointRadius_lt_sharpDoubleLog {L : ℝ} (hlo : 3259 / 25 ≤ L)
    (hhi : L ≤ 16277 / 100) : oddMidscaleEndpointRadius L < sharpOddEndpointDoubleLogRoot L := by
  have h144 : Real.log (144 : ℝ) ≤ 497 / 100 := by
    rw [show (144 : ℝ) = 2 ^ 4 * 3 ^ 2 by norm_num only,
      Real.log_mul (by norm_num only) (by norm_num only), Real.log_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9, Real.log_three_lt_d9]
  have ht :=
    Real.log_le_sub_one_of_pos
      (div_pos (by linarith only [hlo] : 0 < L) (by norm_num only : (0 : ℝ) < 144))
  rw [Real.log_div (by linarith only [hlo] : L ≠ 0) (by norm_num only : (144 : ℝ) ≠ 0)] at ht
  dsimp only [oddMidscaleEndpointRadius, sharpOddEndpointDoubleLogRoot]
  linarith only [ht, h144, hhi]

/-- The squared affine radius is strictly smaller than the previous
double-logarithm squared radius throughout the certified interval.
Multiply the positive radius difference and sum. -/
theorem oddMidscaleEndpointRadius_sq_lt_sharpDoubleLog_sq {L : ℝ} (hlo : 3259 / 25 ≤ L)
    (hhi : L ≤ 16277 / 100) :
    (oddMidscaleEndpointRadius L) ^ 2 < (sharpOddEndpointDoubleLogRoot L) ^ 2 := by
  have hr := (oddMidscaleEndpointRadius_data hlo hhi).1
  have hc := oddMidscaleEndpointRadius_lt_sharpDoubleLog hlo hhi
  have hp :=
    mul_pos (sub_pos.mpr hc)
      (show 0 < sharpOddEndpointDoubleLogRoot L + oddMidscaleEndpointRadius L by
        linarith only [hr, hc])
  nlinarith only [hp]

end PseudoPrime.LLS.PaperStatements
