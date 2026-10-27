/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.FullEndpointPolynomial
public import PseudoPrime.Analysis.RealLog

/-! # Analytic endpoint positivity with correction twenty-two fifths on 8<=L<=16 -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For 0<=t<=8 and 0<=u<=1, the displayed shifted polynomial is positive.
Bound t^4 by 8*t^3 and u^2 by one, retaining the nonnegative linear-u part.
This short exact rational comparison certifies a continuous rectangle. -/
theorem fullEndpoint_shifted_rectangle_pos {t u : ℝ} (ht : 0 ≤ t) (ht8 : t ≤ 8) (hu : 0 ≤ u)
    (hu1 : u ≤ 1) :
    0 <
      -2936381 * t ^ 4 + 249964067 * t ^ 3 + 6875705138 * t ^ 2 + 55034505756 * t + 140728453816 +
          u * (93593939 * t ^ 3 + 1823893018 * t ^ 2 + 11028516100 * t + 19540750776) -
        73240000 * (t + 8) ^ 2 * u ^ 2 := by
  have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht 3
  have ht4 : t ^ 4 ≤ 8 * t ^ 3 := by
    have hm := mul_le_mul_of_nonneg_right ht8 ht3
    nlinarith only [hm]
  have hup : u ^ 2 ≤ 1 := by nlinarith only [hu, hu1]
  have hrest := mul_nonneg (sq_nonneg (t + 8)) (sub_nonneg.mpr hup)
  have huc : 0 ≤ 93593939 * t ^ 3 + 1823893018 * t ^ 2 + 11028516100 * t + 19540750776 := by
    nlinarith only [ht, ht3, sq_nonneg t]
  have hum := mul_nonneg hu huc
  nlinarith only [ht4, hrest, hum, ht, ht3, sq_nonneg t]

/-- For 8<=y<=16,2<=z<=3 and the tangent-coupled L upper relation, the endpoint
polynomial with P=2096/1831 is positive. Separate its shifted rectangle part
from a nonnegative multiple of the coupling slack. This keeps L and y correlated
instead of checking individual integer moduli. -/
theorem fullEndpoint_polynomial_pos_on_rectangle {L y z : ℝ} (hy8 : 8 ≤ y) (hy16 : y ≤ 16)
    (hz2 : 2 ≤ z) (hz3 : z ≤ 3) (hlink : (y - 2) * L ≤ (y - 2) * y + y * (2 * z - 22 / 5)) :
    0 < fullEndpointPolynomial L (2096 / 1831) y z := by
  have hy1 : 1 ≤ y := by linarith only [hy8]
  have hc : 0 ≤ (y - 1) ^ 2 * z + (2 * y + 2 * z + 2) * ((1 / 2 : ℝ) * (y ^ 2 - 1)) := by
    have hs : 0 ≤ y ^ 2 - 1 := by nlinarith only [hy1]
    exact
      add_nonneg (mul_nonneg (sq_nonneg _) (by linarith only [hz2]))
        (mul_nonneg (by linarith only [hy8, hz2]) (mul_nonneg (by norm_num only) hs))
  have hm := mul_nonneg hc (sub_nonneg.mpr hlink)
  have hp :=
    fullEndpoint_shifted_rectangle_pos (by linarith only [hy8] : 0 ≤ y - 8)
      (by linarith only [hy16] : y - 8 ≤ 8) (by linarith only [hz2] : 0 ≤ z - 2)
      (by linarith only [hz3] : z - 2 ≤ 1)
  have he :
    18310000 * (y - 2) * fullEndpointPolynomial L (2096 / 1831) y z =
      (-2936381 * (y - 8) ^ 4 + 249964067 * (y - 8) ^ 3 + 6875705138 * (y - 8) ^ 2 +
            55034505756 * (y - 8) +
            140728453816 +
            (z - 2) *
              (93593939 * (y - 8) ^ 3 + 1823893018 * (y - 8) ^ 2 + 11028516100 * (y - 8) +
                19540750776) -
          73240000 * y ^ 2 * (z - 2) ^ 2) +
        18310000 * ((y - 1) ^ 2 * z + (2 * y + 2 * z + 2) * ((1 / 2 : ℝ) * (y ^ 2 - 1))) *
          ((y - 2) * y + y * (2 * z - 22 / 5) - (y - 2) * L) := by
    unfold fullEndpointPolynomial
    ring
  have hpos : 0 < 18310000 * (y - 2) * fullEndpointPolynomial L (2096 / 1831) y z := by
    nlinarith only [he, hp, hm]
  have hcoef : 0 < (18310000 : ℝ) * (y - 2) := by linarith only [hy8]
  exact (mul_pos_iff_of_pos_left hcoef).mp hpos

/-- For 8<=L<=16, the root y=L-2*log L+22/5 lies in [8,16], log y lies in [2,3],
and the tangent-coupled relation holds. Use logarithmic tangents at eight, sixteen
and y, plus certified log-two bounds. These are continuous real estimates. -/
theorem fullEndpoint_fourPointFour_root_data {L : ℝ} (hL8 : 8 ≤ L) (hL16 : L ≤ 16) :
    let y := L - 2 * Real.log L + 22 / 5
    8 ≤ y ∧
      y ≤ 16 ∧
      2 ≤ Real.log y ∧
      Real.log y ≤ 3 ∧ (y - 2) * L ≤ (y - 2) * y + y * (2 * Real.log y - 22 / 5) := by
  let y := L - 2 * Real.log L + 22 / 5
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 8) hL8
  have he8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have he16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have ht8 := PseudoPrime.Analysis.log_le_log_add_sub_div (by norm_num only : (0 : ℝ) < 8) hL0
  have hy8 : 8 ≤ y := by
    dsimp only [y]
    rw [he8] at ht8
    linarith only [ht8, hL8, Real.log_two_lt_d9]
  have ht16 := PseudoPrime.Analysis.log_le_log_add_sub_div hL0 (by norm_num only : (0 : ℝ) < 16)
  have hratio : (16 - L) / L ≤ (16 - L) / 8 :=
    div_le_div_of_nonneg_left (sub_nonneg.mpr hL16) (by norm_num only) hL8
  have hy16 : y ≤ 16 := by
    dsimp only [y]
    rw [he16] at ht16
    linarith only [ht16, hratio, hL16, Real.log_two_gt_d9]
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 8) hy8
  have hz2 : 2 ≤ Real.log y := by
    have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 8) hy8
    rw [he8] at hl
    linarith only [hl, Real.log_two_gt_d9]
  have hz3 : Real.log y ≤ 3 := by
    have hl := Real.log_le_log hy0 hy16
    rw [he16] at hl
    linarith only [hl, Real.log_two_lt_d9]
  have ht := PseudoPrime.Analysis.log_le_log_add_sub_div hy0 hL0
  have hdiff : Real.log L - Real.log y ≤ (L - y) / y := by linarith only [ht]
  have hm := (le_div_iff₀ hy0).mp hdiff
  have hey := congrArg (fun t : ℝ ↦ y * t) (show y = L - 2 * Real.log L + 22 / 5 from rfl)
  have hlink : (y - 2) * L ≤ (y - 2) * y + y * (2 * Real.log y - 22 / 5) := by
    nlinarith only [hm, hey]
  exact ⟨hy8, hy16, hz2, hz3, hlink⟩

/-- For 8<=L<=16, the endpoint polynomial at root L-2*log L+22/5 and its
logarithm is strictly positive. Supply the continuous rectangle and tangent data.
This certifies correction 4.4 for the full-prime witness comparison on this range. -/
theorem fullEndpoint_polynomial_pos_for_fourPointFour {L : ℝ} (hL8 : 8 ≤ L) (hL16 : L ≤ 16) :
    0 <
      fullEndpointPolynomial L (2096 / 1831) (L - 2 * Real.log L + 22 / 5)
        (Real.log (L - 2 * Real.log L + 22 / 5)) := by
  obtain ⟨hy8, hy16, hz2, hz3, hlink⟩ := fullEndpoint_fourPointFour_root_data hL8 hL16
  exact fullEndpoint_polynomial_pos_on_rectangle hy8 hy16 hz2 hz3 hlink

/-- For 8<=L<=16 and log L>11/5, the correction-4.4 squared radius is strictly
less than L^2. Use root positivity and the negative root correction.
This records the exact strict-log-square portion of the improved analytic range. -/
theorem fullEndpoint_fourPointFour_sq_lt_level_sq {L : ℝ} (hL8 : 8 ≤ L) (hL16 : L ≤ 16)
    (hu : 11 / 5 < Real.log L) : (L - 2 * Real.log L + 22 / 5) ^ 2 < L ^ 2 := by
  have hy := (fullEndpoint_fourPointFour_root_data hL8 hL16).1
  nlinarith only [hy, hL8, hu]

end PseudoPrime.LLS.PaperStatements
