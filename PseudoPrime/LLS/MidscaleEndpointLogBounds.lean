/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.FullEndpointChordTransfer
public import PseudoPrime.LLS.MidscaleEndpointCertificates

/-! # Logarithmic lifts of the continuous midscale endpoint certificates -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a natural exponent k, the rational lower bound for log 2 gives
k*6931/10000 <= log(2^k). Rewriting the logarithm of a positive real power
supplies reusable endpoints for all dyadic logarithmic chords. -/
theorem midscale_log_two_pow_lower (k : ℕ) : (k : ℝ) * (6931 / 10000) ≤ Real.log ((2 : ℝ) ^ k) := by
  rw [Real.log_pow]
  exact
    mul_le_mul_of_nonneg_left
      (le_trans (by norm_num only : (6931 / 10000 : ℝ) ≤ 0.6931471803) Real.log_two_gt_d9.le)
      (Nat.cast_nonneg k)

/-- On a dyadic interval [a,2a] with log a >= k*6931/10000 and
log(2a) >= (k+1)*6931/10000, the indicated affine chord is below log.
Apply the generic endpoint chord theorem to reuse scalar endpoint certificates. -/
theorem midscale_dyadic_chord {a y : ℝ} {k : ℕ} (ha : 0 < a) (hlo : a ≤ y) (hhi : y ≤ 2 * a)
    (hloglo : (k : ℝ) * (6931 / 10000) ≤ Real.log a)
    (hloghi : ((k : ℝ) + 1) * (6931 / 10000) ≤ Real.log (2 * a)) :
    (6931 / 10000 : ℝ) / a * y + ((k : ℝ) - 1) * (6931 / 10000) ≤ Real.log y := by
  apply log_chord_le_of_endpoints ha (by linarith only [ha]) hlo hhi
  · have he := div_mul_cancel₀ (6931 / 10000 : ℝ) ha.ne'
    nlinarith only [he, hloglo]
  · have he := div_mul_cancel₀ (6931 / 10000 : ℝ) ha.ne'
    nlinarith only [he, hloghi]

/-- On 32<=y<=64, replace the lower logarithmic chord in the rational
certificate by log y. Positivity of the logarithmic slope preserves the
strict lower bound and prepares the original-level witness criterion. -/
theorem midscaleEndpoint_log_pos_two {y : ℝ} (hlo : 32 ≤ y) (hhi : y ≤ 64) :
    0 < fullEndpointPolynomial ((3309 / 3200 : ℝ) * y + 103 / 50) (2096 / 1831) y (Real.log y) := by
  have ha := midscale_log_two_pow_lower 5
  have hb := midscale_log_two_pow_lower 6
  norm_num only [Nat.cast_ofNat, pow_succ, pow_zero, mul_one] at ha hb
  have hc :=
    midscale_dyadic_chord (k := 5) (by norm_num only : (0 : ℝ) < 32) hlo (by linarith only [hhi])
      (by
        norm_num only [Nat.cast_ofNat]; exact ha)
      (by
        norm_num only [Nat.cast_ofNat]; exact hb)
  norm_num only [Nat.cast_ofNat] at hc
  exact
    (midscaleEndpoint_base_pos_two hlo hhi).trans_le
      (fullEndpointPolynomial_mono_log_of_level_bound (by linarith only [hlo])
        (by linarith only [hlo]) (by norm_num only) (by linarith only [hlo]) hc)

/-- On 32<=y<=48, the rational lower-logarithm certificate lifts to the
actual logarithm using endpoint bounds at 32 and 48. -/
theorem midscaleEndpoint_log_pos_two_left {y : ℝ} (hlo : 32 ≤ y) (hhi : y ≤ 48) :
    0 < fullEndpointPolynomial ((3337 / 3200 : ℝ) * y + 89 / 50) (2096 / 1831) y (Real.log y) := by
  have ha : (34657 / 10000 : ℝ) ≤ Real.log 32 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_gt_d9]
  have hb : (38712 / 10000 : ℝ) ≤ Real.log 48 := by
    rw [show (48 : ℝ) = 2 ^ 4 * 3 by norm_num only,
      Real.log_mul (by norm_num only) (by norm_num only), Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_gt_d9, Real.log_three_gt_d9]
  have hc :=
    log_chord_le_of_endpoints (m := (811 / 32000 : ℝ)) (c := (26547 / 10000 : ℝ))
      (by norm_num only : (0 : ℝ) < 32) (by norm_num only : (32 : ℝ) < 48) hlo hhi
      (by
        norm_num only; linarith only [ha])
      (by
        norm_num only; linarith only [hb])
  exact
    (midscaleEndpoint_base_pos_two_left hlo hhi).trans_le
      (fullEndpointPolynomial_mono_log_of_level_bound (by linarith only [hlo])
        (by linarith only [hlo]) (by norm_num only) (by linarith only [hlo]) hc)

/-- On 48<=y<=64, the rational lower-logarithm certificate lifts to the
actual logarithm using endpoint bounds at 48 and 64. -/
theorem midscaleEndpoint_log_pos_two_right {y : ℝ} (hlo : 48 ≤ y) (hhi : y ≤ 64) :
    0 < fullEndpointPolynomial ((3281 / 3200 : ℝ) * y + 131 / 50) (2096 / 1831) y (Real.log y) := by
  have ha : (38712 / 10000 : ℝ) ≤ Real.log 48 := by
    rw [show (48 : ℝ) = 2 ^ 4 * 3 by norm_num only,
      Real.log_mul (by norm_num only) (by norm_num only), Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_gt_d9, Real.log_three_gt_d9]
  have hb : (41588 / 10000 : ℝ) ≤ Real.log 64 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_gt_d9]
  have hc :=
    log_chord_le_of_endpoints (m := (719 / 40000 : ℝ)) (c := (7521 / 2500 : ℝ))
      (by norm_num only : (0 : ℝ) < 48) (by norm_num only : (48 : ℝ) < 64) hlo hhi
      (by
        norm_num only; linarith only [ha])
      (by
        norm_num only; linarith only [hb])
  exact
    (midscaleEndpoint_base_pos_two_right hlo hhi).trans_le
      (fullEndpointPolynomial_mono_log_of_level_bound (by linarith only [hlo])
        (by linarith only [hlo]) (by norm_num only) (by linarith only [hlo]) hc)

/-- On 64<=y<=128, monotonicity in the logarithmic argument lifts the third
rational Bernstein certificate to the actual endpoint polynomial. -/
theorem midscaleEndpoint_log_pos_three {y : ℝ} (hlo : 64 ≤ y) (hhi : y ≤ 128) :
    0 < fullEndpointPolynomial ((3259 / 3200 : ℝ) * y + 153 / 50) (2096 / 1831) y (Real.log y) := by
  have ha := midscale_log_two_pow_lower 6
  have hb := midscale_log_two_pow_lower 7
  norm_num only [Nat.cast_ofNat, pow_succ, pow_zero, mul_one] at ha hb
  have hc :=
    midscale_dyadic_chord (k := 6) (by norm_num only : (0 : ℝ) < 64) hlo (by linarith only [hhi])
      (by
        norm_num only [Nat.cast_ofNat]; exact ha)
      (by
        norm_num only [Nat.cast_ofNat]; exact hb)
  norm_num only [Nat.cast_ofNat] at hc
  exact
    (midscaleEndpoint_base_pos_three hlo hhi).trans_le
      (fullEndpointPolynomial_mono_log_of_level_bound (by linarith only [hlo])
        (by linarith only [hlo]) (by norm_num only) (by linarith only [hlo]) hc)

/-- On 128<=y<=256, logarithmic monotonicity lifts the final rational
Bernstein certificate. The radius remains a continuous real variable. -/
theorem midscaleEndpoint_log_pos_four {y : ℝ} (hlo : 128 ≤ y) (hhi : y ≤ 256) :
    0 <
      fullEndpointPolynomial ((12927 / 12800 : ℝ) * y + 83 / 20) (2096 / 1831) y (Real.log y) := by
  have ha := midscale_log_two_pow_lower 7
  have hb := midscale_log_two_pow_lower 8
  norm_num only [Nat.cast_ofNat, pow_succ, pow_zero, mul_one] at ha hb
  have hc :=
    midscale_dyadic_chord (k := 7) (by norm_num only : (0 : ℝ) < 128) hlo (by linarith only [hhi])
      (by
        norm_num only [Nat.cast_ofNat]; exact ha)
      (by
        norm_num only [Nat.cast_ofNat]; exact hb)
  norm_num only [Nat.cast_ofNat] at hc
  exact
    (midscaleEndpoint_base_pos_four hlo hhi).trans_le
      (fullEndpointPolynomial_mono_log_of_level_bound (by linarith only [hlo])
        (by linarith only [hlo]) (by norm_num only) (by linarith only [hlo]) hc)

/-- On 24<=y<=32, the chord through rational lower bounds for log 24 and
log 32 lifts the first Bernstein certificate to the actual logarithm. -/
theorem midscaleEndpoint_log_pos_one {y : ℝ} (hlo : 24 ≤ y) (hhi : y ≤ 32) :
    0 < fullEndpointPolynomial ((837 / 800 : ℝ) * y + 167 / 100) (2096 / 1831) y (Real.log y) := by
  have ha : (31779 / 10000 : ℝ) ≤ Real.log 24 := by
    rw [show (24 : ℝ) = 2 ^ 3 * 3 by norm_num only,
      Real.log_mul (by norm_num only) (by norm_num only), Real.log_pow]
    linarith only [Real.log_two_gt_d9, Real.log_three_gt_d9]
  have hb := midscale_log_two_pow_lower 5
  norm_num only [Nat.cast_ofNat, pow_succ, pow_zero, mul_one] at hb
  have hc :=
    log_chord_le_of_endpoints (m := (719 / 20000 : ℝ)) (c := (23151 / 10000 : ℝ))
      (by norm_num only : (0 : ℝ) < 24) (by norm_num only : (24 : ℝ) < 32) hlo hhi
      (by linarith only [ha]) (by linarith only [hb])
  exact
    (midscaleEndpoint_base_pos_one hlo hhi).trans_le
      (fullEndpointPolynomial_mono_log_of_level_bound (by linarith only [hlo])
        (by linarith only [hlo]) (by norm_num only) (by linarith only [hlo]) hc)

end PseudoPrime.LLS.PaperStatements
