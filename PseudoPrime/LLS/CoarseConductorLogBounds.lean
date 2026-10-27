/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.CosetLogWeightedBounds

/-! # Uniform square-root conductor bounds for logarithmic sums -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH a primitive character of level at least three has xi endpoint
norm at most log(q)+6. Combine the large-level estimate with the small-level cap. -/
theorem norm_logDeriv_xi_zero_le_log_add_six {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ‖logDeriv (xi χ) 0‖ ≤ Real.log q + 6 := by
  by_cases h8 : 8 ≤ q
  · have hb := norm_logDeriv_xi_zero_le_log_level h8 hp hGRH
    rw [Real.log_div (Nat.cast_ne_zero.mpr (NeZero.ne q)) Real.pi_ne_zero] at hb
    have hpi : 0 ≤ Real.log Real.pi :=
      Real.log_nonneg (by linarith only [Real.pi_gt_three] : 1 ≤ Real.pi)
    nlinarith only [hb, hpi, Real.log_natCast_nonneg q]
  · have hb := norm_logDeriv_xi_zero_le_six_of_small_level hq (Nat.lt_of_not_ge h8) hp hGRH
    linarith only [hb, Real.log_natCast_nonneg q]

/-- For nonzero natural q, the absolute logarithmic ratio q/pi is at most
log(q)+2. Bound log(pi) between zero and two. -/
theorem abs_log_level_div_pi_le_log_add_two {q : ℕ} [NeZero q] :
    |Real.log ((q : ℝ) / Real.pi)| ≤ Real.log q + 2 := by
  rw [Real.log_div (Nat.cast_ne_zero.mpr (NeZero.ne q)) Real.pi_ne_zero]
  have hpi : 0 ≤ Real.log Real.pi :=
    Real.log_nonneg (by linarith only [Real.pi_gt_three] : 1 ≤ Real.pi)
  have hpi2 : Real.log Real.pi ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos Real.pi_pos
    have h4 := Real.log_le_log Real.pi_pos Real.pi_lt_four.le
    rw [Real.log_four_eq] at h4
    linarith only [h4, Real.log_two_lt_d9]
  rw [abs_le]
  constructor
  · linarith only [hpi2, Real.log_natCast_nonneg q]
  · linarith only [hpi]

/-- At cutoff at least 65536, either parity correction has absolute value
at most log(x)^2. Use the explicit signed correction intervals and log(x) at least two. -/
theorem abs_logCorrection_le_log_sq {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 65536 ≤ x) :
    |logCorrection χ x| ≤ (Real.log x) ^ 2 := by
  have hx100 : (100 : ℝ) ≤ x := (by norm_num only : (100 : ℝ) ≤ 65536).trans hx
  have hl : 2 ≤ Real.log x := by
    have h :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 8)
        ((by norm_num only : (8 : ℝ) ≤ 65536).trans hx)
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num only, Real.log_pow] at h
    norm_num only at h
    linarith only [h, Real.log_two_gt_d9]
  by_cases he : χ (-1) = 1
  · rw [logCorrection, ite_eq_left he]
    have hb := logCorrectionEven_bounds hx100
    rw [abs_of_nonpos hb.2]
    nlinarith only [hb.1, hl, Real.eulerMascheroniConstant_lt_two_thirds]
  · rw [logCorrection, ite_eq_right he]
    have hb := logCorrectionOdd_bounds hx100
    rw [abs_of_nonpos hb.2]
    nlinarith only [hb.1, hl, Real.log_two_lt_d9, Real.eulerMascheroniConstant_lt_two_thirds]

/-- Under GRH, a primitive character of level at least three and cutoff
at least 65536 has logarithmic sum norm at most 6(log(q)+6)sqrt(x).
Retain the primitive conductor, bound its endpoint and parity correction, and
absorb log(x)^2 by sqrt(x). This is a uniform explicit analytic input. -/
theorem norm_characterLogWeightedSum_le_sqrt_conductor {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 65536 ≤ x) :
    ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ‖ ≤
      6 * (Real.log q + 6) * Real.sqrt x := by
  have hx1 : 1 < x := (by norm_num only : (1 : ℝ) < 65536).trans_le hx
  have hs : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx1.le
  have hl0 := (Real.log_pos hx1).le
  have hls := log_sq_le_sqrt_of_large hx
  have hl : Real.log x ≤ Real.sqrt x := by nlinarith only [hls, hs, sq_nonneg (Real.log x - 1)]
  have hq0 := Real.log_natCast_nonneg q
  have hnorm := norm_characterLogWeightedSum_le_explicit hq hp hGRH hx1
  have hB := abs_primitiveBRe_le_norm_logDeriv_xi_zero hq hp hGRH
  have hD := norm_logDeriv_xi_zero_le_log_add_six hq hp hGRH
  have hb :=
    mul_le_mul_of_nonneg_right (hB.trans hD) (show 0 ≤ 2 * Real.sqrt x + 2 by linarith only [hs])
  have hd := mul_le_mul_of_nonneg_right hD hl0
  have hc := abs_logCorrection_le_log_sq χ hx
  have hlog := abs_log_level_div_pi_le_log_add_two (q := q)
  have hcorr :
    |Real.log ((q : ℝ) / Real.pi) * Real.log x / 2 + logCorrection χ x| ≤
      (Real.log q + 2) * Real.log x / 2 + (Real.log x) ^ 2 := by
    have ha := abs_add_le (Real.log ((q : ℝ) / Real.pi) * Real.log x / 2) (logCorrection χ x)
    rw [abs_div, abs_mul, abs_of_nonneg hl0] at ha
    rw [abs_of_pos (by norm_num only : (0 : ℝ) < 2)] at ha
    have hm := mul_le_mul_of_nonneg_right hlog hl0
    linarith only [ha, hc, hm]
  have hprod := mul_nonneg hq0 (sub_nonneg.mpr hl)
  have hprod2 := mul_nonneg (by linarith only [hq0] : 0 ≤ Real.log q + 6) (sub_nonneg.mpr hs)
  nlinarith only [hnorm, hb, hd, hcorr, hl, hs, hq0, hls, hprod, hprod2]

end PseudoPrime.LLS.PaperStatements
