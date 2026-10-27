/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SmallScaleConductorLogBounds

/-! # Affine conductor coefficients in small-scale logarithmic comparisons -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For x ≥ 81, log(x) ≤ sqrt(x)/2. Apply the logarithm tangent at three to
the fourth root and compare its linear and quadratic powers.
This retains the smaller logarithmic cost in affine conductor bounds. -/
theorem log_le_half_sqrt_of_ge_eightyOne {x : ℝ} (hx : 81 ≤ x) : Real.log x ≤ Real.sqrt x / 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only) hx
  have hs : (9 : ℝ) ≤ Real.sqrt x :=
    Real.le_sqrt_of_sq_le
      (by
        norm_num only at hx ⊢; exact hx)
  have hy : (3 : ℝ) ≤ Real.sqrt (Real.sqrt x) :=
    Real.le_sqrt_of_sq_le
      (by
        norm_num only at hs ⊢; exact hs)
  have hy0 : 0 < Real.sqrt (Real.sqrt x) := lt_of_lt_of_le (by norm_num only) hy
  have ht := Analysis.log_le_log_add_sub_div (a := (3 : ℝ)) (by norm_num only) hy0
  have hl : Real.log x = 4 * Real.log (Real.sqrt (Real.sqrt x)) := by
    rw [Real.log_sqrt (Real.sqrt_nonneg x), Real.log_sqrt hx0.le]
    ring
  have hle : Real.log x ≤ (3 / 2 : ℝ) * Real.sqrt (Real.sqrt x) := by
    rw [hl]
    linarith only [ht, hy, Real.log_three_lt_d9]
  have he := Real.sq_sqrt (Real.sqrt_nonneg x)
  have hm := mul_nonneg (Real.sqrt_nonneg (Real.sqrt x)) (sub_nonneg.mpr hy)
  nlinarith only [hle, he, hm]

/-- Under GRH for primitive χ of level q ≥ 3 and x ≥ 100, its logarithmic sum
has norm at most (3log(q)+20)sqrt(x). Retain log(x) ≤ sqrt(x)/2 and sqrt(x) ≥ 10
when absorbing endpoint and parity costs. This improves the previous 6(log(q)+6) coefficient. -/
theorem norm_characterLogWeightedSum_le_affine_sqrt {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 3 ≤ q) (hp : χ.IsPrimitive) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x : ℝ} (hx : 100 ≤ x) :
    ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ‖ ≤
      (3 * Real.log q + 20) * Real.sqrt x := by
  have hx1 : 1 < x := (by norm_num only : (1 : ℝ) < 100).trans_le hx
  have hs : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx1.le
  have hl0 := (Real.log_pos hx1).le
  have hls := log_sq_le_three_sqrt_of_ge_eightyOne ((by norm_num only : (81 : ℝ) ≤ 100).trans hx)
  have hs10 : (10 : ℝ) ≤ Real.sqrt x :=
    Real.le_sqrt_of_sq_le
      (by
        norm_num only at hx ⊢; exact hx)
  have hl := log_le_half_sqrt_of_ge_eightyOne ((by norm_num only : (81 : ℝ) ≤ 100).trans hx)
  have hq0 := Real.log_natCast_nonneg q
  have hnorm := norm_characterLogWeightedSum_le_explicit hq hp hGRH hx1
  have hB := abs_primitiveBRe_le_norm_logDeriv_xi_zero hq hp hGRH
  have hD := norm_logDeriv_xi_zero_le_log_add_six hq hp hGRH
  have hb :=
    mul_le_mul_of_nonneg_right (hB.trans hD) (show 0 ≤ 2 * Real.sqrt x + 2 by linarith only [hs])
  have hd := mul_le_mul_of_nonneg_right hD hl0
  have hc := abs_logCorrection_le_log_sq_of_ge_hundred χ hx
  have hlog := abs_log_level_div_pi_le_log_add_two (q := q)
  have hcorr :
    |Real.log ((q : ℝ) / Real.pi) * Real.log x / 2 + logCorrection χ x| ≤
      (Real.log q + 2) * Real.log x / 2 + (Real.log x) ^ 2 := by
    have ha := abs_add_le (Real.log ((q : ℝ) / Real.pi) * Real.log x / 2) (logCorrection χ x)
    rw [abs_div, abs_mul, abs_of_nonneg hl0] at ha
    rw [abs_of_pos (by norm_num only : (0 : ℝ) < 2)] at ha
    have hm := mul_le_mul_of_nonneg_right hlog hl0
    linarith only [ha, hc, hm]
  have hprod := mul_nonneg hq0 (show 0 ≤ Real.sqrt x / 2 - Real.log x by linarith only [hl])
  have hprod2 := mul_nonneg (by linarith only [hq0] : 0 ≤ Real.log q + 6) (sub_nonneg.mpr hs10)
  nlinarith only [hnorm, hb, hd, hcorr, hl, hs, hq0, hls, hprod, hprod2]

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

/-- Under RH and y ≥ 200, the principal logarithmic half-difference is at
least y/2-sqrt(y)/2. Retain the corrected logarithmic formulas and sqrt(y) ≥ 14.
This improves the former four-square-root allowance. -/
theorem principal_log_half_difference_lower_half_sqrt (hRH : RiemannHypothesis) {y : ℝ}
    (hy : 200 ≤ y) :
    y / 2 - Real.sqrt y / 2 ≤
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum y -
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (y / 2) := by
  have hy0 : 0 < y := (by norm_num only : (0 : ℝ) < 200).trans_le hy
  have hy1 : 1 < y := (by norm_num only : (1 : ℝ) < 200).trans_le hy
  have hh : 1 < y / 2 := by linarith only [hy]
  have hA := (abs_le.mp (LLS.logWeightedMangoldtSum_log_shift_error_le hRH hy1)).1
  have hB := (abs_le.mp (LLS.logWeightedMangoldtSum_log_shift_error_le hRH hh)).2
  have hs := Real.sqrt_le_sqrt (show y / 2 ≤ y by linarith only [hy0])
  have hs2 : 14 ≤ Real.sqrt y :=
    (Real.le_sqrt (by norm_num only) hy0.le).mpr
      (by
        norm_num only; linarith only [hy])
  rw [Real.log_div hy0.ne' (by norm_num only : (2 : ℝ) ≠ 0)] at hB
  have hpi := Analysis.log_two_mul_pi_lt
  have hpi0 : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by linarith only [Real.pi_gt_three] : 1 ≤ 2 * Real.pi)
  have hcost := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le hpi0
  have hprod : Real.log (2 * Real.pi) * Real.log 2 ≤ 2 := by nlinarith only [hcost, hpi]
  nlinarith only [hA, hB, hs, hs2, hprod]

/-- Under GRH for primitive χ of level q ≥ 3 and excluded m ≠ 0, absence of
non-one prime values through y ≥ 200 forces the displayed affine comparison.
Retain the half-scale square-root ratio, log two and the improved principal error.
Both conductor and exclusion coefficients are smaller. -/
theorem log_half_no_witness_affine_conductor_comparison {q m : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hm : m ≠ 0) {y : ℝ}
    (hy : 200 ≤ y) (hno : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ y → ¬p ∣ m → χ p = 1) :
    y / 2 ≤
      ((21 / 4 : ℝ) * Real.log q + 607 / 10) * Real.sqrt y +
        (7 / 5 : ℝ) * (∑ p ∈ m.primeFactors, Real.log p) := by
  have hy0 : 0 < y := (by norm_num only : (0 : ℝ) < 200).trans_le hy
  have hh : 100 ≤ y / 2 := by linarith only [hy]
  have hhalf : y / 2 ≤ y := by linarith only [hy0]
  have hb :=
    AnalyticNumberTheory.Arithmetic.log_difference_prime_exclusion χ hm
      (div_pos hy0 (by norm_num only : (0 : ℝ) < 2)) hhalf hno
  have hr : y / (y / 2) = 2 := by field_simp [hy0.ne']
  rw [hr] at hb
  have hP := principal_log_half_difference_lower_half_sqrt hGRH.riemann hy
  have hR :=
    norm_characterLogWeightedSum_le_affine_sqrt hq hp hGRH
      ((by norm_num only : (100 : ℝ) ≤ 200).trans hy)
  have hL := norm_characterLogWeightedSum_le_affine_sqrt hq hp hGRH hh
  have hs : Real.sqrt (y / 2) ≤ (3 / 4 : ℝ) * Real.sqrt y := by
    apply Real.sqrt_le_iff.mpr
    exact
      ⟨mul_nonneg (by norm_num only) (Real.sqrt_nonneg y), by
        nlinarith only [Real.sq_sqrt hy0.le, hy0]⟩
  have hcoef : 0 ≤ 3 * Real.log q + 20 := by linarith only [Real.log_natCast_nonneg q]
  have hLs := mul_le_mul_of_nonneg_left hs hcoef
  have hnorm :=
    (Complex.re_le_norm
          (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum y χ -
            AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y / 2) χ)).trans
      (norm_sub_le _ _)
  have ht := psi_sub_theta_le_eighteen_sqrt ((by norm_num only : (1 : ℝ) ≤ 200).trans hy)
  have hsum : 0 ≤ ∑ p ∈ m.primeFactors, Real.log p :=
    Finset.sum_nonneg (fun p _ ↦ Real.log_natCast_nonneg p)
  have htail := Chebyshev.theta_le_psi y
  have hln2 : Real.log (2 : ℝ) ≤ 7 / 10 := by linarith only [Real.log_two_lt_d9]
  have hscale1 :=
    mul_le_mul_of_nonneg_right hln2
      (show 0 ≤ (∑ p ∈ m.primeFactors, Real.log p) + Chebyshev.psi y - Chebyshev.theta y by
        linarith only [hsum, htail])
  nlinarith only [hb, hP, hR, hL, hLs, hnorm, ht, hscale1]

end PseudoPrime.LLS.PaperStatements
