/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleUnitPrincipal
public import PseudoPrime.LLS.RelativeChebyshevLowerBounds
public import PseudoPrime.LLS.RiemannOneSidedCheckpoint
public import PseudoPrime.Analysis.LogTrapezoidBounds

/-! # Sharp relative-width Chebyshev lower bound under RH -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Above one, the logarithmic trivial-zero series decreases with its argument.
Compare its positive summands termwise using monotonicity of inverse powers. -/
theorem refined_trivial_series_antitone {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries y ≤
      AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hy : 1 < y := hx.trans_le hxy
  have hi : y⁻¹ ≤ x⁻¹ := (inv_le_inv₀ (hx0.trans_le hxy) hx0).mpr hxy
  unfold AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries
  apply
    Summable.tsum_le_tsum _ (AnalyticNumberTheory.RiemannZeta.summable_logTrivialZeroTerm hy)
      (AnalyticNumberTheory.RiemannZeta.summable_logTrivialZeroTerm hx)
  intro k
  apply div_le_div_of_nonneg_right _ (mul_nonneg (by norm_num only) (sq_nonneg _))
  exact pow_le_pow_left₀ (inv_nonneg.mpr (hx0.trans_le hxy).le) hi _

/-- Under RH and ordered cutoffs above one, bound the Chebyshev function from below
using the sharp zero mass. Cancel constant terms and compare the decreasing trivial tail. -/
theorem refined_psi_secant (hRH : RiemannHypothesis) {x y : ℝ} (hx : 1 < x) (hxy : x < y) :
    x - ((231 / 5000 : ℝ) * (Real.sqrt x + Real.sqrt y + 2)) * x / (y - x) - (1839 / 1000 : ℝ) ≤
      Chebyshev.psi y := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hy : 1 < y := hx.trans hxy
  have heX := abs_le.mp (LLS.abs_logWeightedMangoldtSum_error_le hRH hx)
  have heY := abs_le.mp (LLS.abs_logWeightedMangoldtSum_error_le hRH hy)
  have hT := refined_trivial_series_antitone hx hxy.le
  have hmassX :=
    mul_le_mul_of_nonneg_right AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_231_div_10000
      (add_nonneg (Real.sqrt_nonneg x) zero_le_one)
  have hmassY :=
    mul_le_mul_of_nonneg_right AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_231_div_10000
      (add_nonneg (Real.sqrt_nonneg y) zero_le_one)
  let U : ℝ :=
    -Real.log (2 * Real.pi) * Real.log x - 1 + Real.pi ^ 2 / 24 -
        AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries x +
      (231 / 5000 : ℝ) * (Real.sqrt x + 1)
  let V : ℝ :=
    Real.log (2 * Real.pi) * Real.log y + 1 - Real.pi ^ 2 / 24 +
      AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries y +
      (231 / 5000 : ℝ) * (Real.sqrt y + 1)
  have hU : AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x ≤ x + U := by
    dsimp only [U]
    linarith only [heX.2, hmassX]
  have hV : y - V ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum y := by
    dsimp only [V]
    linarith only [heY.1, hmassY]
  have hpsi := LLS.psi_lower_of_one_sided_errors hx0 hxy hU hV
  have hc : 0 ≤ Real.log (2 * Real.pi) := by linarith only [Analysis.log_two_mul_pi_gt]
  have hlog := Real.log_le_sub_one_of_pos (div_pos (hx0.trans hxy) hx0)
  rw [div_sub_one hx0.ne', Real.log_div (hx0.trans hxy).ne' hx0.ne'] at hlog
  have hl := mul_le_mul_of_nonneg_left hlog hc
  rw [← mul_div_assoc] at hl
  have hd : 0 < y - x := sub_pos.mpr hxy
  have hcdiv := (le_div_iff₀ hx0).mp hl
  have hl' :
    Real.log (2 * Real.pi) * (Real.log y - Real.log x) * x / (y - x) ≤ Real.log (2 * Real.pi) := by
    apply (div_le_iff₀ hd).mpr
    nlinarith only [hcdiv]
  have hUV :
    U + V ≤
      Real.log (2 * Real.pi) * (Real.log y - Real.log x) +
        (231 / 5000 : ℝ) * (Real.sqrt x + Real.sqrt y + 2) := by
    dsimp only [U, V]
    linarith only [hT]
  have hscaled := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hUV hx0.le) hd.le
  have hc' := Analysis.log_two_mul_pi_lt.le
  ring_nf at hpsi hscaled hl' hc' ⊢
  linarith only [hpsi, hscaled, hl', hc']

/-- Under RH and ordered cutoffs above one, the Chebyshev lower bound retains the
exact logarithmic width. Cancel constant terms and use the decreasing trivial-zero tail. -/
theorem refined_psi_log_secant (hRH : RiemannHypothesis) {x y : ℝ} (hx : 1 < x) (hxy : x < y) :
    (y - x) / Real.log (y / x) -
        ((231 / 5000 : ℝ) * (Real.sqrt x + Real.sqrt y + 2)) / Real.log (y / x) -
        (1839 / 1000 : ℝ) ≤
      Chebyshev.psi y := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hy : 1 < y := hx.trans hxy
  have heX := abs_le.mp (LLS.abs_logWeightedMangoldtSum_error_le hRH hx)
  have heY := abs_le.mp (LLS.abs_logWeightedMangoldtSum_error_le hRH hy)
  have hT := refined_trivial_series_antitone hx hxy.le
  have hmassX :=
    mul_le_mul_of_nonneg_right AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_231_div_10000
      (add_nonneg (Real.sqrt_nonneg x) zero_le_one)
  have hmassY :=
    mul_le_mul_of_nonneg_right AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_231_div_10000
      (add_nonneg (Real.sqrt_nonneg y) zero_le_one)
  let U : ℝ :=
    -Real.log (2 * Real.pi) * Real.log x - 1 + Real.pi ^ 2 / 24 -
        AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries x +
      (231 / 5000 : ℝ) * (Real.sqrt x + 1)
  let V : ℝ :=
    Real.log (2 * Real.pi) * Real.log y + 1 - Real.pi ^ 2 / 24 +
      AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries y +
      (231 / 5000 : ℝ) * (Real.sqrt y + 1)
  have hU : AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x ≤ x + U := by
    dsimp only [U]
    linarith only [heX.2, hmassX]
  have hV : y - V ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum y := by
    dsimp only [V]
    linarith only [heY.1, hmassY]
  have hpsi := LLS.psi_mul_log_lower_of_one_sided_errors hx0 hxy hU hV
  have hUV :
    U + V ≤
      Real.log (2 * Real.pi) * (Real.log y - Real.log x) +
        (231 / 5000 : ℝ) * (Real.sqrt x + Real.sqrt y + 2) := by
    dsimp only [U, V]
    linarith only [hT]
  have hlog : 0 < Real.log (y / x) :=
    Real.log_pos ((lt_div_iff₀ hx0).mpr (by simpa only [one_mul] using hxy))
  have hc := Analysis.log_two_mul_pi_lt.le
  have hi : (y - x - (U + V)) / Real.log (y / x) ≤ Chebyshev.psi y :=
    (div_le_iff₀ hlog).mpr (by linarith only [hpsi])
  have hnum :
    y - x - (231 / 5000 : ℝ) * (Real.sqrt x + Real.sqrt y + 2) ≤
      (y - x - (U + V)) + Real.log (2 * Real.pi) * Real.log (y / x) := by
    rw [Real.log_div (hx0.trans hxy).ne' hx0.ne']
    linarith only [hUV]
  have hn := div_le_div_of_nonneg_right hnum hlog.le
  rw [add_div, mul_div_cancel_right₀ _ hlog.ne'] at hn
  rw [sub_div] at hn
  linarith only [hn, hi, hc]

/-- For a positive relative width at most `H ≤ 1/2`, bound its logarithmic width
below by `h` and above by `h / (1 - h/(2-H))`. Use the logarithmic trapezoid bound. -/
theorem refined_log_window {h H : ℝ} (hh : 0 < h) (hhH : h ≤ H) (hH : H ≤ 1 / 2) :
    h ≤ Real.log (1 / (1 - h)) ∧ Real.log (1 / (1 - h)) ≤ h / (1 - h / (2 - H)) := by
  have hh1 : h < 1 := by linarith only [hhH, hH]
  have hd : 0 < 1 - h := sub_pos.mpr hh1
  have hH2 : 0 < 2 - H := by linarith only [hH]
  have hden : 0 < 1 - h / (2 - H) := by
    have hh' : h / (2 - H) < 1 := (div_lt_one hH2).mpr (by linarith only [hhH, hH])
    linarith only [hh']
  have hl := Real.log_le_sub_one_of_pos hd
  have ht := Analysis.logTrapezoidError_nonneg (div_nonneg hh.le hd.le)
  have he : 1 + h / (1 - h) = 1 / (1 - h) := by
    field_simp (disch :=
      first
      | exact hd.ne'
      | norm_num only)
    ring
  rw [Analysis.logTrapezoidError, he] at ht
  rw [Real.log_div (by norm_num only : (1 : ℝ) ≠ 0) hd.ne', Real.log_one, zero_sub] at ht ⊢
  constructor
  · linarith only [hl]
  · have hab : h * (2 - h) / (2 * (1 - h)) ≤ h / (1 - h / (2 - H)) := by
      apply (div_le_div_iff₀ (mul_pos (by norm_num only) hd) hden).mpr
      have heq : 1 - h / (2 - H) = (2 - H - h) / (2 - H) := by
        field_simp (disch :=
          first
          | exact hH2.ne'
          | norm_num only)
      rw [heq, ← mul_div_assoc]
      apply (div_le_iff₀ hH2).mpr
      have hk := mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hhH)
      nlinarith only [hk]
    have hu : -Real.log (1 - h) ≤ h * (2 - h) / (2 * (1 - h)) := by
      rw [one_div, inv_inv] at ht
      have hr : ((1 / (1 - h) - (1 - h)) / 2) = h * (2 - h) / (2 * (1 - h)) := by
        field_simp (disch :=
          first
          | exact hd.ne'
          | norm_num only)
        ring
      rw [← hr]
      simp only [one_div] at ht ⊢
      linarith only [ht]
    exact hu.trans hab

/-- Under RH, for `0 < h ≤ H ≤ 1/2` and nonnegative `t`, the Chebyshev function
satisfies the sharp relative-width lower estimate with coefficient `231/2500`. Apply
the logarithmic secant above one and treat small arguments using nonnegativity. -/
theorem refined_psi_relative (hRH : RiemannHypothesis) {h H t : ℝ} (hh : 0 < h) (hhH : h ≤ H)
    (hH : H ≤ 1 / 2) (ht : 0 ≤ t) :
    (1 - h / (2 - H)) * t - (231 / 2500 : ℝ) / h * Real.sqrt t - (231 / 2500 : ℝ) / h -
        1839 / 1000 ≤
      Chebyshev.psi t := by
  have hh1 : h < 1 := by linarith only [hhH, hH]
  have hd : 0 < 1 - h := sub_pos.mpr hh1
  have hH2 : 0 < 2 - H := by linarith only [hH]
  have hden : 0 < 1 - h / (2 - H) := by
    have hh' : h / (2 - H) < 1 := (div_lt_one hH2).mpr (by linarith only [hhH, hH])
    linarith only [hh']
  have hhfrac : 0 ≤ h / (2 - H) := div_nonneg hh.le hH2.le
  let z : ℝ := (1 - h) * t
  have hz0 : 0 ≤ z := mul_nonneg hd.le ht
  have hzt : z ≤ t := by
    dsimp only [z]
    nlinarith only [mul_nonneg hh.le ht]
  by_cases hz : 1 < z
  · have hzt' : z < t := by
      dsimp only [z] at hz ⊢
      nlinarith only [mul_pos hh (lt_trans zero_lt_one (hz.trans_le hzt))]
    have hp := refined_psi_log_secant hRH hz hzt'
    have hlogeq : Real.log (t / z) = Real.log (1 / (1 - h)) := by
      have ht0 : 0 < t := zero_lt_one.trans (hz.trans_le hzt)
      dsimp only [z]
      congr 1
      field_simp (disch :=
        first
        | exact hd.ne'
        | exact ht0.ne'
        | norm_num only)
    rw [hlogeq] at hp
    obtain ⟨hlow, hhigh⟩ := refined_log_window hh hhH hH
    have hlog0 : 0 < Real.log (1 / (1 - h)) := hh.trans_le hlow
    have hmain : (1 - h / (2 - H)) * t ≤ (t - z) / Real.log (1 / (1 - h)) := by
      apply (le_div_iff₀ hlog0).mpr
      have hmul := mul_le_mul_of_nonneg_left hhigh (mul_nonneg hden.le ht)
      have hid : (1 - h / (2 - H)) * t * (h / (1 - h / (2 - H))) = t - z := by
        dsimp only [z]
        field_simp (disch :=
          first
          | exact hden.ne'
          | norm_num only)
        ring
      exact hmul.trans_eq hid
    have hs := Real.sqrt_le_sqrt hzt
    have hnum :
      (231 / 5000 : ℝ) * (Real.sqrt z + Real.sqrt t + 2) ≤
        (231 / 2500 : ℝ) * (Real.sqrt t + 1) := by
      linarith only [hs]
    have hdiv := div_le_div_of_nonneg_right hnum hlog0.le
    have hinv := one_div_le_one_div_of_le hh hlow
    have hcost :=
      mul_le_mul_of_nonneg_left hinv
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 231 / 2500)
          (by linarith only [Real.sqrt_nonneg t] : 0 ≤ Real.sqrt t + 1))
    have hcost' :
      (231 / 5000 : ℝ) * (Real.sqrt z + Real.sqrt t + 2) / Real.log (1 / (1 - h)) ≤
        (231 / 2500 : ℝ) / h * Real.sqrt t + (231 / 2500 : ℝ) / h := by
      have hcost0 :
        (231 / 2500 : ℝ) * (Real.sqrt t + 1) / Real.log (1 / (1 - h)) ≤
          (231 / 2500 : ℝ) * (Real.sqrt t + 1) / h := by
        simpa only [div_eq_mul_inv, one_div, one_mul] using hcost
      have h := hdiv.trans hcost0
      ring_nf at h ⊢
      exact h
    linarith only [hp, hmain, hcost']
  · have hzsmall : z ≤ 1 := le_of_not_gt hz
    have htbound : t ≤ 2 := by
      have hs : (1 / 2 : ℝ) ≤ 1 - h := by linarith only [hhH, hH]
      dsimp only [z] at hzsmall
      nlinarith only [hzsmall, mul_nonneg (sub_nonneg.mpr hs) ht]
    have hcost : (231 / 1250 : ℝ) ≤ (231 / 2500 : ℝ) / h := by
      apply (le_div_iff₀ hh).mpr
      linarith only [hhH, hH]
    have hm := mul_nonneg hhfrac ht
    have hc :=
      mul_nonneg (div_nonneg (by norm_num only : (0 : ℝ) ≤ 231 / 2500) hh.le) (Real.sqrt_nonneg t)
    linarith only [htbound, hcost, hm, hc, Chebyshev.psi_nonneg t]

end PseudoPrime.PrimeTestBounds.MillerRabin
