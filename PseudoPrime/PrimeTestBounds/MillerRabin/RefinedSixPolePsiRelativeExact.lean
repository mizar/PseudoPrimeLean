/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPolePsiRelative

/-! # Relative Chebyshev bound retaining the logarithmic constant -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, the logarithmic secant bound retains the exact constant
`log (2 * pi)`. This form permits its cancellation in centered Abel estimates. -/
theorem refined_psi_log_secant_exact (hRH : RiemannHypothesis) {x y : ℝ} (hx : 1 < x)
    (hxy : x < y) :
    (y - x) / Real.log (y / x) -
        ((231 / 5000 : ℝ) * (Real.sqrt x + Real.sqrt y + 2)) / Real.log (y / x) -
        Real.log (2 * Real.pi) ≤
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
  linarith only [hn, hi]

/-- For a relative window above one, RH gives the Chebyshev lower bound with
the exact logarithmic constant retained. This is the form used in centered Abel cancellation. -/
theorem refined_psi_relative_exact (hRH : RiemannHypothesis) {h H t : ℝ} (hh : 0 < h) (hhH : h ≤ H)
    (hH : H ≤ 1 / 2) (ht : 0 ≤ t) (hz : 1 < (1 - h) * t) :
    (1 - h / (2 - H)) * t - (231 / 2500 : ℝ) / h * Real.sqrt t - (231 / 2500 : ℝ) / h -
        Real.log (2 * Real.pi) ≤
      Chebyshev.psi t := by
  have hh1 : h < 1 := by linarith only [hhH, hH]
  have hd : 0 < 1 - h := sub_pos.mpr hh1
  have hH2 : 0 < 2 - H := by linarith only [hH]
  have hden : 0 < 1 - h / (2 - H) := by
    have hh' : h / (2 - H) < 1 := (div_lt_one hH2).mpr (by linarith only [hhH, hH])
    linarith only [hh']
  let z : ℝ := (1 - h) * t
  have hz0 : 0 ≤ z := mul_nonneg hd.le ht
  have hzt : z ≤ t := by
    dsimp only [z]
    nlinarith only [mul_nonneg hh.le ht]
  have hz' : 1 < z := hz
  have hzt' : z < t := by
    dsimp only [z] at hz' ⊢
    nlinarith only [mul_pos hh (lt_trans zero_lt_one (hz'.trans_le hzt))]
  have hp := refined_psi_log_secant_exact hRH hz' hzt'
  have hlogeq : Real.log (t / z) = Real.log (1 / (1 - h)) := by
    have ht0 : 0 < t := zero_lt_one.trans (hz'.trans_le hzt)
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
    (231 / 5000 : ℝ) * (Real.sqrt z + Real.sqrt t + 2) ≤ (231 / 2500 : ℝ) * (Real.sqrt t + 1) := by
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

/-- For `r ≥ 34`, specialize the exact relative bound to the window
`h = (3/7)/sqrt r` and `H = 1/10`. This supplies the boundary term in the
centered principal-sum estimate without rounding `log (2*pi)`. -/
theorem refined_psi_relative_scale (hRH : RiemannHypothesis) {r : ℝ} (hr : 34 ≤ r) :
    let h := (3 / 7 : ℝ) / Real.sqrt r
    (1 - h / (19 / 10)) * r ^ 2 - (231 / 2500 : ℝ) / h * r - (231 / 2500 : ℝ) / h -
        Real.log (2 * Real.pi) ≤
      Chebyshev.psi (r ^ 2) := by
  have hr0 : 0 < r := (by norm_num only : (0 : ℝ) < 34).trans_le hr
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hs5 : (5 : ℝ) ≤ Real.sqrt r := Real.le_sqrt_of_sq_le (by nlinarith only [hr])
  have hh : 0 < (3 / 7 : ℝ) / Real.sqrt r := div_pos (by norm_num only) hs
  have hw : (3 / 7 : ℝ) / Real.sqrt r ≤ 1 / 10 := by
    apply (div_le_iff₀ hs).mpr
    linarith only [hs5]
  have hz : 1 < (1 - (3 / 7 : ℝ) / Real.sqrt r) * r ^ 2 := by
    have hm :=
      mul_nonneg (show (0 : ℝ) ≤ 1 / 10 - (3 / 7 : ℝ) / Real.sqrt r by linarith only [hw])
        (sq_nonneg r)
    nlinarith only [hr, hm]
  have hp :=
    refined_psi_relative_exact hRH hh hw (by norm_num only : (1 / 10 : ℝ) ≤ 1 / 2) (sq_nonneg r) hz
  norm_num only [Real.sqrt_sq hr0.le] at hp ⊢
  exact hp

end PseudoPrime.PrimeTestBounds.MillerRabin
