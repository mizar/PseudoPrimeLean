/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.FarResolventBounds

/-!
# Nearby-zero approximation of the completed logarithmic derivative

The right-line local count and distant resolvent mass give a nearby simple-pole
expansion for an entire regularized completion without a Riemann hypothesis.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- The multiplicity-weighted simple resolvent at s for zero locations within
unit height distance from T, and zero elsewhere. Summing these terms isolates
the nearby poles in the logarithmic derivative approximation. -/
noncomputable def nearZeroResolventTerm (F : ℂ → ℂ) (T : ℝ) (s ρ : ℂ) : ℂ := by
  classical exact if |T - ρ.im| < 1 then (analyticOrderNatAt F ρ : ℂ) / (s - ρ) else 0

/-- For critical-strip zeros, the nearby resolvent at 3+iT has norm at most
half the unit-window multiplicity. The real distance to the strip is at least
two, and nonzero function values have multiplicity zero. This supplies a
summable majorant for the nearby correction at the reference line. -/
theorem norm_nearRightResolvent_le_localMultiplicity {F : ℂ → ℂ}
    (hstrip : ∀ ρ, F ρ = 0 → 0 ≤ ρ.re ∧ ρ.re ≤ 1) (T : ℝ) (ρ : ℂ) :
    ‖nearZeroResolventTerm F T (((3 : ℝ) : ℂ) + T * Complex.I) ρ‖ ≤
      (1 / 2 : ℝ) * localZeroMultiplicity F T ρ := by
  classical
  by_cases hn : |T - ρ.im| < 1
  · simp only [nearZeroResolventTerm, ite_eq_left hn, localZeroMultiplicity, ite_eq_left hn.le,
      norm_div, Complex.norm_natCast]
    by_cases hz : F ρ = 0
    · have hr : 2 ≤ ‖(((3 : ℝ) : ℂ) + T * Complex.I) - ρ‖ := by
        have hh := Complex.re_le_norm ((((3 : ℝ) : ℂ) + T * Complex.I) - ρ)
        simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero] at hh
        linarith only [hh, (hstrip ρ hz).2]
      have hb :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg (analyticOrderNatAt F ρ) : (0 : ℝ) ≤ _)
          (by norm_num only : (0 : ℝ) < 2) hr
      convert hb using 1
      ring
    · have ho : analyticOrderNatAt F ρ = 0 := by
        rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hz), ENat.toNat_zero]
      simp only [ho, Nat.cast_zero, zero_div, mul_zero, le_refl]
  · simp only [nearZeroResolventTerm, ite_eq_right hn, norm_zero]
    exact mul_nonneg (by norm_num only) (localZeroMultiplicity_nonneg F T ρ)

/-- Entire order-one completion data and its functional equation imply that
the nearby resolvent sum at 3+iT is absolutely convergent and its norm is at
most five times the real logarithmic derivative there. Dominate by half the
local multiplicity sum. This bounds the reference-line nearby correction. -/
theorem summable_nearRightResolvent_and_bound {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) (T : ℝ) :
    Summable (nearZeroResolventTerm F T (((3 : ℝ) : ℂ) + T * Complex.I)) ∧
      ‖∑' ρ : ℂ, nearZeroResolventTerm F T (((3 : ℝ) : ℂ) + T * Complex.I) ρ‖ ≤
        5 * (logDeriv F (((3 : ℝ) : ℂ) + T * Complex.I)).re := by
  have hm := localZeroCount_bound_of_orderAtMostOne hε hfe hright hF h0 horder T
  have hmajor := hm.1.mul_left (1 / 2 : ℝ)
  have hb :=
    norm_nearRightResolvent_le_localMultiplicity
      (fun ρ hz ↦ zero_re_mem_Icc_of_functionalEquation hε hfe hright hz) T
  have hn := hmajor.of_nonneg_of_le (fun ρ ↦ norm_nonneg _) hb
  refine ⟨hn.of_norm, (norm_tsum_le_tsum_norm hn).trans ?_⟩
  have hh := hn.tsum_le_tsum hb hmajor
  rw [tsum_mul_left] at hh
  nlinarith only [hh, hm.2]

/-- The nearby multiplicity-weighted resolvent difference is the difference
of the two nearby simple resolvents, with the same height cutoff. Split on
the cutoff and distribute the multiplicity. This connects the two-point
Hadamard formula to the usual nearby-pole approximation. -/
theorem nearResolventDifference_eq (F : ℂ → ℂ) (s t ρ : ℂ) :
    nearResolventDifferenceTerm F s t ρ =
      nearZeroResolventTerm F s.im s ρ - nearZeroResolventTerm F s.im t ρ := by
  classical
  by_cases hn : |s.im - ρ.im| < 1
  · simp only [nearResolventDifferenceTerm, nearZeroResolventTerm, ite_eq_left hn]
    ring
  · simp only [nearResolventDifferenceTerm, nearZeroResolventTerm, ite_eq_right hn, sub_zero]

/-- Entire subquadratic growth and nonvanishing at zero imply absolute
convergence of the nearby resolvent difference for arbitrary s and t.
Subtract the centered genus-one series and restrict its summable difference
to the height window. This proves convergence before rearranging zero sums. -/
theorem summable_nearResolventDifference {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    {C r : ℝ} (hC : 0 < C) (hr0 : 0 ≤ r) (hr2 : r < 2)
    (hg : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (‖z‖ + 1) ^ r)) (s t : ℂ) :
    Summable (nearResolventDifferenceTerm F s t) := by
  classical
  have hgs := summable_genusTerms_of_entireGrowth hF h0 hC hr0 hr2 hg s
  have hgt := summable_genusTerms_of_entireGrowth hF h0 hC hr0 hr2 hg t
  have hd : Summable (fun ρ : ℂ ↦ (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) - 1 / (t - ρ))) :=
    (hgs.sub hgt).congr (fun ρ ↦ by ring)
  exact
    (hd.indicator {ρ : ℂ | |s.im - ρ.im| < 1}).congr
      (fun ρ ↦ by simp only [Set.indicator, Set.mem_ofPred_eq, nearResolventDifferenceTerm])

/-- For an entire order-one regularized completion satisfying the functional
equation and nonvanishing to the right of the strip, at a nonzero point s the
nearby simple-resolvent sum converges and approximates logDeriv F(s) with
error at most (6+10 times the distance to 3+i Im(s)) times the reference
logarithmic derivative norm. Split the centered Hadamard series into nearby
and distant parts; the local count controls the nearby reference correction
and the quadratic zero mass controls the distant difference. This is the
completed-function analogue of the nearby-zero estimate used in contour
shifts; endpoint and gamma corrections for the ordinary L function are separate. -/
theorem logDeriv_nearZero_error_le {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) (s : ℂ) (hs : F s ≠ 0) :
    Summable (nearZeroResolventTerm F s.im s) ∧
      ‖logDeriv F s - ∑' ρ : ℂ, nearZeroResolventTerm F s.im s ρ‖ ≤
        (6 + 10 * ‖(((3 : ℝ) : ℂ) + s.im * Complex.I) - s‖) *
          ‖logDeriv F (((3 : ℝ) : ℂ) + s.im * Complex.I)‖ := by
  obtain ⟨C, hC, hg⟩ :=
    exists_global_exponential_bound_of_orderAtMostOne hF.continuous horder (r := 3 / 2)
      (by norm_num only)
  let t : ℂ := ((3 : ℝ) : ℂ) + s.im * Complex.I
  have ht : F t ≠ 0 := by
    apply hright
    simp only [t, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero]
    norm_num only
  have hnear :=
    summable_nearResolventDifference hF h0 hC (by norm_num only : (0 : ℝ) ≤ 3 / 2)
      (by norm_num only : (3 / 2 : ℝ) < 2) hg s t
  have hrightnear := summable_nearRightResolvent_and_bound hε hfe hright hF h0 horder s.im
  have hnearS : Summable (nearZeroResolventTerm F s.im s) :=
    (hnear.add hrightnear.1).congr
      (fun ρ ↦ by
        rw [nearResolventDifference_eq]; ring)
  have he := logDeriv_nearDifference_error_le hε hfe hright hF h0 horder s hs
  have hsum :
    (∑' ρ : ℂ, nearResolventDifferenceTerm F s t ρ) =
      (∑' ρ : ℂ, nearZeroResolventTerm F s.im s ρ) -
        ∑' ρ : ℂ, nearZeroResolventTerm F s.im t ρ := by
    rw [← hnearS.tsum_sub hrightnear.1]
    exact tsum_congr (nearResolventDifference_eq F s t)
  change
    ‖logDeriv F s - logDeriv F t - ∑' ρ : ℂ, nearResolventDifferenceTerm F s t ρ‖ ≤
      10 * ‖t - s‖ * (logDeriv F t).re at he
  rw [hsum] at he
  have htri :=
    norm_add_le
      (logDeriv F s - logDeriv F t -
        ((∑' ρ : ℂ, nearZeroResolventTerm F s.im s ρ) - ∑' ρ : ℂ, nearZeroResolventTerm F s.im t ρ))
      (logDeriv F t - ∑' ρ : ℂ, nearZeroResolventTerm F s.im t ρ)
  have htri' := norm_sub_le (logDeriv F t) (∑' ρ : ℂ, nearZeroResolventTerm F s.im t ρ)
  have hid :
    logDeriv F s - logDeriv F t -
          ((∑' ρ : ℂ, nearZeroResolventTerm F s.im s ρ) -
            ∑' ρ : ℂ, nearZeroResolventTerm F s.im t ρ) +
        (logDeriv F t - ∑' ρ : ℂ, nearZeroResolventTerm F s.im t ρ) =
      logDeriv F s - ∑' ρ : ℂ, nearZeroResolventTerm F s.im s ρ := by
    ring
  rw [hid] at htri
  have hr := Complex.re_le_norm (logDeriv F t)
  have hh := mul_le_mul_of_nonneg_left hr (norm_nonneg (t - s))
  refine ⟨hnearS, ?_⟩
  change
    ‖logDeriv F s - ∑' ρ : ℂ, nearZeroResolventTerm F s.im s ρ‖ ≤
      (6 + 10 * ‖t - s‖) * ‖logDeriv F t‖
  nlinarith only [htri, htri', he, hrightnear.2, hr, hh]

/-- Under the regularized completion hypotheses, complex gamma parameter
range, and coefficient and Dirichlet-series logarithmic derivative bounds,
the nearby simple-pole approximation has an explicit logarithmic analytic
conductor error. Combine the order-one nearby-zero expansion with the
right-line conductor norm bound. The endpoint order remains explicit; this
is a quantitative completion estimate for contour shifts, not the full
ordinary-L-function statement with separately removed gamma poles. -/
theorem logDeriv_nearZero_error_le_log_analyticConductor {F L : ℂ → ℂ} {ε : ℂ} {q d : ℕ}
    (hq : 1 ≤ q) (k : ℤ) (κ : Fin d → ℂ) (hκ : ∀ j, -1 < (κ j).re)
    (hreg :
      ∀ z,
        z ≠ 0 →
          z ≠ 1 → F z = (z * (1 - z)) ^ k * ((q : ℂ) ^ (z / 2) * archimedeanGammaFactor κ z * L z))
    (hε : ε ≠ 0) (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ (d : ℝ) * n * Real.log n) (s : ℂ) (hs : F s ≠ 0)
    (hL : L (((3 : ℝ) : ℂ) + s.im * Complex.I) ≠ 0)
    (hdL : DifferentiableAt ℂ L (((3 : ℝ) : ℂ) + s.im * Complex.I))
    (hlog :
      logDeriv L (((3 : ℝ) : ℂ) + s.im * Complex.I) =
        -LSeries a (((3 : ℝ) : ℂ) + s.im * Complex.I)) :
    Summable (nearZeroResolventTerm F s.im s) ∧
      ‖logDeriv F s - ∑' ρ : ℂ, nearZeroResolventTerm F s.im s ρ‖ ≤
        (6 + 10 * ‖(((3 : ℝ) : ℂ) + s.im * Complex.I) - s‖) *
          (2 * |(k : ℝ)| + Real.log (analyticConductor q κ (((3 : ℝ) : ℂ) + s.im * Complex.I)) / 2 +
            (d : ℝ) *
              ((‖Complex.log (Real.pi : ℂ)‖ + Real.pi + Gamma.digammaLogErrorBound) / 2 +
                ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2)) := by
  have hs3 : ((((3 : ℝ) : ℂ) + s.im * Complex.I)).re = 3 := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero]
    norm_num only
  have hb := logDeriv_nearZero_error_le hε hfe hright hF h0 horder s hs
  have hc := norm_logDeriv_le_log_analyticConductor_at_three hq k κ hκ hreg ha hs3 hL hdL hlog
  exact
    ⟨hb.1,
      hb.2.trans
        (mul_le_mul_of_nonneg_left hc
          (by nlinarith only [norm_nonneg ((((3 : ℝ) : ℂ) + s.im * Complex.I) - s)]))⟩

end PseudoPrime.AnalyticNumberTheory.General
