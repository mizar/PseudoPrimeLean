/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.PoissonZeroMass

/-!
# Distant-zero resolvent differences

The quadratic height-weighted mass gives absolute convergence and quantitative
bounds away from nearby poles, as required in an explicit-formula contour shift.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For two points at the same imaginary height, a zero at height distance
at least one has resolvent difference bounded by ten times the horizontal
distance divided by the quadratic height profile. The inverse difference
identity and the imaginary-part lower bound control both denominators.
This is the distant-zero estimate used when isolating nearby poles. -/
theorem norm_resolventDifference_le_heightProfile {s t ρ : ℂ} (him : s.im = t.im)
    (hfar : 1 ≤ |s.im - ρ.im|) :
    ‖1 / (s - ρ) - 1 / (t - ρ)‖ ≤ 10 * ‖t - s‖ / (9 + (s.im - ρ.im) ^ 2) := by
  have ha : |s.im - ρ.im| ≤ ‖s - ρ‖ := by
    simpa only [Complex.sub_im] using Complex.abs_im_le_norm (s - ρ)
  have hb : |s.im - ρ.im| ≤ ‖t - ρ‖ := by
    simpa only [Complex.sub_im, ← him] using Complex.abs_im_le_norm (t - ρ)
  have hu : 0 < (s.im - ρ.im) ^ 2 := by
    have hh := (sq_le_sq₀ zero_le_one (abs_nonneg _)).mpr hfar
    rw [one_pow, sq_abs] at hh
    linarith only [hh]
  have hprod : (s.im - ρ.im) ^ 2 ≤ ‖s - ρ‖ * ‖t - ρ‖ := by
    simpa only [← sq, sq_abs] using mul_le_mul ha hb (abs_nonneg _) (norm_nonneg _)
  have hs : s - ρ ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (hfar.trans ha))
  have ht : t - ρ ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (hfar.trans hb))
  rw [one_div, one_div, inv_sub_inv hs ht, show (t - ρ) - (s - ρ) = t - s from by ring, norm_div,
    norm_mul]
  have hh : 9 + (s.im - ρ.im) ^ 2 ≤ 10 * (s.im - ρ.im) ^ 2 := by
    have hsq := (sq_le_sq₀ zero_le_one (abs_nonneg _)).mpr hfar
    rw [one_pow, sq_abs] at hsq
    linarith only [hsq]
  refine (div_le_div_of_nonneg_left (norm_nonneg _) hu hprod).trans ?_
  rw [div_le_div_iff₀ hu (by linarith only [hu])]
  nlinarith only [mul_le_mul_of_nonneg_left hh (norm_nonneg (t - s))]

/-- The multiplicity-weighted resolvent difference at s and t, retaining
only points at height distance at least one from s. The omitted nearby terms
are the poles that must be handled separately in contour shifts. -/
noncomputable def farResolventTerm (F : ℂ → ℂ) (s t ρ : ℂ) : ℂ := by
  classical
    exact
    if 1 ≤ |s.im - ρ.im| then (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) - 1 / (t - ρ)) else 0

/-- For points at equal imaginary height, summability of the weighted
quadratic height profile implies absolute convergence of the distant-zero
resolvent difference and bounds its sum by ten times the horizontal distance
and the profile mass. Pointwise domination justifies both the sum and norm
comparison, so no convergence premise for the resolvent series is needed. -/
theorem summable_farResolventTerm_and_bound {F : ℂ → ℂ} {s t : ℂ} (him : s.im = t.im)
    (hm : Summable (fun ρ : ℂ ↦ (analyticOrderNatAt F ρ : ℝ) / (9 + (s.im - ρ.im) ^ 2))) :
    Summable (farResolventTerm F s t) ∧
      ‖∑' ρ : ℂ, farResolventTerm F s t ρ‖ ≤
        10 * ‖t - s‖ * ∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℝ) / (9 + (s.im - ρ.im) ^ 2) := by
  classical
  have hb :
    ∀ ρ : ℂ,
      ‖farResolventTerm F s t ρ‖ ≤
        (10 * ‖t - s‖) * ((analyticOrderNatAt F ρ : ℝ) / (9 + (s.im - ρ.im) ^ 2)) := by
    intro ρ
    by_cases hfar : 1 ≤ |s.im - ρ.im|
    · simp only [farResolventTerm, ite_eq_left hfar, norm_mul, Complex.norm_natCast]
      have hh :=
        mul_le_mul_of_nonneg_left (norm_resolventDifference_le_heightProfile him hfar)
          (Nat.cast_nonneg (analyticOrderNatAt F ρ) : (0 : ℝ) ≤ _)
      convert hh using 1
      ring
    · simp only [farResolventTerm, ite_eq_right hfar, norm_zero]
      exact
        mul_nonneg (mul_nonneg (by norm_num only) (norm_nonneg _))
          (div_nonneg (Nat.cast_nonneg _) (by nlinarith only [sq_nonneg (s.im - ρ.im)]))
  have hmajor := hm.mul_left (10 * ‖t - s‖)
  have hn := hmajor.of_nonneg_of_le (fun ρ ↦ norm_nonneg _) hb
  refine ⟨hn.of_norm, (norm_tsum_le_tsum_norm hn).trans ?_⟩
  have hh := hn.tsum_le_tsum hb hmajor
  rw [tsum_mul_left] at hh
  exact hh

/-- Entire order-one completion data with its functional equation and
right half-plane nonvanishing bound the distant-zero resolvent difference
between s and 3+i Im(s). The quadratic zero mass is derived from the reflected
Hadamard identity, and then dominates the difference series. This controls
the distant contribution to a nearby-pole expansion without assuming RH. -/
theorem farResolventSum_bound_of_orderAtMostOne {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) (s : ℂ) :
    Summable (farResolventTerm F s (((3 : ℝ) : ℂ) + s.im * Complex.I)) ∧
      ‖∑' ρ : ℂ, farResolventTerm F s (((3 : ℝ) : ℂ) + s.im * Complex.I) ρ‖ ≤
        10 * ‖(((3 : ℝ) : ℂ) + s.im * Complex.I) - s‖ *
          (logDeriv F (((3 : ℝ) : ℂ) + s.im * Complex.I)).re := by
  have him : s.im = ((((3 : ℝ) : ℂ) + s.im * Complex.I)).im := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
  have hm := poissonZeroMass_bound_of_orderAtMostOne hε hfe hright hF h0 horder s.im
  have hb := summable_farResolventTerm_and_bound him hm.1
  exact
    ⟨hb.1,
      hb.2.trans (mul_le_mul_of_nonneg_left hm.2 (mul_nonneg (by norm_num only) (norm_nonneg _)))⟩

/-- The multiplicity-weighted resolvent difference at s and t for zero
locations at height distance strictly less than one from s, and zero elsewhere.
It complements farResolventTerm and isolates nearby poles in the logarithmic
derivative expansion. -/
noncomputable def nearResolventDifferenceTerm (F : ℂ → ℂ) (s t ρ : ℂ) : ℂ := by
  classical
    exact
    if |s.im - ρ.im| < 1 then (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) - 1 / (t - ρ)) else 0

/-- Entire subquadratic growth and nonvanishing at zero, s and t identify
the logarithmic derivative difference with the sum of nearby and distant
zero terms. Given convergence of the distant part, convergence of the nearby
part follows from the centered Hadamard series. Subtracting centered formulas
cancels the constant and reciprocal-zero corrections. This is the exact
identity behind the nearby-zero approximation. -/
theorem logDeriv_sub_eq_near_add_far {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) {C r : ℝ}
    (hC : 0 < C) (hr0 : 0 ≤ r) (hr2 : r < 2) (hg : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (‖z‖ + 1) ^ r))
    {s t : ℂ} (hs : F s ≠ 0) (ht : F t ≠ 0) (hfar : Summable (farResolventTerm F s t)) :
    logDeriv F s - logDeriv F t =
      (∑' ρ : ℂ, nearResolventDifferenceTerm F s t ρ) + ∑' ρ : ℂ, farResolventTerm F s t ρ := by
  classical
  have hgs := summable_genusTerms_of_entireGrowth hF h0 hC hr0 hr2 hg s
  have hgt := summable_genusTerms_of_entireGrowth hF h0 hC hr0 hr2 hg t
  have hdiff : Summable (fun ρ : ℂ ↦ (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) - 1 / (t - ρ))) :=
    (hgs.sub hgt).congr (fun ρ ↦ by ring)
  have hpt :
    ∀ ρ : ℂ,
      (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) - 1 / (t - ρ)) =
        nearResolventDifferenceTerm F s t ρ + farResolventTerm F s t ρ := by
    intro ρ
    by_cases hn : |s.im - ρ.im| < 1
    · simp only [nearResolventDifferenceTerm, farResolventTerm, ite_eq_left hn,
        ite_eq_right (not_le.mpr hn), add_zero]
    · simp only [nearResolventDifferenceTerm, farResolventTerm, ite_eq_right hn,
        ite_eq_left (le_of_not_gt hn), zero_add]
  have hnear : Summable (nearResolventDifferenceTerm F s t) :=
    (hdiff.sub hfar).congr
      (fun ρ ↦ by
        rw [hpt]; ring)
  have he :
    logDeriv F s - logDeriv F t =
      ∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) - 1 / (t - ρ)) := by
    have hs' := centered_logDeriv_eq_genusSum hF h0 hC hr0 hr2 hg hs hgs
    have ht' := centered_logDeriv_eq_genusSum hF h0 hC hr0 hr2 hg ht hgt
    calc
      _ = (logDeriv F s - logDeriv F 0) - (logDeriv F t - logDeriv F 0) := by ring
      _ = _ := by
        rw [hs', ht', ← hgs.tsum_sub hgt]
        exact tsum_congr (fun ρ ↦ by ring)
  rw [he, ← hnear.tsum_add hfar]
  exact tsum_congr hpt

/-- For entire order-one completion data, its functional equation and right
half-plane nonvanishing, subtracting the nearby resolvent differences from
logDeriv F(s)-logDeriv F(3+i Im(s)) leaves an error bounded by the horizontal
distance times the quadratic zero-mass bound. The distant series supplies
the error after the exact Hadamard decomposition. This is a nearby-pole
estimate for the regularized completion, without a Riemann hypothesis. -/
theorem logDeriv_nearDifference_error_le {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) (s : ℂ) (hs : F s ≠ 0) :
    ‖logDeriv F s - logDeriv F (((3 : ℝ) : ℂ) + s.im * Complex.I) -
          ∑' ρ : ℂ, nearResolventDifferenceTerm F s (((3 : ℝ) : ℂ) + s.im * Complex.I) ρ‖ ≤
      10 * ‖(((3 : ℝ) : ℂ) + s.im * Complex.I) - s‖ *
        (logDeriv F (((3 : ℝ) : ℂ) + s.im * Complex.I)).re := by
  obtain ⟨C, hC, hg⟩ :=
    exists_global_exponential_bound_of_orderAtMostOne hF.continuous horder (r := 3 / 2)
      (by norm_num only)
  have ht : F (((3 : ℝ) : ℂ) + s.im * Complex.I) ≠ 0 := by
    apply hright
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero]
    norm_num only
  have hb := farResolventSum_bound_of_orderAtMostOne hε hfe hright hF h0 horder s
  rw [logDeriv_sub_eq_near_add_far hF h0 hC (by norm_num only : (0 : ℝ) ≤ 3 / 2)
      (by norm_num only : (3 / 2 : ℝ) < 2) hg hs ht hb.1,
    add_sub_cancel_left]
  exact hb.2

end PseudoPrime.AnalyticNumberTheory.General
