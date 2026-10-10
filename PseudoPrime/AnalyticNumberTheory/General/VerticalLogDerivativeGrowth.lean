/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.NearbyZeroExpansion
public import PseudoPrime.AnalyticNumberTheory.General.ConductorGrowth

/-!
# Outer vertical-line logarithmic derivative growth

Nearby zero counts and reflection transfer reference-line bounds to both sides
of the Mellin residue contour.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For zeros in the closed critical strip and a point s with real part at least
two, the nearby multiplicity-weighted resolvent norm is at most the local
unit-height multiplicity. Its distance to each zero is at least one; nonzeros
have zero analytic order. This majorant bounds the nearby sum on an outer line. -/
theorem norm_nearResolvent_le_localMultiplicity {F : ℂ → ℂ}
    (hstrip : ∀ ρ, F ρ = 0 → 0 ≤ ρ.re ∧ ρ.re ≤ 1) (s : ℂ) (hs : 2 ≤ s.re) (ρ : ℂ) :
    ‖nearZeroResolventTerm F s.im s ρ‖ ≤ localZeroMultiplicity F s.im ρ := by
  classical
  by_cases hn : |s.im - ρ.im| < 1
  · simp only [nearZeroResolventTerm, ite_eq_left hn, localZeroMultiplicity, ite_eq_left hn.le,
      norm_div, Complex.norm_natCast]
    by_cases hz : F ρ = 0
    · have hr : 1 ≤ ‖s - ρ‖ := by
        have hh := Complex.re_le_norm (s - ρ)
        rw [Complex.sub_re] at hh
        linarith only [hh, hs, (hstrip ρ hz).2]
      exact
        (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num only : (0 : ℝ) < 1) hr).trans_eq
          (div_one _)
    · have ho : analyticOrderNatAt F ρ = 0 := by
        rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hz), ENat.toNat_zero]
      simp only [ho, Nat.cast_zero, zero_div, le_refl]
  · simp only [nearZeroResolventTerm, ite_eq_right hn, norm_zero]
    exact localZeroMultiplicity_nonneg F s.im ρ

/-- For entire order-one completion data nonzero at zero, with conjugate functional
equation and right-half-plane nonvanishing, the nearby resolvent sum at any
point of real part at least two is bounded by ten times the reference
logarithmic derivative norm at 3+i Im(s). Dominate by local multiplicity and
apply the proved local count estimate. This removes individual zero terms
from the outer-line growth bound. -/
theorem norm_nearResolventSum_le_reference {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) (s : ℂ)
    (hs : 2 ≤ s.re) :
    ‖∑' ρ : ℂ, nearZeroResolventTerm F s.im s ρ‖ ≤
      10 * ‖logDeriv F (((3 : ℝ) : ℂ) + s.im * Complex.I)‖ := by
  have hm := localZeroCount_bound_of_orderAtMostOne hε hfe hright hF h0 horder s.im
  have hb :=
    norm_nearResolvent_le_localMultiplicity
      (fun ρ hz ↦ zero_re_mem_Icc_of_functionalEquation hε hfe hright hz) s hs
  have hn := hm.1.of_nonneg_of_le (fun ρ ↦ norm_nonneg _) hb
  exact
    (norm_tsum_le_tsum_norm hn).trans
      ((hn.tsum_le_tsum hb hm.1).trans
        (hm.2.trans (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (by norm_num only))))

/-- For entire order-one completion data nonzero at zero and to the right of the
strip, with conjugate functional equation, the logarithmic derivative at 2+iT
has norm at most 26 times its norm at 3+iT. The nearby resolvent contributes
at most ten reference norms, and the nearby-zero error contributes sixteen.
This transfers the reference-line growth estimate to the contour's right side. -/
theorem norm_logDeriv_at_two_le_reference {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) (T : ℝ) :
    ‖logDeriv F (((2 : ℝ) : ℂ) + T * Complex.I)‖ ≤
      26 * ‖logDeriv F (((3 : ℝ) : ℂ) + T * Complex.I)‖ := by
  let s : ℂ := ((2 : ℝ) : ℂ) + T * Complex.I
  have hre : s.re = 2 := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have him : s.im = T := by
    simp only [s, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
  have hs :=
    hright s
      (by
        rw [hre]; norm_num only)
  have he := (logDeriv_nearZero_error_le hε hfe hright hF h0 horder s hs).2
  have hn := norm_nearResolventSum_le_reference hε hfe hright hF h0 horder s (by rw [hre])
  have hd : (((3 : ℝ) : ℂ) + s.im * Complex.I) - s = 1 := by
    rw [him]
    dsimp only [s]
    rw [Complex.ofReal_ofNat, Complex.ofReal_ofNat]
    ring
  rw [hd, norm_one, him] at he
  rw [him] at hn
  have ht :=
    norm_add_le (logDeriv F s - ∑' ρ : ℂ, nearZeroResolventTerm F T s ρ)
      (∑' ρ : ℂ, nearZeroResolventTerm F T s ρ)
  rw [sub_add_cancel] at ht
  change ‖logDeriv F s‖ ≤ _
  linarith only [ht, he, hn]

/-- For an entire function with a nonzero conjugate functional equation constant,
its logarithmic derivative norms at -1+iT and 2+iT agree. Reflection sends the
first point to the second, and conjugation and negation preserve norm.
This transfers right-side growth bounds to the left contour line. -/
theorem norm_logDeriv_at_minus_one_eq_two {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hF : Differentiable ℂ F) (T : ℝ) :
    ‖logDeriv F (((-1 : ℝ) : ℂ) + T * Complex.I)‖ =
      ‖logDeriv F (((2 : ℝ) : ℂ) + T * Complex.I)‖ := by
  rw [logDeriv_eq_neg_conjugateReflection hε hfe (hF _), norm_neg, norm_star]
  have he : 1 - star (((-1 : ℝ) : ℂ) + T * Complex.I) = (((2 : ℝ) : ℂ) + T * Complex.I) := by
    simp only [Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
      Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat, map_neg, map_one]
    ring
  rw [he]

/-- For entire order-one completion data nonzero at zero and right of the strip,
a linear logarithmic derivative bound on real part three gives a common
linear bound on real parts two and minus one. Use the nearby-zero comparison
and reflection, with multiplier 26. These outer-line bounds suffice for
integrability after multiplying by a rapidly decaying Mellin test. -/
theorem vertical_logDeriv_linear_bound {F : ℂ → ℂ} {ε : ℂ} {A : ℝ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F)
    (href : ∀ T : ℝ, ‖logDeriv F (((3 : ℝ) : ℂ) + T * Complex.I)‖ ≤ A * (1 + |T|)) :
    ∀ T : ℝ,
      ‖logDeriv F (((2 : ℝ) : ℂ) + T * Complex.I)‖ ≤ (26 * A) * (1 + |T|) ∧
        ‖logDeriv F (((-1 : ℝ) : ℂ) + T * Complex.I)‖ ≤ (26 * A) * (1 + |T|) := by
  intro T
  have hb :=
    (norm_logDeriv_at_two_le_reference hε hfe hright hF h0 horder T).trans
      (mul_le_mul_of_nonneg_left (href T) (by norm_num only : (0 : ℝ) ≤ 26))
  rw [← mul_assoc] at hb
  exact ⟨hb, (norm_logDeriv_at_minus_one_eq_two hε hfe hF T).trans_le hb⟩

/-- General completion data with admissible complex gamma shifts, entire
order-one regularization nonzero at zero, conjugate functional equation and
right-half-plane nonvanishing give a positive linear-growth constant for both
outer contour lines. Coefficient bounds and the arithmetic logarithmic
derivative series at real part three first bound that reference line; transfer
the bound to two and minus one. No independent outer-line growth premise
or Riemann hypothesis is required. -/
theorem exists_vertical_logDeriv_linear_bound_of_completion {F L : ℂ → ℂ} {ε : ℂ} {q d : ℕ}
    (hq : 1 ≤ q) (k : ℤ) (κ : Fin d → ℂ) (hκ : ∀ j, -1 < (κ j).re)
    (hreg :
      ∀ z,
        z ≠ 0 →
          z ≠ 1 → F z = (z * (1 - z)) ^ k * ((q : ℂ) ^ (z / 2) * archimedeanGammaFactor κ z * L z))
    (hε : ε ≠ 0) (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ (d : ℝ) * n * Real.log n)
    (hL : ∀ T : ℝ, L (((3 : ℝ) : ℂ) + T * Complex.I) ≠ 0)
    (hdL : ∀ T : ℝ, DifferentiableAt ℂ L (((3 : ℝ) : ℂ) + T * Complex.I))
    (hlog :
      ∀ T : ℝ,
        logDeriv L (((3 : ℝ) : ℂ) + T * Complex.I) = -LSeries a (((3 : ℝ) : ℂ) + T * Complex.I)) :
    ∃ A : ℝ,
      0 < A ∧
        ∀ T : ℝ,
          ‖logDeriv F (((2 : ℝ) : ℂ) + T * Complex.I)‖ ≤ A * (1 + |T|) ∧
            ‖logDeriv F (((-1 : ℝ) : ℂ) + T * Complex.I)‖ ≤ A * (1 + |T|) := by
  obtain ⟨A, hA, href⟩ :=
    exists_norm_logDeriv_at_three_le_linear_height hq k κ hκ hreg ha hL hdL hlog
  exact
    ⟨26 * A, mul_pos (by norm_num only) hA,
      vertical_logDeriv_linear_bound hε hfe hright hF h0 horder href⟩

end PseudoPrime.AnalyticNumberTheory.General
