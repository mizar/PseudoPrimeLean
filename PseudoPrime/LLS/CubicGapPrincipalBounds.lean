/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CubicLogWeightedSummation
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterPrimeTriviality
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExponentialLogWeightedSummation
public import PseudoPrime.LLS.RiemannWeightedErrorBounds
public import PseudoPrime.LLS.ReciprocalGapPrincipalLower
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Analytic principal lower bounds for the cubic-gap kernel -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.Arithmetic in
/-- Under RH and x ≥ 1, the cubic smoothing integral of the logarithmic Mangoldt
sum is at most x⁴/4+sqrt(x)x³/60. Use the existing RH upper bound and monotonicity
of sqrt on the integration interval, then integrate two polynomial terms exactly.
This supplies the negative integral term in the cubic principal lower bound. -/
theorem cubic_log_integral_le (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x, t ^ 2 * logWeightedMangoldtSum t) ≤
      x ^ 4 / 4 + Real.sqrt x * x ^ 3 / 60 := by
  have hA := continuousOn_logWeightedMangoldtSum_scaled (x := 1) (by norm_num only) x
  simp only [one_mul] at hA
  have hA1 : ContinuousOn logWeightedMangoldtSum (Set.uIcc (1 : ℝ) x) := by
    apply hA.mono
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    exact ⟨zero_le_one.trans ht.1, ht.2⟩
  have hiA :
    IntervalIntegrable (fun t : ℝ ↦ t ^ 2 * logWeightedMangoldtSum t) MeasureTheory.volume 1 x :=
    ((continuous_id.pow 2).continuousOn.mul hA1).intervalIntegrable
  have hiB :
    IntervalIntegrable (fun t : ℝ ↦ t ^ 2 * (t + Real.sqrt x / 20)) MeasureTheory.volume 1 x :=
    ((continuous_id.pow 2).mul
          (continuous_id.add (continuous_const (y := Real.sqrt x / 20)))).intervalIntegrable
      1 x
  have hb :=
    intervalIntegral.integral_mono_on_of_le_Ioo (μ := MeasureTheory.volume) hx hiA hiB
      (fun t ht ↦ ?_)
  · have he :
      (fun t : ℝ ↦ t ^ 2 * (t + Real.sqrt x / 20)) =
        (fun t : ℝ ↦ t ^ 3 + (Real.sqrt x / 20) * t ^ 2) := by
      funext t
      ring
    have hi3 : IntervalIntegrable (fun t : ℝ ↦ t ^ 3) MeasureTheory.volume 1 x :=
      (continuous_id.pow 3).intervalIntegrable 1 x
    have hi2 :
      IntervalIntegrable (fun t : ℝ ↦ (Real.sqrt x / 20) * t ^ 2) MeasureTheory.volume 1 x :=
      (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 1 x
    rw [he, intervalIntegral.integral_add hi3 hi2, intervalIntegral.integral_const_mul,
      integral_pow, integral_pow] at hb
    norm_num only [Nat.reduceAdd, Nat.cast_ofNat, one_pow] at hb
    nlinarith only [hb, Real.sqrt_nonneg x]
  · have hs := PseudoPrime.LLS.logWeightedMangoldtSum_le_add_sqrt_twentieth hRH ht.1
    have hroot := Real.sqrt_le_sqrt ht.2.le
    exact
      mul_le_mul_of_nonneg_left
        (show logWeightedMangoldtSum t ≤ t + Real.sqrt x / 20 by linarith only [hs, hroot])
        (sq_nonneg t)

open AnalyticNumberTheory.Arithmetic in
/-- Under RH and x > 1, the cubic-gap Mangoldt sum is at least x/4-sqrt(x)/10
minus the retained logarithmic and constant errors. Combine the exact finite
identity, the integral upper bound and the existing Riemann lower bound.
This is the quantitative principal input before coarse error absorption. -/
theorem cubicGapMangoldtSum_ge_refined (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    x / 4 - Real.sqrt x / 10 - (1839 / 1000 : ℝ) * Real.log x - 21 / 20 ≤
      cubicGapMangoldtSum x := by
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hi :=
    mul_le_mul_of_nonneg_left (cubic_log_integral_le hRH hx.le)
      (div_nonneg (by norm_num only : (0 : ℝ) ≤ 3) (pow_nonneg (zero_lt_one.trans hx).le 3))
  have he : 3 / x ^ 3 * (x ^ 4 / 4 + Real.sqrt x * x ^ 3 / 60) = 3 * x / 4 + Real.sqrt x / 20 := by
    field_simp [hx0]
    ring
  rw [he] at hi
  rw [cubicGapMangoldtSum_eq_log_integral hx.le]
  linarith only [hi, PseudoPrime.LLS.logWeightedMangoldtSum_ge_rational_refined hRH hx]

/-- For x ≥ 1, the logarithm is at most sqrt x. Apply the logarithmic tangent
at two to sqrt x and use log two ≤ 1. This elementary bound absorbs the retained
principal logarithmic error into a fixed square-root cost. -/
theorem log_le_sqrt_of_one_le {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ Real.sqrt x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have ht :=
    Analysis.log_le_log_add_sub_div (by norm_num only : (0 : ℝ) < 2) (Real.sqrt_pos.mpr hx0)
  rw [Real.log_sqrt hx0.le] at ht
  linarith only [ht, Real.log_two_lt_d9]

open AnalyticNumberTheory.Arithmetic in
/-- Under RH and x > 1, the cubic-gap principal sum is at least x/4-3sqrt x.
Absorb the retained logarithmic and constant errors using log x ≤ sqrt x and
sqrt x ≥ 1. This is the simple principal lower bound required for R3. -/
theorem cubicGapMangoldtSum_ge_quarter_sub_three_sqrt (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 1 < x) : x / 4 - 3 * Real.sqrt x ≤ cubicGapMangoldtSum x := by
  have hl := cubicGapMangoldtSum_ge_refined hRH hx
  have hr := log_le_sqrt_of_one_le hx.le
  have hs : 1 ≤ Real.sqrt x := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx.le
  linarith only [hl, hr, hs]

open AnalyticNumberTheory.Arithmetic in
/-- At gap three, the real principal character sum is the cubic Mangoldt sum
divided by sqrt x. Expand the finite weights and convert the real power to a
natural cube. This identifies the arithmetic and Mellin-kernel normalizations. -/
theorem reciprocalGap_principal_three_eq (x : ℝ) :
    (reciprocalGapCharacterSum 3 (1 : DirichletCharacter ℂ 1) x).re =
      cubicGapMangoldtSum x / Real.sqrt x := by
  rw [reciprocalGap_principal_re_eq_sum]
  simp only [cubicGapMangoldtSum, Finset.sum_div, reciprocalGapPrincipalWeight, Real.rpow_ofNat]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Under RH and x > 1, the normalized cubic-gap principal character sum is at
least sqrt x/4-3. Divide the arithmetic principal lower bound by positive sqrt x
and use its square identity. This is ready for the conductor comparison. -/
theorem reciprocalGap_principal_three_ge (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    Real.sqrt x / 4 - 3 ≤ (reciprocalGapCharacterSum 3 (1 : DirichletCharacter ℂ 1) x).re := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr (zero_lt_one.trans hx)
  have hl := div_le_div_of_nonneg_right (cubicGapMangoldtSum_ge_quarter_sub_three_sqrt hRH hx) hs.le
  have he : (x / 4 - 3 * Real.sqrt x) / Real.sqrt x = Real.sqrt x / 4 - 3 := by
    field_simp [hs.ne']
    nlinarith only [Real.sq_sqrt (zero_lt_one.trans hx).le]
  rw [he] at hl
  rw [reciprocalGap_principal_three_eq]
  exact hl

open AnalyticNumberTheory.Arithmetic in
/-- For a nonnegative cutoff and a character equal to one on every prime through x,
its real gap sum equals the principal real gap sum for any real gap h.
Mangoldt-zero terms vanish; every remaining index is a prime power with value one.
This transfers prime witness nonexistence to the analytic principal lower bound. -/
theorem reciprocalGap_re_eq_principal_of_prime_trivial {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 ≤ x) (h : ℝ) (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → χ p = 1) :
    (reciprocalGapCharacterSum h χ x).re =
      (reciprocalGapCharacterSum h (1 : DirichletCharacter ℂ 1) x).re := by
  rw [reciprocalGap_principal_re_eq_sum, reciprocalGapCharacterSum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · simp only [hΛ, zero_div, Complex.ofReal_zero, zero_mul, Complex.zero_re,
      reciprocalGapPrincipalWeight]
  · have hnle : (n : ℝ) ≤ x := (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le hx)
    rw [character_apply_one_of_mangoldt_ne_zero χ hsmall hnle hΛ]
    simp only [mul_one, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      reciprocalGapPrincipalWeight]

/-- Under RH and x > 1, any upper budget U for the cubic character sum strictly
below sqrt x/4-3 produces a prime through x where the character is not one.
Witness nonexistence identifies the character and principal sums, contradicting
the proved principal lower bound. Divisors of the level are allowed zero witnesses. -/
theorem exists_prime_ne_one_of_cubic_upper {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hRH : RiemannHypothesis) {x U : ℝ} (hx : 1 < x) (hU : (reciprocalGapCharacterSum 3 χ x).re ≤ U)
    (hgap : U < Real.sqrt x / 4 - 3) : ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  by_contra hn
  have ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → χ p = 1 := by
    intro p hp hpx
    by_contra hv
    exact hn ⟨p, hp, hpx, hv⟩
  have he := reciprocalGap_re_eq_principal_of_prime_trivial χ (zero_lt_one.trans hx).le 3 ht
  have hl := reciprocalGap_principal_three_ge hRH hx
  rw [he] at hU
  exact (not_lt_of_ge (hl.trans hU)) hgap

end PseudoPrime.LLS.PaperStatements
