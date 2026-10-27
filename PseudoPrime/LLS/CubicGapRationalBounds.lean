/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.CubicGapPrincipalBounds
public import PseudoPrime.LLS.ReciprocalGapCoupledBudgets

/-! # Rational character budgets for the cubic-gap kernel -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- At real argument 9/5, the uniform odd Gamma upper bound is nonpositive.
Certify digamma(7/5) in a broad rational interval and use log pi > 1.
This supplies the zero-comparison Gamma endpoint for the cubic kernel. -/
theorem cubicGapOddGammaUpper_nonpos : reciprocalGapOddGammaUpper (9 / 5) ≤ 0 := by
  have hd :=
    AnalyticNumberTheory.Gamma.rationalDigammaIntervalCheck_sound
      (show AnalyticNumberTheory.Gamma.rationalDigammaIntervalCheck (7 / 5) 32 6 24 (-1) 1 = true by
        decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one] at hd
  unfold reciprocalGapOddGammaUpper
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
  linarith only [hd.2, Analysis.log_pi_ge_2096_div_1831]

/-- At real argument four, the uniform even Gamma lower bound is at least -11/10.
Certify digamma two in a broad interval and use the existing rational upper
bound for log pi. This supplies the reflected-contour Gamma input. -/
theorem cubicGapEvenGammaLower_ge : -(11 / 10 : ℝ) ≤ reciprocalGapEvenGammaLower 4 := by
  have hd :=
    AnalyticNumberTheory.Gamma.rationalDigammaIntervalCheck_sound
      (show AnalyticNumberTheory.Gamma.rationalDigammaIntervalCheck 2 32 6 24 (-1) 1 = true by
        decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one] at hd
  unfold reciprocalGapEvenGammaLower
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
  linarith only [hd.1, log_pi_le_229_div_200]

/-- The cubic-gap character budget at modulus q and real scale x. Use h=3,
c=13/10,r=1/5, empty positive prefixes, and certified rational Euler/Gamma inputs.
The later upper theorem supplies positivity and primitive GRH hypotheses. -/
noncomputable def cubicGapRationalBudget (q : ℕ) (x : ℝ) : ℝ :=
  (10 / 13 : ℝ) * (Real.log q / 2 + 97 / 100) +
    (reciprocalGapScalarPoleBudget 3 (1 / 5) q x (4481 / 1000) (-(784 / 1000)) 0 +
      reciprocalGapRealAxisBudget 3 q x (97 / 100) (-(11 / 10)) +
      reciprocalGapSignedGammaBudget 3 x)

/-- For primitive nonprincipal GRH data at q ≥ 2 and x ≥ 1, the real cubic
character sum is at most the rational cubic budget. Specialize the general
scalar-prefix bound and supply all six Euler/Gamma certificates internally.
No prime-triviality assumption or finite arithmetic prefix is required. -/
theorem reciprocalGapCharacterSum_three_re_le_rational {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    (reciprocalGapCharacterSum 3 χ x).re ≤ cubicGapRationalBudget q x := by
  have H :
    (reciprocalGapCharacterSum 3 χ x).re ≤
      (1 / (13 / 10 : ℝ)) * (Real.log q / 2 + 0 + 97 / 100 - 0) +
        (reciprocalGapScalarPoleBudget 3 (1 / 5) q x (4481 / 1000) (-(784 / 1000)) 0 +
          reciprocalGapRealAxisBudget 3 q x (97 / 100) (-(11 / 10)) +
          reciprocalGapSignedGammaBudget 3 x) := by
    refine
      reciprocalGapCharacterSum_re_le_scalar_prefix (h := 3) (r := 1 / 5) (c := 13 / 10)
        (by norm_num only) (by norm_num only) hq hGRH hp hne hinv (by norm_num only)
        (by norm_num only) hx ∅ ∅ (97 / 100) 0 (4481 / 1000) (-(784 / 1000)) (97 / 100) (-(11 / 10))
        0 0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact
        AnalyticNumberTheory.Arithmetic.tsum_vonMangoldt_le_seventeen_tenths_certified
          (by norm_num only)
    · have hg :=
        (reciprocalGapGamma_re_le_odd (by norm_num only : (0 : ℝ) < 9 / 5) χ).trans
          cubicGapOddGammaUpper_nonpos
      norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_add,
        Complex.ofReal_one] at hg ⊢
      exact hg
    · exact
        AnalyticNumberTheory.Arithmetic.tsum_vonMangoldt_le_six_fifths_certified (by norm_num only)
    · have hg :=
        (reciprocalGapGamma_re_le_odd (by norm_num only : (0 : ℝ) < 6 / 5) χ⁻¹).trans
          reciprocalGapOddGammaUpper_at_six_fifths
      norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one] at hg ⊢
      exact hg
    · exact
        AnalyticNumberTheory.Arithmetic.tsum_vonMangoldt_le_seventeen_tenths_certified
          (by norm_num only)
    · have hg :=
        cubicGapEvenGammaLower_ge.trans
          (reciprocalGapEvenGammaLower_le (by norm_num only : (0 : ℝ) < 4) χ⁻¹)
      norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one] at hg ⊢
      exact hg
    · norm_num only [Finset.sum_empty]
    · norm_num only [Finset.sum_empty]
  simpa only [cubicGapRationalBudget, add_zero, sub_zero,
    show (1 / (13 / 10 : ℝ)) = 10 / 13 by norm_num only] using H

/-- For q ≥ 2 and x ≥ 1, the rational cubic budget is bounded by a linear
conductor term plus a reciprocal-square-root correction. Retain nonnegative
Gamma-profile savings and bound the reflected power by one. This is the
explicit character-side estimate used in the proposed R3 comparison. -/
theorem cubicGapRationalBudget_le_explicit {q : ℕ} (hq : 2 ≤ q) {x : ℝ} (hx : 1 ≤ x) :
    cubicGapRationalBudget q x ≤
      ((5 / 13 : ℝ) * Real.log q + 257 / 130) +
        ((2 / 5 : ℝ) * Real.log q + 122917 / 15000) / Real.sqrt x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hs1 : 1 ≤ Real.sqrt x := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hq)
  have hL := Real.log_nonneg hq1
  have hp0 : 0 ≤ x ^ (-(3 : ℝ)) := Real.rpow_nonneg hx0.le _
  have hp1 : x ^ (-(3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num only)
  have hleft : x ^ (-(3 : ℝ)) * ((207 / 100 : ℝ) - Real.log q) ≤ 207 / 100 := by
    have ha :=
      mul_le_mul_of_nonneg_left
        (show (207 / 100 : ℝ) - Real.log q ≤ 207 / 100 by linarith only [hL]) hp0
    have hb := mul_le_mul_of_nonneg_right hp1 (by norm_num only : (0 : ℝ) ≤ 207 / 100)
    exact ha.trans (by simpa only [one_mul] using hb)
  have hprof := mul_nonneg (reciprocalGapProfile_nonneg (by norm_num only : (0 : ℝ) < 3) x) hs.le
  have he :
    cubicGapRationalBudget q x * Real.sqrt x =
      ((5 / 13 : ℝ) * Real.log q + 97 / 130) * Real.sqrt x + (2 / 5 : ℝ) * Real.log q +
          25879 / 15000 +
          x ^ (-(3 : ℝ)) * ((207 / 100 : ℝ) - Real.log q) / 3 +
          9 / 2 -
        (3 / 4 : ℝ) * reciprocalGapProfile 3 x * Real.sqrt x := by
    unfold cubicGapRationalBudget reciprocalGapScalarPoleBudget reciprocalGapRealAxisBudget
      reciprocalGapSignedGammaBudget
    rw [reciprocalGap_left_power_factor (h := 3) hx0, Real.sqrt_inv]
    field_simp [hs.ne']
    ring
  apply (mul_le_mul_iff_right₀ hs).mp
  simp only [mul_comm (Real.sqrt x)]
  rw [he]
  simp only [add_mul, div_mul_cancel₀ _ hs.ne']
  nlinarith only [hleft, hprof, hs1]

/-- For primitive nonprincipal GRH data at q ≥ 2 and x ≥ 1, the real cubic
character sum obeys the explicit conductor and reciprocal-square-root bound.
Compose the certified character budget and its scalar simplification.
This discharges the character-side estimate in the R3 design. -/
theorem reciprocalGapCharacterSum_three_re_le_explicit {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    (reciprocalGapCharacterSum 3 χ x).re ≤
      ((5 / 13 : ℝ) * Real.log q + 257 / 130) +
        ((2 / 5 : ℝ) * Real.log q + 122917 / 15000) / Real.sqrt x := by
  exact
    (reciprocalGapCharacterSum_three_re_le_rational hq hGRH hp hne hinv hx).trans
      (cubicGapRationalBudget_le_explicit hq hx)

/-- Under the primitive GRH hypotheses and x ≥ 1, undo the square-root
normalization to obtain the explicit upper bound for S3(x,chi). Multiply the
proved normalized bound by positive sqrt x and cancel its denominator.
This matches the unnormalized character inequality in the R3 design. -/
theorem sqrt_mul_reciprocalGapCharacterSum_three_re_le {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    Real.sqrt x * (reciprocalGapCharacterSum 3 χ x).re ≤
      ((5 / 13 : ℝ) * Real.log q + 257 / 130) * Real.sqrt x + (2 / 5 : ℝ) * Real.log q +
        122917 / 15000 := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr (zero_lt_one.trans_le hx)
  have hm :=
    mul_le_mul_of_nonneg_right
      (reciprocalGapCharacterSum_three_re_le_explicit hq hGRH hp hne hinv hx) hs.le
  rw [add_mul, div_mul_cancel₀ _ hs.ne'] at hm
  nlinarith only [hm]

/-- Primitive nonprincipal GRH data and a strict explicit cubic budget below
sqrt x/4-3 produce a non-one prime through x. Compose the certified character
upper bound with the analytic principal extraction. No Gamma or Euler inputs
remain as external assumptions; level divisors are allowed zero witnesses. -/
theorem exists_prime_ne_one_of_cubic_explicit_gap {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 < x)
    (hgap :
      ((5 / 13 : ℝ) * Real.log q + 257 / 130) +
          ((2 / 5 : ℝ) * Real.log q + 122917 / 15000) / Real.sqrt x <
        Real.sqrt x / 4 - 3) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  exact
    exists_prime_ne_one_of_cubic_upper χ hGRH.riemann hx
      (reciprocalGapCharacterSum_three_re_le_explicit hq hGRH hp hne hinv hx.le) hgap

end PseudoPrime.LLS.PaperStatements
