/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapCertifiedEuler
public import PseudoPrime.AnalyticNumberTheory.Gamma.DigammaRationalCertificate
public import PseudoPrime.Analysis.PrecisePiLogBound

/-! # Rational Gamma bounds in the certified reciprocal-gap witness criterion -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The real logarithm of pi is at most 229/200. Certify log(3.141593)
by a rational Taylor interval and use the strict upper bound for pi.
This supplies the normalization in the even Gamma lower estimate. -/
theorem log_pi_le_229_div_200 : Real.log Real.pi ≤ (229 / 200 : ℝ) := by
  have hc : Analysis.rationalLogIntervalCheck (3141593 / 1000000) 2 12 0 (229 / 200) = true := by
    decide +kernel
  have h := (Analysis.rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : Real.pi ≤ (3141593 / 1000000 : ℝ) := by
    convert Real.pi_lt_d6.le using 1
    norm_num only
  exact (Real.log_le_log Real.pi_pos hpi).trans h

/-- At sigma=127/100, the uniform odd Gamma upper bound is at most -759/1000.
Certify digamma(227/200) and use the rational lower bound for log pi.
This removes the Gamma special value from the zero-comparison budget. -/
theorem reciprocalGapOddGammaUpper_at_127_div_100 :
    reciprocalGapOddGammaUpper (127 / 100) ≤ -(759 / 1000 : ℝ) := by
  have hd :=
    AnalyticNumberTheory.Gamma.rationalDigammaIntervalCheck_sound
      (show
        AnalyticNumberTheory.Gamma.rationalDigammaIntervalCheck (227 / 200) 32 6 24 (-3748 / 10000)
            (-3746 / 10000) =
          true
        by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] at hd
  unfold reciprocalGapOddGammaUpper
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
  linarith only [hd.2, Analysis.log_pi_ge_2096_div_1831]

/-- At sigma=6/5, the uniform odd Gamma upper bound is at most -784/1000.
Certify digamma(11/10) and use the rational lower bound for log pi.
This removes the Gamma special value from the pole budget. -/
theorem reciprocalGapOddGammaUpper_at_six_fifths :
    reciprocalGapOddGammaUpper (6 / 5) ≤ -(784 / 1000 : ℝ) := by
  have hd :=
    AnalyticNumberTheory.Gamma.rationalDigammaIntervalCheck_sound
      (show
        AnalyticNumberTheory.Gamma.rationalDigammaIntervalCheck (11 / 10) 32 6 24 (-4239 / 10000)
            (-4236 / 10000) =
          true
        by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] at hd
  unfold reciprocalGapOddGammaUpper
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
  linarith only [hd.2, Analysis.log_pi_ge_2096_div_1831]

/-- At sigma=17/10, the uniform even Gamma lower bound is at least -1001/1000.
Certify digamma(17/20) and bound log pi above by 229/200.
This removes the Gamma special value from the signed left budget. -/
theorem reciprocalGapEvenGammaLower_at_seventeen_tenths :
    -(1001 / 1000 : ℝ) ≤ reciprocalGapEvenGammaLower (17 / 10) := by
  have hd :=
    AnalyticNumberTheory.Gamma.rationalDigammaIntervalCheck_sound
      (show
        AnalyticNumberTheory.Gamma.rationalDigammaIntervalCheck (17 / 20) 32 6 24 (-8554 / 10000)
            (-8551 / 10000) =
          true
        by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] at hd
  unfold reciprocalGapEvenGammaLower
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
  linarith only [hd.1, log_pi_le_229_div_200]

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

/-- For h,x>0 and r>=0, increasing the Gamma input increases the prefix pole budget.
The prefactor and the Gamma coefficient are nonnegative. Other inputs are arbitrary.
This supports replacing exact Gamma values by certified upper endpoints. -/
theorem reciprocalGapPrefixPoleBudget_mono_gamma {h r x M G G' : ℝ} (hh : 0 < h) (hr : 0 ≤ r)
    (hx : 0 < x) (q : ℕ) (B : Finset ℕ) (hG : G ≤ G') :
    reciprocalGapPrefixPoleBudget h r q x M G B ≤ reciprocalGapPrefixPoleBudget h r q x M G' B := by
  unfold reciprocalGapPrefixPoleBudget
  apply mul_le_mul_of_nonneg_left
  · exact
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left (by linarith only [hG]) (by linarith only [hr] : 0 ≤ 1 + 2 * r))
  · exact (one_div_pos.mpr (mul_pos hh (Real.sqrt_pos.mpr hx))).le

/-- For h,x>0, increasing the Gamma input decreases the signed real-axis budget.
Multiply the reversed scalar comparison by its positive prefactor.
This preserves the direction required when using a certified Gamma lower endpoint. -/
theorem reciprocalGapRealAxisBudget_antitone_gamma {h x M G G' : ℝ} (hh : 0 < h) (hx : 0 < x)
    (q : ℕ) (hG : G ≤ G') :
    reciprocalGapRealAxisBudget h q x M G' ≤ reciprocalGapRealAxisBudget h q x M G := by
  unfold reciprocalGapRealAxisBudget
  exact
    mul_le_mul_of_nonneg_left (by linarith only [hG]) (div_pos (Real.rpow_pos_of_pos hx _) hh).le

/-- The fixed-gap certified Euler budget with three arbitrary scalar Gamma inputs.
The modulus q, radius x and supports B0,B1 remain variable; operations are totalized.
Comparison and witness theorems supply positivity and endpoint conditions. -/
noncomputable def reciprocalGapScalarSeparation (q : ℕ) (x : ℝ) (B₀ B₁ : Finset ℕ) (G₀ G₁ G₂ : ℝ) :
    ℝ :=
  (100 / 77) *
      (Real.log q / 2 + G₀ + 1597 / 500 -
        2 * ∑ n ∈ B₀, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (127 / 100 : ℝ)) +
    (reciprocalGapPrefixPoleBudget (7 / 10) (1 / 5) q x (4481 / 1000) G₁ B₁ +
      reciprocalGapRealAxisBudget (7 / 10) q x (97 / 100) G₂ +
      reciprocalGapSignedGammaBudget (7 / 10) x)

/-- For x>0, upper endpoints for both odd Gamma values and a lower endpoint for
the even Gamma value bound the certified separation budget by its scalar version.
Use the pole monotonicity, left antitonicity and positive zero coefficient. -/
theorem reciprocalGapCertifiedSeparation_le_scalar {x G₀ G₁ G₂ : ℝ} (hx : 0 < x) (q : ℕ)
    (B₀ B₁ : Finset ℕ) (hG₀ : reciprocalGapOddGammaUpper (127 / 100) ≤ G₀)
    (hG₁ : reciprocalGapOddGammaUpper (6 / 5) ≤ G₁)
    (hG₂ : G₂ ≤ reciprocalGapEvenGammaLower (17 / 10)) :
    reciprocalGapCertifiedSeparation q x B₀ B₁ ≤
      reciprocalGapScalarSeparation q x B₀ B₁ G₀ G₁ G₂ := by
  have hz :=
    mul_le_mul_of_nonneg_left
      (show
        Real.log q / 2 + reciprocalGapOddGammaUpper (127 / 100) + 1597 / 500 -
            2 * ∑ n ∈ B₀, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (127 / 100 : ℝ) ≤
          Real.log q / 2 + G₀ + 1597 / 500 -
            2 * ∑ n ∈ B₀, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (127 / 100 : ℝ)
        by linarith only [hG₀])
      (by norm_num only : (0 : ℝ) ≤ 100 / 77)
  have hp :=
    reciprocalGapPrefixPoleBudget_mono_gamma (M := 4481 / 1000)
      (by norm_num only : (0 : ℝ) < 7 / 10) (by norm_num only : (0 : ℝ) ≤ 1 / 5) hx q B₁ hG₁
  have hl :=
    reciprocalGapRealAxisBudget_antitone_gamma (M := 97 / 100) (by norm_num only : (0 : ℝ) < 7 / 10)
      hx q hG₂
  exact add_le_add hz (add_le_add (add_le_add hp hl) (le_refl _))

/-- The fixed-gap separation budget with certified rational Euler and Gamma inputs.
Gamma inputs are -759/1000,-784/1000,-1001/1000; q,x and both finite supports vary.
This removes Gamma special functions and infinite Euler sums from the scalar condition. -/
noncomputable def reciprocalGapRationalGammaSeparation (q : ℕ) (x : ℝ) (B₀ B₁ : Finset ℕ) : ℝ :=
  reciprocalGapScalarSeparation q x B₀ B₁ (-(759 / 1000)) (-(784 / 1000)) (-(1001 / 1000))

/-- For primitive nonprincipal GRH data at q>=2,x>=1 and supports below x, the
rational-Gamma separation below the principal sum produces a non-one prime witness.
Bound the previous budget by certified Gamma endpoints. Values zero remain allowed. -/
theorem exists_prime_not_one_of_reciprocalGap_rationalGamma_separation {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) (B₀ B₁ : Finset ℕ)
    (hB₀ : ∀ n ∈ B₀, (n : ℝ) ≤ x) (hB₁ : ∀ n ∈ B₁, (n : ℝ) ≤ x)
    (hgap :
      reciprocalGapRationalGammaSeparation q x B₀ B₁ <
        (reciprocalGapCharacterSum (7 / 10) (1 : DirichletCharacter ℂ 1) x).re) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  apply
    exists_prime_not_one_of_reciprocalGap_certified_separation hq hGRH hp hne hinv hx B₀ B₁ hB₀ hB₁
  have hbound :=
    reciprocalGapCertifiedSeparation_le_scalar (zero_lt_one.trans_le hx) q B₀ B₁
      reciprocalGapOddGammaUpper_at_127_div_100 reciprocalGapOddGammaUpper_at_six_fifths
      reciprocalGapEvenGammaLower_at_seventeen_tenths
  exact hbound.trans_lt hgap

end PseudoPrime.LLS.PaperStatements
