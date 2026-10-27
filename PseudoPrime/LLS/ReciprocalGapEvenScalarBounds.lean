/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapEvenGamma
public import PseudoPrime.LLS.ReciprocalGapScalarPrefixBounds

/-! # Even-character scalar budgets with an exact parity saving -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Fixed reciprocal-gap budget for even characters, with Gamma upper endpoints
-1281/1000 and -1342/1000. The modulus, radius and two positive-prefix lower scalars
remain variable. This retains the parity saving in the zero and pole terms. -/
noncomputable def reciprocalGapEvenScalarRationalSeparation (q : ℕ) (x K₀ K₁ : ℝ) : ℝ :=
  (100 / 77) * (Real.log q / 2 + (-(1281 / 1000)) + 1597 / 500 - K₀) +
    (reciprocalGapScalarPoleBudget (7 / 10) (1 / 5) q x (4481 / 1000) (-(1342 / 1000)) K₁ +
      reciprocalGapRealAxisBudget (7 / 10) q x (97 / 100) (-(1001 / 1000)) +
      reciprocalGapSignedGammaBudget (7 / 10) x)

/-- For primitive even nonprincipal GRH data at q>=2 and x>=1, positive-prefix
lower scalars yield the sharper even rational upper bound on the real character sum.
Use the exact even Gamma identity for the character and its inverse.
This is the analytic input for parity-sensitive ambient witness theorems. -/
theorem reciprocalGapCharacterSum_re_le_even_scalar_rational {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (he : χ.Even) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x K₀ K₁ : ℝ} (hx : 1 ≤ x)
    (B₀ B₁ : Finset ℕ)
    (hK₀ :
      K₀ ≤ ∑ n ∈ B₀, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (127 / 100 : ℝ))
    (hK₁ :
      K₁ ≤ ∑ n ∈ B₁, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (6 / 5 : ℝ)) :
    (reciprocalGapCharacterSum (7 / 10) χ x).re ≤
      reciprocalGapEvenScalarRationalSeparation q x K₀ K₁ := by
  have H :
    (reciprocalGapCharacterSum (7 / 10) χ x).re ≤
      (1 / (77 / 100 : ℝ)) * (Real.log q / 2 + (-(1281 / 1000)) + 1597 / 500 - K₀) +
        (reciprocalGapScalarPoleBudget (7 / 10) (1 / 5) q x (4481 / 1000) (-(1342 / 1000)) K₁ +
          reciprocalGapRealAxisBudget (7 / 10) q x (97 / 100) (-(1001 / 1000)) +
          reciprocalGapSignedGammaBudget (7 / 10) x) := by
    refine
      reciprocalGapCharacterSum_re_le_scalar_prefix (h := 7 / 10) (r := 1 / 5) (c := 77 / 100)
        (by norm_num only) (by norm_num only) hq hGRH hp hne hinv (by norm_num only)
        (by norm_num only) hx B₀ B₁ (1597 / 500) (-(1281 / 1000)) (4481 / 1000) (-(1342 / 1000))
        (97 / 100) (-(1001 / 1000)) K₀ K₁ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact
        AnalyticNumberTheory.Arithmetic.tsum_vonMangoldt_le_hundredTwentySeven_hundredths_certified
          (by norm_num only)
    · have hg :=
        (reciprocalGapGamma_re_eq_even he (by norm_num only : (0 : ℝ) < 127 / 100)).le.trans
          reciprocalGapEvenGamma_at_127_div_100
      norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one] at hg ⊢
      exact hg
    · exact
        AnalyticNumberTheory.Arithmetic.tsum_vonMangoldt_le_six_fifths_certified (by norm_num only)
    · have hg :=
        (reciprocalGapGamma_re_eq_even (reciprocalGap_inverse_even he)
              (by norm_num only : (0 : ℝ) < 6 / 5)).le.trans
          reciprocalGapEvenGamma_at_six_fifths
      norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one] at hg ⊢
      exact hg
    · exact
        AnalyticNumberTheory.Arithmetic.tsum_vonMangoldt_le_seventeen_tenths_certified
          (by norm_num only)
    · have hg :=
        reciprocalGapEvenGammaLower_at_seventeen_tenths.trans
          (reciprocalGapEvenGammaLower_le (by norm_num only : (0 : ℝ) < 17 / 10) χ⁻¹)
      norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one] at hg ⊢
      exact hg
    · norm_num only
      exact hK₀
    · norm_num only
      exact hK₁
  norm_num only [reciprocalGapEvenScalarRationalSeparation] at H ⊢
  exact H

/-- For x>0, retaining even parity lowers the previous scalar budget by exactly
261/385+279/(250*sqrt(x)). Expand the two Gamma coefficients and simplify the rational
identity. This quantifies a strict saving independent of the positive-prefix inputs. -/
theorem reciprocalGapEvenScalarRationalSeparation_eq_saving {q : ℕ} {x K₀ K₁ : ℝ} (hx : 0 < x) :
    reciprocalGapEvenScalarRationalSeparation q x K₀ K₁ =
      reciprocalGapScalarRationalSeparation q x K₀ K₁ - 261 / 385 - 279 / (250 * Real.sqrt x) := by
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  unfold reciprocalGapEvenScalarRationalSeparation reciprocalGapScalarRationalSeparation
    reciprocalGapScalarPoleBudget
  field_simp [hs]
  ring

end PseudoPrime.LLS.PaperStatements
