/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaSignedEulerIdentity

/-! # Nonnegative Euler series and finite positive-prefix gains -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Input: any complex Dirichlet character, real exponent and natural index.
Claim: the Mangoldt power term weighted by 1+Re chi is nonnegative.
Proof: the character norm is at most one and the real denominator is nonnegative.
Role: retain a positive Euler prefix before estimating real logarithmic derivatives. -/
theorem positiveEulerTerm_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q) (σ : ℝ) (n : ℕ) :
    0 ≤ (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ := by
  have hc := (Complex.abs_re_le_norm (χ n)).trans (χ.norm_le_one n)
  have hl := (abs_le.mp hc).1
  exact
    div_nonneg (mul_nonneg (by linarith only [hl]) ArithmeticFunction.vonMangoldt_nonneg)
      (Real.rpow_nonneg (Nat.cast_nonneg n) σ)

/-- Input: a complex character and a real exponent greater than one.
Claim: the nonnegative Euler series weighted by 1+Re chi converges.
Proof: add the untwisted and twisted absolutely convergent Mangoldt series.
Role: justify lower bounds by arbitrary finite prime-power prefixes. -/
theorem summable_positiveEuler {q : ℕ} (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ ↦ (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ) := by
  have hs := (Arithmetic.summable_vonMangoldt_div_rpow hσ).add (summable_real_twistedMangoldt χ hσ)
  apply hs.congr
  intro n
  ring

/-- Input: a nonzero level, a character, real exponent greater than one and a finite index set.
Claim: the real L logarithmic derivative is at most principal Euler mass minus the positive prefix.
Proof: use the exact twisted Euler identity and the nonnegative full-series comparison.
Role: supply a kernel-independent form of the retained real-axis Euler gain. -/
theorem re_logDeriv_le_principal_sub_positive_prefix {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (B : Finset ℕ) :
    (logDeriv χ.LFunction (σ : ℂ)).re ≤
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ) -
        ∑ n ∈ B, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ := by
  have hp := (summable_positiveEuler χ hσ).sum_le_tsum B (fun n _ ↦ positiveEulerTerm_nonneg χ σ n)
  have he :
    (∑' n : ℕ, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ) =
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ) +
        (∑' n : ℕ, (χ n).re * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ) := by
    rw [←
      (Arithmetic.summable_vonMangoldt_div_rpow hσ).tsum_add (summable_real_twistedMangoldt χ hσ)]
    apply tsum_congr
    intro n
    ring
  have hL := re_logDeriv_eq_signed_Mangoldt_tsum χ hσ
  linarith only [hp, he, hL]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
