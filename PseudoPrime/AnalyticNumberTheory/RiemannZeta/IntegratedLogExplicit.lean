/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LogWeightedExact
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.IntegratedChebyshev

/-! # Integrated logarithmic explicit formula

Insert the exact signed zeta-zero expression into the arithmetic difference identity.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The exact logarithmically weighted Mangoldt expression for `x > 1`,
consisting of pole terms, the signed nontrivial-zero series and the trivial-zero
correction. It is integrated to obtain the centered Chebyshev difference. -/
noncomputable def logExplicit (x : ℝ) : ℝ :=
  -RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re - Real.log (2 * Real.pi) * Real.log x + x +
      (∑' ρ : ℂ, nontrivialLogZeroTerm x ρ).re -
    riemannZetaLogTrivialZeroSeries x

/-- Expand the exact logarithmic expression into its pole and zero terms.
This identity allows downstream modules to separate its interval integral. -/
theorem logExplicit_eq (x : ℝ) :
    logExplicit x =
      -RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re - Real.log (2 * Real.pi) * Real.log x +
          x +
          (∑' ρ : ℂ, nontrivialLogZeroTerm x ρ).re -
        riemannZetaLogTrivialZeroSeries x := by
  rfl

/-- For `1 < a ≤ b`, express the integrated Chebyshev difference in terms
of the exact logarithmic zero formula. Substitute the pointwise identity into
the arithmetic partial-summation formula, including its interval integral. -/
theorem psi1_diff_logExplicit {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    Arithmetic.psiIntegralSum b - Arithmetic.psiIntegralSum a =
      b * logExplicit b - a * logExplicit a - ∫ t in a..b, logExplicit t := by
  have heq {x : ℝ} (hx : 1 < x) : Arithmetic.logWeightedMangoldtSum x = logExplicit x :=
    log_weighted_exact hx
  have hi : (∫ t in a..b, Arithmetic.logWeightedMangoldtSum t) = ∫ t in a..b, logExplicit t := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hab]
    intro t ht
    exact heq (lt_of_lt_of_le ha ht.1)
  rw [Arithmetic.psi1_diff (zero_lt_one.trans ha) hab, heq ha, heq (lt_of_lt_of_le ha hab), hi]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
