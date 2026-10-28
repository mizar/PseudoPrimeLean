/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.Euler16CertifiedBounds
public import PseudoPrime.LLS.ReciprocalGapTwoShiftBounds

/-! # Certified scalar Euler caps in a fixed two-shift witness criterion -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For every character and height, the certified Euler cap bounds the logarithmic
 derivative norm throughout the indicated right half-plane. Use absolute convergence
 and the unconditional sixteen-term Euler certificate; no GRH is needed. -/
theorem norm_logDeriv_le_six_fifths_certified {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : (6 / 5 : ℝ) ≤ σ) (t : ℝ) :
    ‖logDeriv χ.LFunction ((σ : ℂ) + t * Complex.I)‖ ≤ (4481 / 1000 : ℝ) := by
  have hn :=
    norm_neg_deriv_div_dirichletLFunction_le_vonMangoldt_tsum χ
      ((by norm_num only : (1 : ℝ) < 6 / 5).trans_le hσ) t
  simp only [neg_div, norm_neg] at hn
  exact hn.trans (Arithmetic.tsum_vonMangoldt_le_six_fifths_certified hσ)

/-- For every character and height, the certified Euler cap bounds the logarithmic
 derivative norm throughout the indicated right half-plane. Use absolute convergence
 and the unconditional sixteen-term Euler certificate; no GRH is needed. -/
theorem norm_logDeriv_le_hundredTwentySeven_hundredths_certified {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : (127 / 100 : ℝ) ≤ σ) (t : ℝ) :
    ‖logDeriv χ.LFunction ((σ : ℂ) + t * Complex.I)‖ ≤ (1597 / 500 : ℝ) := by
  have hn :=
    norm_neg_deriv_div_dirichletLFunction_le_vonMangoldt_tsum χ
      ((by norm_num only : (1 : ℝ) < 127 / 100).trans_le hσ) t
  simp only [neg_div, norm_neg] at hn
  exact hn.trans (Arithmetic.tsum_vonMangoldt_le_hundredTwentySeven_hundredths_certified hσ)

/-- For every character and height, the certified Euler cap bounds the logarithmic
 derivative norm throughout the indicated right half-plane. Use absolute convergence
 and the unconditional sixteen-term Euler certificate; no GRH is needed. -/
theorem norm_logDeriv_le_seventeen_tenths_certified {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : (17 / 10 : ℝ) ≤ σ) (t : ℝ) :
    ‖logDeriv χ.LFunction ((σ : ℂ) + t * Complex.I)‖ ≤ (97 / 100 : ℝ) := by
  have hn :=
    norm_neg_deriv_div_dirichletLFunction_le_vonMangoldt_tsum χ
      ((by norm_num only : (1 : ℝ) < 17 / 10).trans_le hσ) t
  simp only [neg_div, norm_neg] at hn
  exact hn.trans (Arithmetic.tsum_vonMangoldt_le_seventeen_tenths_certified hσ)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
