/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapReflectedGamma

/-! # Scalar Euler and Gamma budgets for the exact reflected left value -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The explicit real-axis left budget x^(-1/2-h)/h*(M-log(q)-G).
The scalar M bounds the ordinary untwisted Euler series at 1+h, and G bounds the
inverse character's Gamma logarithmic derivative below there. Operations are totalized.
This preserves conductor and Gamma savings when replacing the exact character value. -/
noncomputable def reciprocalGapRealAxisBudget (h : ℝ) (q : ℕ) (x M G : ℝ) : ℝ :=
  x ^ (-1 / 2 - h) / h * (M - Real.log q - G)

open AnalyticNumberTheory.DirichletLFunction in
/-- For positive gap and scale, nonzero modulus and nonprincipal inverse character,
an upper bound M for the untwisted Euler series and lower Gamma bound G imply that
the signed real-axis left value is at most the explicit scalar budget.
Use the completed derivative decomposition, character norm bound and the negative
prefactor. This avoids a separate norm estimate on the conductor contribution. -/
theorem reciprocalGapRealAxisLeftValue_le_budget {h x : ℝ} (hh : 0 < h) (hx : 0 < x) {q : ℕ}
    [NeZero q] {χ : DirichletCharacter ℂ q} (hinv : χ⁻¹ ≠ 1) {M G : ℝ}
    (hM : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + h)) ≤ M)
    (hG : G ≤ (logDeriv χ⁻¹.gammaFactor ((1 + h : ℝ) : ℂ)).re) :
    reciprocalGapRealAxisLeftValue h χ x ≤ reciprocalGapRealAxisBudget h q x M G := by
  have hr : 1 < 1 + h := by linarith only [hh]
  have hs : 1 ≤ (((1 + h : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]; linarith only [hh]
  have hs0 : 0 < (((1 + h : ℝ) : ℂ)).re := zero_lt_one.trans_le hs
  have he :=
    logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hinv
      (completedLFunction_ne_zero_of_one_le_re hinv hs) (gammaFactor_ne_zero_of_re_pos χ⁻¹ hs0)
      (analyticAt_gammaFactor_of_re_pos χ⁻¹ hs0).differentiableAt
  have hn := norm_neg_deriv_div_dirichletLFunction_le_vonMangoldt_tsum χ⁻¹ hr 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero, neg_div, norm_neg] at hn
  have hnorm : ‖logDeriv χ⁻¹.LFunction ((1 + h : ℝ) : ℂ)‖ ≤ M := hn.trans hM
  have hl :=
    (neg_le_neg (Complex.abs_re_le_norm (logDeriv χ⁻¹.LFunction ((1 + h : ℝ) : ℂ)))).trans
      (neg_abs_le (logDeriv χ⁻¹.LFunction ((1 + h : ℝ) : ℂ)).re)
  have hleft : -M ≤ (logDeriv χ⁻¹.LFunction ((1 + h : ℝ) : ℂ)).re := by linarith only [hnorm, hl]
  have hEq :
    (logDeriv χ⁻¹.completedLFunction ((1 + h : ℝ) : ℂ)).re =
      (logDeriv χ⁻¹.LFunction ((1 + h : ℝ) : ℂ)).re +
        (logDeriv χ⁻¹.gammaFactor ((1 + h : ℝ) : ℂ)).re := by
    rw [he, Complex.sub_re]
    ring
  have hlow : -M + G ≤ (logDeriv χ⁻¹.completedLFunction ((1 + h : ℝ) : ℂ)).re := by
    rw [hEq]
    linarith only [hleft, hG]
  have hmul := mul_le_mul_of_nonneg_left hlow (div_pos (Real.rpow_pos_of_pos hx (-1 / 2 - h)) hh).le
  unfold reciprocalGapRealAxisLeftValue reciprocalGapRealAxisBudget
  simp only [neg_div]
  nlinarith only [hmul]

/-- For primitive nonprincipal GRH data at level at least eight, positive gap,
admissible zero-test coordinate and scale at least one, scalar Euler/Gamma bounds
and the explicit real-axis separation produce a non-one prime witness.
Bound the exact left value and apply the signed real-axis witness criterion.
The bounds M and G remain arbitrary certified inputs for later quantitative choices. -/
theorem exists_prime_not_one_of_reciprocalGap_realAxis_budget_separation {h c : ℝ} (hh : 0 < h)
    {q : ℕ} [NeZero q] (hq : 8 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hc : (1 / 2 : ℝ) < c) (hbound : c ^ 2 ≤ 1 / 4 + h / 2) {x : ℝ}
    (hx : 1 ≤ x) (B : Finset ℕ) (M G : ℝ)
    (hM : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + h)) ≤ M)
    (hG : G ≤ (logDeriv χ⁻¹.gammaFactor ((1 + h : ℝ) : ℂ)).re)
    (hgap :
      (1 / c) *
            (Real.log q / 2 + (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + c) : ℂ)).re +
                (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) -
              ∑ n ∈ B, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) +
          (((7 / 6 : ℝ) * Real.log q + 4) / (h * Real.sqrt x) +
            reciprocalGapRealAxisBudget h q x M G +
            reciprocalGapSignedGammaBudget h x) <
        (reciprocalGapCharacterSum h (1 : DirichletCharacter ℂ 1) x).re) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  apply
    exists_prime_not_one_of_reciprocalGap_realAxis_separation hh hq hGRH hp hne hinv hc hbound hx B
  have hV := reciprocalGapRealAxisLeftValue_le_budget hh (zero_lt_one.trans_le hx) hinv hM hG
  linarith only [hV, hgap]

end PseudoPrime.LLS.PaperStatements
