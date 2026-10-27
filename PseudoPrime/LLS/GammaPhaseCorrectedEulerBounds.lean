/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaEulerCorrectedPhase
public import PseudoPrime.Analysis.GammaEulerCorrected256
public import PseudoPrime.LLS.GammaPhase64CompactBounds

/-! # Actual Gamma arithmetic bounds from corrected finite Euler phase certificates -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Input: GRH, the primitive-character and scale conditions, and a corrected finite Euler
phase certificate
with the explicit approximation allowance throughout the compact frequency interval.
Claim: the actual Gamma arithmetic sum obeys its certified prefix-plus-remainder bound.
Proof: transfer the corrected-product certificate to Gamma and apply the compact comparison.
Role: avoid leaving a special-function approximation as an unproved assumption. -/
theorem gamma_primitive_sum_re_le_phase64_of_correctedEuler {q m : ℕ} [NeZero m] (hq : 20000 ≤ q)
    (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) (B : Finset ℕ) {n : ℕ} (hn : n ≠ 0)
    (hc :
      ∀ t : ℝ,
        |t| ≤ 16 →
          -(Analysis.gammaEulerCorrectedApprox ((1 / 2 : ℂ) + Complex.I * t) n *
                    (x : ℂ) ^ (Complex.I * t)).re +
              Analysis.gammaEulerCorrectedHalfError n ≤
            Analysis.finiteSignedResolvent Analysis.phaseResolvent64Coefficients t) :
    (∑' k : ℕ, gammaMellinKernel.summand χ x k).re ≤
      AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget χ
          Analysis.phaseResolvent64Coefficients B +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  apply gamma_primitive_sum_re_le_phase64_of_compact hq hm hmq hGRH hp hne hinv hx B
  intro t ht
  exact
    (Analysis.neg_re_Gamma_phase_le_corrected (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx) t
          hn).trans
      (hc t ht)

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

/-- Input: the primitive Gamma hypotheses, an order-256 corrected phase certificate
with error 1/25000 on |t|<=5, and a middle-frequency Gamma norm comparison.
Claim: the actual arithmetic sum obeys the prefix-plus-remainder upper bound.
Proof: transfer the certified corrected phase and apply the compact comparison.
Role: expose a fixed short-product entry point for the finite-scale analytic bound. -/
theorem gamma_primitive_sum_re_le_phase64_of_correctedEuler256_split {q m : ℕ} [NeZero m]
    (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) (B : Finset ℕ)
    (hc :
      ∀ t : ℝ,
        |t| ≤ 5 →
          -(Analysis.gammaEulerCorrectedApprox ((1 / 2 : ℂ) + Complex.I * t) 256 *
                    (x : ℂ) ^ (Complex.I * t)).re +
              (1 / 25000 : ℝ) ≤
            Analysis.finiteSignedResolvent Analysis.phaseResolvent64Coefficients t)
    (hmiddle :
      ∀ t : ℝ,
        5 ≤ |t| →
          |t| ≤ 16 →
          ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ ≤
            Analysis.finiteSignedResolvent Analysis.phaseResolvent64Coefficients t) :
    (∑' k : ℕ, gammaMellinKernel.summand χ x k).re ≤
      AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget χ
          Analysis.phaseResolvent64Coefficients B +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  apply gamma_primitive_sum_re_le_phase64_of_compact hq hm hmq hGRH hp hne hinv hx B
  intro t ht
  have hx0 := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx
  by_cases hsmall : |t| ≤ 5
  · exact (Analysis.neg_re_Gamma_phase_le_corrected256 hx0 t).trans (hc t hsmall)
  · exact
      (Analysis.neg_re_mul_imaginary_power_le_norm _ hx0 t).trans
        (hmiddle t (le_of_not_ge hsmall) ht)

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

/-- Input: the primitive Gamma comparison hypotheses, a corrected finite Euler phase
certificate on |t|<=5,
and a Gamma norm comparison on 5<=|t|<=16.
Claim: the actual Gamma arithmetic sum obeys the same prefix-plus-remainder bound.
Proof: combine the low-frequency approximation with the middle norm bound and the proved tail.
Role: avoid paying a uniform absolute approximation error on the decaying spectral tail. -/
theorem gamma_primitive_sum_re_le_phase64_of_correctedEuler_split {q m : ℕ} [NeZero m]
    (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) (B : Finset ℕ) {n : ℕ} (hn : n ≠ 0)
    (hc :
      ∀ t : ℝ,
        |t| ≤ 5 →
          -(Analysis.gammaEulerCorrectedApprox ((1 / 2 : ℂ) + Complex.I * t) n *
                    (x : ℂ) ^ (Complex.I * t)).re +
              Analysis.gammaEulerCorrectedHalfError n ≤
            Analysis.finiteSignedResolvent Analysis.phaseResolvent64Coefficients t)
    (hmiddle :
      ∀ t : ℝ,
        5 ≤ |t| →
          |t| ≤ 16 →
          ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ ≤
            Analysis.finiteSignedResolvent Analysis.phaseResolvent64Coefficients t) :
    (∑' k : ℕ, gammaMellinKernel.summand χ x k).re ≤
      AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget χ
          Analysis.phaseResolvent64Coefficients B +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  apply gamma_primitive_sum_re_le_phase64_of_compact hq hm hmq hGRH hp hne hinv hx B
  intro t ht
  have hx0 := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx
  by_cases hsmall : |t| ≤ 5
  · exact (Analysis.neg_re_Gamma_phase_le_corrected hx0 t hn).trans (hc t hsmall)
  · exact
      (Analysis.neg_re_mul_imaginary_power_le_norm _ hx0 t).trans
        (hmiddle t (le_of_not_ge hsmall) ht)

end PseudoPrime.LLS.PaperStatements
