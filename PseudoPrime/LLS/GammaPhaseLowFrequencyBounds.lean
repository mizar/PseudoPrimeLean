/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.PhaseResolvent64ExpTail
public import PseudoPrime.LLS.GammaPhaseCorrectedEulerBounds

/-! # Actual Gamma bounds from low-frequency corrected Euler certificates -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Input: GRH, the primitive-character hypotheses and an order-256 corrected phase
certificate with error 1/25000 only on |t|<=5.
Claim: the actual Gamma arithmetic sum obeys the prefix-plus-remainder upper bound.
Proof: use the certified Gamma norm comparison for every |t|>=5.
Role: leave only the low-frequency phase certificate as a spectral premise. -/
theorem gamma_primitive_sum_re_le_phase64_of_correctedEuler256_low {q m : ℕ} [NeZero m]
    (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) (B : Finset ℕ)
    (hc :
      ∀ t : ℝ,
        |t| ≤ 5 →
          -(Analysis.gammaEulerCorrectedApprox ((1 / 2 : ℂ) + Complex.I * t) 256 *
                    (x : ℂ) ^ (Complex.I * t)).re +
              (1 / 25000 : ℝ) ≤
            Analysis.finiteSignedResolvent Analysis.phaseResolvent64Coefficients t) :
    (∑' k : ℕ, gammaMellinKernel.summand χ x k).re ≤
      AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget χ
          Analysis.phaseResolvent64Coefficients B +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  exact
    gamma_primitive_sum_re_le_phase64_of_correctedEuler256_split hq hm hmq hGRH hp hne hinv hx B hc
      (fun _ ht _ ↦ (Analysis.phase64_norm_Gamma_lt_of_abs_ge_five ht).le)

end PseudoPrime.LLS.PaperStatements
