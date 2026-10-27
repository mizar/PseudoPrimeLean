/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.PhaseResolvent64Tail
public import PseudoPrime.LLS.MellinPhaseCertificateBounds

/-! # Actual Gamma arithmetic bounds from a compact phase certificate -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Input: a positive scale and the candidate's compact Gamma phase comparison.
Claim: the global majorant premise for the Gamma Mellin kernel holds.
Proof: apply the proved tail extension and unfold the Mellin kernel.
Role: feed a compact spectral certificate into the actual explicit formula. -/
theorem gamma_phase64_majorant_of_compact {x : ℝ} (hx : 0 < x)
    (hc :
      ∀ t : ℝ,
        |t| ≤ 16 →
          -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
            Analysis.finiteSignedResolvent Analysis.phaseResolvent64Coefficients t)
    (t : ℝ) :
    -(gammaMellinKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
      Analysis.finiteSignedResolvent Analysis.phaseResolvent64Coefficients t := by
  change -(Complex.Gamma (Complex.I * t + 1 / 2) * (x : ℂ) ^ (Complex.I * t)).re ≤ _
  rw [add_comm (Complex.I * (t : ℂ)) (1 / 2)]
  exact Analysis.phase64_signed_phase_le_of_compact hx hc t

/-- Input: GRH, primitive nonprincipal conductor 3 <= m <= q, q >= 20000, x >= 2,
and the candidate's signed phase comparison only on absolute ordinates at most sixteen.
Claim: the actual Gamma arithmetic sum obeys its prefix-plus-certified-remainder bound.
Proof: the rational node check and the proved spectral tail discharge all other majorant inputs.
Role: leave only a compact phase comparison for this candidate's arithmetic application. -/
theorem gamma_primitive_sum_re_le_phase64_of_compact {q m : ℕ} [NeZero m] (hq : 20000 ≤ q)
    (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) (B : Finset ℕ)
    (hc :
      ∀ t : ℝ,
        |t| ≤ 16 →
          -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
            Analysis.finiteSignedResolvent Analysis.phaseResolvent64Coefficients t) :
    (∑' k : ℕ, gammaMellinKernel.summand χ x k).re ≤
      AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget χ
          Analysis.phaseResolvent64Coefficients B +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  exact
    gamma_primitive_sum_re_le_phase_prefix_of_nodeCheck hq hm hmq hGRH hp hne hinv hx
      Analysis.phaseResolvent64Coefficients Analysis.phaseResolvent64_node_check B
      (gamma_phase64_majorant_of_compact (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx) hc)

end PseudoPrime.LLS.PaperStatements
