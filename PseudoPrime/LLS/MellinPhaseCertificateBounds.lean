/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteSignedEulerCertificate
public import PseudoPrime.LLS.MellinPhaseResolventBounds

/-! # Phase-sensitive bounds from finite rational Euler certificates -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- Input: GRH, a primitive nonprincipal character, positive scale,
a successful rational node check,
and a global one-sided majorant of the signed Mellin phase.
Claim: the actual negative real zero sum is bounded by the Euler prefix budget.
Proof: the rational certificate proves whole-halfline Mangoldt-weight positivity.
Role: remove an unproved real positivity premise from the generic phase interface. -/
theorem neg_re_oscillatingZeroSum_le_prefix_of_nodeCheck (K : MellinKernel) {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (l : List (ℚ × ℚ))
    (hc : Analysis.finiteSignedPhaseNodeCheck l = true) (B : Finset ℕ)
    (hphase :
      ∀ t : ℝ,
        -(K.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
          Analysis.finiteSignedResolvent l t) :
    -(∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ).re ≤
      AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget χ l B := by
  have h := Analysis.finiteSignedPhaseNodeCheck_sound l hc
  exact
    neg_re_oscillatingZeroSum_le_prefix K hq hGRH hp hne hinv hx l h.1
      (Analysis.finiteSignedMangoldtWeight_nonneg_of_check l h.2) B hphase

end PseudoPrime.LLS.PaperStatements.MellinKernel

namespace PseudoPrime.LLS.PaperStatements

/-- Input: GRH, primitive conductor 3 <= m <= q, q >= 20000, x >= 2,
a successful rational node check and a global Gamma phase majorant.
Claim: the actual Gamma arithmetic sum obeys the certified prefix-plus-remainder bound.
Proof: use the node certificate to supply admissibility and common-weight positivity.
Role: connect finite coefficient certificates to witness-bound comparisons. -/
theorem gamma_primitive_sum_re_le_phase_prefix_of_nodeCheck {q m : ℕ} [NeZero m] (hq : 20000 ≤ q)
    (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) (l : List (ℚ × ℚ))
    (hc : Analysis.finiteSignedPhaseNodeCheck l = true) (B : Finset ℕ)
    (hphase :
      ∀ t : ℝ,
        -(gammaMellinKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
          Analysis.finiteSignedResolvent l t) :
    (∑' k : ℕ, gammaMellinKernel.summand χ x k).re ≤
      AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget χ l B +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  have h := Analysis.finiteSignedPhaseNodeCheck_sound l hc
  exact
    gamma_primitive_sum_re_le_phase_prefix hq hm hmq hGRH hp hne hinv hx l h.1
      (Analysis.finiteSignedMangoldtWeight_nonneg_of_check l h.2) B hphase

end PseudoPrime.LLS.PaperStatements
