/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaPairedTailConductorBounds
public import PseudoPrime.AnalyticNumberTheory.Gamma.EvenResolventCertificate

/-! # Arithmetic witness budget with a certified fixed Gamma correction -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The refined arithmetic budget with its even Gamma correction replaced
by the proved upper bound -159/100. The remaining Euler, finite prefix,
conductor, local dual, pole and left-contour terms retain their original signs.
This is the scalar budget to certify on the logarithmic scale interval. -/
noncomputable def gammaCertifiedArithmeticBudget (L b : ℝ) : ℝ :=
  let x := Analysis.gammaRefinedScale L
  (-159 / 100 : ℝ) + (∑' m : ℕ, Analysis.gammaResolventMangoldtWeight m) -
      2 * (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m) +
    (11783423 / 25000000 : ℝ) * (L + Real.log 4) +
    (3 / 4 : ℝ) +
    gammaRefinedSignedDualBudget L +
    ((7 / 6 : ℝ) * (L + Real.log 4) + 4) / Real.sqrt x +
    x ^ (-9 / 16 : ℝ) * ((3 / 2) * (L + Real.log 4 + 28) + 1)

/-- At every scale and prefix, the original refined budget is at most
the certified scalar budget. Use the signed Gamma correction certificate;
all other terms coincide, so no scale or arithmetic assumptions are needed. -/
theorem gammaRefinedArithmeticBudget_le_certified (L b : ℝ) :
    gammaRefinedArithmeticBudget L b ≤ gammaCertifiedArithmeticBudget L b := by
  have h := AnalyticNumberTheory.Gamma.gammaResolvent_even_correction_le
  dsimp only [gammaRefinedArithmeticBudget, gammaCertifiedArithmeticBudget]
  linarith only [h]

/-- A strict certified budget gap, including selected square gains, forces
an odd-prime negative Jacobi witness for an odd nonsquare n at least 10^100
under GRH. The fixed Gamma correction is already proved rather than an input
to the numerical certificate. Transfer the upper bound to the existing witness theorem. -/
theorem exists_odd_prime_negative_of_certified_square_gain_gap {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlarge : 10 ^ 100 ≤ n) {b : ℝ}
    (hb : 1 ≤ b) (hbX : b ≤ (99 / 40 : ℝ) * Analysis.gammaRefinedScale (Real.log n)) (C : Finset ℕ)
    (hC : ∀ m ∈ C, IsSquare m) (hBC : Disjoint (Finset.Ioc 0 ⌊b⌋₊) C)
    (hgap :
      gammaCertifiedArithmeticBudget (Real.log n) b <
        2 *
              (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum
                  (Analysis.gammaRefinedScale (Real.log n)) /
                Real.sqrt (Analysis.gammaRefinedScale (Real.log n))) -
            (∑' k : ℕ,
                PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1)
                  (Analysis.gammaRefinedScale (Real.log n)) k).re +
          (∑ m ∈ C, Analysis.gammaResolventMangoldtWeight m)) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * Analysis.gammaRefinedScale (Real.log n) ∧ jacobiSym n p = -1 := by
  exact
    exists_odd_prime_negative_of_refined_square_gain_gap bridge hGRH hlarge hb hbX C hC hBC
      ((gammaRefinedArithmeticBudget_le_certified _ _).trans_lt hgap)

end PseudoPrime.LLS
