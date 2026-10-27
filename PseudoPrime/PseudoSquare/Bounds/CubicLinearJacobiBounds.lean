/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.CubicSquareFactorLinearBounds
public import PseudoPrime.PseudoSquare.Bounds.CubicNegativeSupportBounds
public import PseudoPrime.PseudoSquare.Bounds.RefinedConductorRadicalWitnessBounds

/-! # Explicit logarithm-linear quadratic witness envelopes for fixed squarefree part -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- For n=s²d, the squared full square-factor radius is below the envelope
at G=log(4d), L=log n. Use E(s) at most L/2 and the generic real comparison.
No GRH is needed for this arithmetic-to-real envelope transfer. -/
theorem cubicSquareFactorRadius_sq_le_log_envelope {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) :
    (LLS.PaperStatements.cubicSquareFactorRadius (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ))
          (∑ p ∈ bridge.squareFactor.primeFactors, Real.log p)) ^
        2 ≤
      LLS.PaperStatements.cubicSquareFactorLinearEnvelope
        (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ)) (Real.log n) := by
  exact
    LLS.PaperStatements.cubicSquareFactorRadius_sq_le_linear_envelope (Real.log_natCast_nonneg _)
      (Finset.sum_nonneg fun p _ ↦ Real.log_natCast_nonneg p)
      (squareFactor_prime_log_sum_le_half_log bridge)

/-- Under GRH for an odd nonsquare n=s²d, there is an odd coprime negative prime
below the explicit envelope at G=log(4d), L=log n. Combine the actual prime from
the cubic square-factor theorem with the arithmetic envelope comparison. -/
theorem exists_prime_neg_one_le_cubic_linear_envelope {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        Nat.Coprime p n ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤
          LLS.PaperStatements.cubicSquareFactorLinearEnvelope
            (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ)) (Real.log n) := by
  obtain ⟨p, hp, ho, hc, hj, hb⟩ := exists_prime_neg_one_le_cubic_square_factor bridge hGRH
  exact ⟨p, hp, ho, hc, hj, hb.trans (cubicSquareFactorRadius_sq_le_log_envelope bridge)⟩

/-- Under GRH, the least negative odd-prime witness is bounded by the explicit
linear envelope with G=log(4d). Compose the proved square-factor witness bound
with the arithmetic-to-real comparison; no conductor threshold is needed. -/
theorem primeNegOneWitness_le_cubic_linear_envelope {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      LLS.PaperStatements.cubicSquareFactorLinearEnvelope
        (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ)) (Real.log n) := by
  exact
    (primeNegOneWitness_le_cubic_square_factor bridge hGRH hw).trans
      (cubicSquareFactorRadius_sq_le_log_envelope bridge)

/-- The least non-one odd-prime witness has the same linear envelope under GRH.
Compose its square-factor bound with the common envelope comparison. This
retains the distinction between the two least-witness definitions. -/
theorem primeNeOneWitness_le_cubic_linear_envelope {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤
      LLS.PaperStatements.cubicSquareFactorLinearEnvelope
        (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ)) (Real.log n) := by
  exact
    (primeNeOneWitness_le_cubic_square_factor bridge hGRH hw).trans
      (cubicSquareFactorRadius_sq_le_log_envelope bridge)

/-- Under GRH for n=s²d, the least negative witness is at most (4/3+delta)log n
when the two explicit conductor-dependent cutoff inequalities hold. Apply the
linear envelope and its quantified absorption theorem. For fixed d this gives
an effective asymptotic coefficient 4/3 without finite-input certificates. -/
theorem primeNegOneWitness_le_cubic_linear_coefficient {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) {δ : ℝ} (hδ : 0 < δ)
    (hc₁ :
      8 * ((10 / 13 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 35) ^ 2 ≤
        δ * Real.log n)
    (hc₂ :
      64 * ((10 / 13 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 35) ^ 2 ≤
        δ ^ 2 * Real.log n) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (4 / 3 + δ) * Real.log n := by
  apply (primeNegOneWitness_le_cubic_linear_envelope bridge hGRH hw).trans
  exact
    LLS.PaperStatements.cubicSquareFactorLinearEnvelope_le_coefficient (Real.log_natCast_nonneg _)
      (Real.log_natCast_nonneg n) hδ hc₁ hc₂

end PseudoPrime.PseudoSquare
