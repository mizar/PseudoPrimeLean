/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ParameterizedCubicSquareFactorRadius
public import PseudoPrime.PseudoSquare.Bounds.TightCubicNegativeSupportBounds

/-! # Negative-support cubic bounds with constant 2434/75 -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Under GRH, conductor envelope G and sensitive cost at most G+2E
give an odd coprime negative Jacobi witness below the 2434/75 radius squared.
Apply the existing primitive witness theorem and the parameterized absorption
comparison. No finite input certificates are required. -/
theorem exists_prime_neg_one_le_cubic2434_square_factor_of_envelopes {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {G E : ℝ}
    (hlog : Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ G) (hE : 0 ≤ E)
    (hcost :
      AnalyticNumberTheory.Arithmetic.characterExclusionCost
          (NumberTheory.primitiveQuadraticCharacter n hn) (2 * n) ≤
        G + 2 * E) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        Nat.Coprime p n ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤ (LLS.PaperStatements.cubicSquareFactorRadius2434 G E) ^ 2 := by
  have hG :=
    (Real.log_natCast_nonneg (NumberTheory.complexQuadraticCharacter n hn).conductor).trans hlog
  obtain ⟨p, hp, ho, hc, hj, hb⟩ :=
    exists_prime_neg_one_le_tight_cubic_sensitive_radius (hns := hns) hGRH hlog hcost
  have hr := LLS.PaperStatements.tightCubicExclusionRadius_le_square_factor2434 hG hE
  have hcost0 : 0 ≤ G + 2 * E := by linarith only [hG, hE]
  have hn := (LLS.PaperStatements.tightCubicExclusionRadius_data hG hcost0).1
  have hs := pow_le_pow_left₀ ((by norm_num only : (0 : ℝ) ≤ 63 / 2).trans hn) hr 2
  exact ⟨p, hp, ho, hc, hj, hb.trans hs⟩

/-- For the canonical decomposition n=d*s², GRH supplies an odd negative
prime below the 2434/75 square-factor radius. Its only square-factor cost is
the logarithm sum over primes where (d/p)=-1. Conductor and cost estimates
are discharged from the existing arithmetic decomposition. -/
theorem exists_prime_neg_one_le_cubic2434_negative_support {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        Nat.Coprime p n ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤
          (LLS.PaperStatements.cubicSquareFactorRadius2434
              (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ))
              (negativeSquareFactorCost bridge.squarefreePart bridge.squareFactor)) ^
            2 := by
  let : NeZero (4 * n) := ⟨mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hdvd : bridge.squarefreePart ∣ n :=
    ⟨bridge.squareFactor ^ 2, by simpa only [mul_comm] using bridge.squarefreePart_sq_mul.symm⟩
  have hf :=
    Nat.le_of_dvd (Nat.mul_pos (by decide : 0 < 4) bridge.squarefreePart_pos)
      (NumberTheory.complexQuadraticCharacter_conductor_dvd_four_mul_squarefreePart bridge hdvd)
  have hlog :=
    Real.log_le_log
      (Nat.cast_pos.mpr
        (Nat.pos_of_ne_zero (NumberTheory.complexQuadraticCharacter n hn).conductor_ne_zero))
      (Nat.cast_le.mpr hf)
  exact
    exists_prime_neg_one_le_cubic2434_square_factor_of_envelopes (hns := hns) hGRH hlog
      (negativeSquareFactorCost_nonneg _ _)
      (primitiveQuadraticExclusionCost_le_negative_square_factor bridge)

/-- Under GRH, leastness transfers the negative-support cubic radius to the
least negative odd-prime witness of n=s²d. The support cost is the explicit
Jacobi filter on the square factor, with no remaining analytic cost hypothesis. -/
theorem primeNegOneWitness_le_cubic2434_negative_support {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      (LLS.PaperStatements.cubicSquareFactorRadius2434
          (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ))
          (negativeSquareFactorCost bridge.squarefreePart bridge.squareFactor)) ^
        2 := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ := exists_prime_neg_one_le_cubic2434_negative_support bridge hGRH
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hj⟩)).trans hb

/-- The same negative-support radius bounds the least non-one odd-prime
witness under GRH. Use the constructed negative value as a non-one value;
this does not identify the two least witnesses. -/
theorem primeNeOneWitness_le_cubic2434_negative_support {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤
      (LLS.PaperStatements.cubicSquareFactorRadius2434
          (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ))
          (negativeSquareFactorCost bridge.squarefreePart bridge.squareFactor)) ^
        2 := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ := exists_prime_neg_one_le_cubic2434_negative_support bridge hGRH
  have hne : jacobiSym n p ≠ 1 := by
    rw [hj]; norm_num only
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hne⟩)).trans hb

end PseudoPrime.PseudoSquare
