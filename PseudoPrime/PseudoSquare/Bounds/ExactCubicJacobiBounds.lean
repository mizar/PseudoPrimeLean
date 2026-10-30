/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Bounds.ExactQuadraticExclusion
public import PseudoPrime.LLS.TightCubicRadiusOrder

/-! # Cubic Jacobi bounds with exact conductors and exact exclusion costs -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- The squared tight cubic radius at the actual primitive conductor logarithm
and actual exclusion cost at 2n. The canonical bridge records the input domain,
but neither budget is replaced by log(4d). Exact residue formulas are proved below. -/
noncomputable def cubicExactConductorBound {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (_b : NumberTheory.JacobiCharacterArithmeticData n hn hns) : ℝ :=
  (LLS.PaperStatements.tightCubicExclusionRadius
      (Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor)
      (AnalyticNumberTheory.Arithmetic.characterExclusionCost
        (NumberTheory.primitiveQuadraticCharacter n hn) (2 * n))) ^
    2

/-- The actual primitive conductor logarithm is at most log(4d).
Use conductor divisibility, positivity and logarithm monotonicity.
This checks the conductor side of comparison with the old uniform radius. -/
private theorem exact_conductor_le_level {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (b : NumberTheory.JacobiCharacterArithmeticData n hn hns) :
    Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor ≤
      Real.log (4 * b.squarefreePart : ℕ) := by
  let : NeZero (4 * n) := ⟨mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hdvd : b.squarefreePart ∣ n :=
    ⟨b.squareFactor ^ 2, by simpa only [mul_comm] using b.squarefreePart_sq_mul.symm⟩
  exact
    Real.log_le_log
      (Nat.cast_pos.mpr
        (Nat.pos_of_ne_zero (NumberTheory.complexQuadraticCharacter n hn).conductor_ne_zero))
      (Nat.cast_le.mpr
        (Nat.le_of_dvd (Nat.mul_pos (by norm_num only) b.squarefreePart_pos)
          (NumberTheory.complexQuadraticCharacter_conductor_dvd_four_mul_squarefreePart b hdvd)))

/-- At least one exact quadratic budget is strictly below the former uniform budget.
For d=1 modulo four the conductor drops from 4d to d; for d=3 modulo four,
the cost at two is log(2), strictly below the old twice-log allowance. -/
private theorem exact_quadratic_budget_saving {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (b : NumberTheory.JacobiCharacterArithmeticData n hn hns) :
    Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor <
        Real.log (4 * b.squarefreePart : ℕ) ∨
      AnalyticNumberTheory.Arithmetic.characterExclusionCost
          (NumberTheory.primitiveQuadraticCharacter n hn) (2 * n) <
        Real.log (4 * b.squarefreePart : ℕ) +
          2 * negativeSquareFactorCost b.squarefreePart b.squareFactor := by
  let : NeZero (4 * n) := ⟨mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp b.squarefreePart_odd) with h1 | h3
  · left
    have hdvd : b.squarefreePart ∣ n :=
      ⟨b.squareFactor ^ 2, by simpa only [mul_comm] using b.squarefreePart_sq_mul.symm⟩
    rw [NumberTheory.complexQuadraticCharacter_conductor_eq_squarefreePart_of_mod_four_eq_one b hdvd
        h1]
    apply Real.log_lt_log (Nat.cast_pos.mpr b.squarefreePart_pos)
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    have hdR : (0 : ℝ) < b.squarefreePart := Nat.cast_pos.mpr b.squarefreePart_pos
    linarith only [hdR]
  · right
    have hl : Real.log (4 * b.squarefreePart : ℕ) = 2 * Real.log 2 + Real.log b.squarefreePart := by
      rw [Nat.cast_mul, Nat.cast_ofNat,
        Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0)
          (Nat.cast_ne_zero.mpr b.squarefreePart_pos.ne')]
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
    rw [primitiveQuadratic_exclusion_cost_exact b, NumberTheory.primitiveQuadratic_two_zero b h3,
      Complex.zero_re, sub_zero, one_mul, hl]
    linarith only [Real.log_pos (by norm_num only : (1 : ℝ) < 2)]

/-- For every canonical odd nonsquare input, the exact squared cubic radius is
strictly below the previous 2434/75 negative-support squared radius. Compare exact
nonnegative budgets, use the strict conductor-or-cost saving, then apply the
existing absorption theorem and square the positive radii. -/
theorem cubicExactConductorBound_lt_uniform {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (b : NumberTheory.JacobiCharacterArithmeticData n hn hns) :
    cubicExactConductorBound b <
      (LLS.PaperStatements.cubicSquareFactorRadius2434 (Real.log (4 * b.squarefreePart : ℕ))
          (negativeSquareFactorCost b.squarefreePart b.squareFactor)) ^
        2 := by
  have hG := Real.log_natCast_nonneg (NumberTheory.complexQuadraticCharacter n hn).conductor
  have hE :=
    AnalyticNumberTheory.Arithmetic.characterExclusionCost_nonneg
      (NumberTheory.primitiveQuadraticCharacter n hn) (2 * n)
  have hr :=
    LLS.PaperStatements.tightCubicRadius_strict hG hE (exact_conductor_le_level b)
      (primitiveQuadraticExclusionCost_le_negative_square_factor b)
      (exact_quadratic_budget_saving b)
  have ha :=
    LLS.PaperStatements.tightCubicExclusionRadius_le_square_factor2434
      (Real.log_natCast_nonneg (4 * b.squarefreePart))
      (negativeSquareFactorCost_nonneg b.squarefreePart b.squareFactor)
  have hzero := (LLS.PaperStatements.tightCubicExclusionRadius_data hG hE).1
  have ht := hr.trans_le ha
  have hp :
    (0 : ℝ) ≤
      LLS.PaperStatements.tightCubicExclusionRadius
        (Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor)
        (AnalyticNumberTheory.Arithmetic.characterExclusionCost
          (NumberTheory.primitiveQuadraticCharacter n hn) (2 * n)) := by
    linarith only [hzero]
  exact (sq_lt_sq₀ hp (hp.trans ht.le)).mpr ht

/-- The exact squared cubic bound is at least 27. The tight radius itself is
at least 63/2 because both actual budgets are nonnegative.
This absorbs exceptional Selfridge stopping magnitudes. -/
theorem cubicExactConductorBound_ge27 {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (b : NumberTheory.JacobiCharacterArithmeticData n hn hns) :
    27 ≤ cubicExactConductorBound b := by
  have h :=
    (LLS.PaperStatements.tightCubicExclusionRadius_data
        (Real.log_natCast_nonneg (NumberTheory.complexQuadraticCharacter n hn).conductor)
        (AnalyticNumberTheory.Arithmetic.characterExclusionCost_nonneg
          (NumberTheory.primitiveQuadraticCharacter n hn) (2 * n))).1
  dsimp only [cubicExactConductorBound]
  nlinarith only [h]

/-- Under GRH, an actual odd coprime negative Jacobi prime obeys the exact bound.
Apply the established tight sensitive-radius extraction with both exact budgets.
There is no remaining conductor-envelope or exclusion-cost hypothesis. -/
theorem exists_prime_neg_one_le_cubic_exact {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (b : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧ Nat.Coprime p n ∧ jacobiSym n p = -1 ∧ (p : ℝ) ≤ cubicExactConductorBound b := by
  exact exists_prime_neg_one_le_tight_cubic_sensitive_radius (hns := hns) hg le_rfl le_rfl

/-- Under GRH, the least negative odd-prime witness obeys the exact conductor bound.
Minimize the actual odd-prime witness supplied above and transfer its real bound.
The explicit nonemptiness proof preserves the existing witness API. -/
theorem primeNegOneWitness_le_cubic_exact {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (b : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ cubicExactConductorBound b := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ := exists_prime_neg_one_le_cubic_exact b hg
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hj⟩)).trans hb

/-- Under GRH, the least non-one odd-prime witness obeys the same exact bound.
A negative Jacobi value is non-one, so minimize its actual witness set.
This does not identify the negative and non-one least witnesses. -/
theorem primeNeOneWitness_le_cubic_exact {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (b : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ cubicExactConductorBound b := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ := exists_prime_neg_one_le_cubic_exact b hg
  have hne : jacobiSym n p ≠ 1 := by
    rw [hj]; norm_num only
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hne⟩)).trans hb

/-- In the stated residue class modulo eight, the exact cubic bound has the displayed
conductor and prime-two cost. Substitute the exact exclusion identity before the
conductor identity to avoid dependent casts. The five-mod-eight branch retains
its twice-log(2) cost even though its conductor is d. -/
theorem cubicExactConductorBound_mod_one {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (b : NumberTheory.JacobiCharacterArithmeticData n hn hns) (h8 : b.squarefreePart % 8 = 1) :
    cubicExactConductorBound b =
      (LLS.PaperStatements.tightCubicExclusionRadius (Real.log b.squarefreePart)
          (Real.log b.squarefreePart +
            2 * negativeSquareFactorCost b.squarefreePart b.squareFactor)) ^
        2 := by
  unfold cubicExactConductorBound
  rw [primitiveQuadratic_exclusion_mod_one b h8, (NumberTheory.quadratic_mod_eight_one_data b h8).1]
  rw [add_zero]

/-- In the stated residue class modulo eight, the exact cubic bound has the displayed
conductor and prime-two cost. Substitute the exact exclusion identity before the
conductor identity to avoid dependent casts. The five-mod-eight branch retains
its twice-log(2) cost even though its conductor is d. -/
theorem cubicExactConductorBound_mod_five {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (b : NumberTheory.JacobiCharacterArithmeticData n hn hns) (h8 : b.squarefreePart % 8 = 5) :
    cubicExactConductorBound b =
      (LLS.PaperStatements.tightCubicExclusionRadius (Real.log b.squarefreePart)
          (Real.log b.squarefreePart + 2 * Real.log 2 +
            2 * negativeSquareFactorCost b.squarefreePart b.squareFactor)) ^
        2 := by
  unfold cubicExactConductorBound
  rw [primitiveQuadratic_exclusion_mod_five b h8,
    (NumberTheory.quadratic_mod_eight_five_data b h8).1]

/-- In the stated residue class modulo eight, the exact cubic bound has the displayed
conductor and prime-two cost. Substitute the exact exclusion identity before the
conductor identity to avoid dependent casts. The five-mod-eight branch retains
its twice-log(2) cost even though its conductor is d. -/
theorem cubicExactConductorBound_mod_three_seven {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (b : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (h8 : b.squarefreePart % 8 = 3 ∨ b.squarefreePart % 8 = 7) :
    cubicExactConductorBound b =
      (LLS.PaperStatements.tightCubicExclusionRadius (Real.log (4 * b.squarefreePart : ℕ))
          (Real.log b.squarefreePart + Real.log 2 +
            2 * negativeSquareFactorCost b.squarefreePart b.squareFactor)) ^
        2 := by
  unfold cubicExactConductorBound
  rw [primitiveQuadratic_exclusion_mod_three_seven b h8,
    (NumberTheory.quadratic_mod_eight_three_seven b h8).1]

end PseudoPrime.PseudoSquare
