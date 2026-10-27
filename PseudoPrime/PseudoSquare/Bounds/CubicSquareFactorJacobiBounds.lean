/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterExclusionProducts
public import PseudoPrime.PseudoSquare.Bounds.CubicSensitiveJacobiBounds
public import PseudoPrime.LLS.CubicSquareFactorBounds

/-! # Cubic negative witnesses with squarefree and square-factor costs separated -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- For the standard odd nonsquare decomposition, the squarefree part divides
the quadratic conductor. Identify the conductor with the positive fundamental
discriminant, which is d or 4d. This certifies ramification at every prime of d. -/
theorem squarefreePart_dvd_quadratic_conductor {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) :
    bridge.squarefreePart ∣ (NumberTheory.complexQuadraticCharacter n hn).conductor := by
  have hdvd : bridge.squarefreePart ∣ n :=
    ⟨bridge.squareFactor ^ 2, by simpa only [mul_comm] using bridge.squarefreePart_sq_mul.symm⟩
  rw [NumberTheory.complexQuadraticCharacter_conductor_eq_discriminant bridge hdvd,
    bridge.discriminant_eq]
  unfold NumberTheory.positiveFundamentalDiscriminant
  split
  · exact dvd_refl _
  · exact dvd_mul_left _ 4

/-- Every prime in the squarefree part has zero value under the primitive
quadratic character. Its divisibility into the conductor makes the prime a
nonunit. This remains valid when that prime also divides the square factor. -/
theorem primitiveQuadraticCharacter_zero_on_squarefreePart {n p : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hp : p ∈ bridge.squarefreePart.primeFactors) :
    NumberTheory.primitiveQuadraticCharacter n hn p = 0 := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpf := (Nat.dvd_of_mem_primeFactors hp).trans (squarefreePart_dvd_quadratic_conductor bridge)
  have hnc : ¬Nat.Coprime p (NumberTheory.complexQuadraticCharacter n hn).conductor := fun hc ↦
    (hprime.coprime_iff_not_dvd.mp hc) hpf
  simpa only [Int.cast_natCast] using
    (DirichletCharacter.apply_eq_zero_iff (NumberTheory.primitiveQuadraticCharacter n hn)
          (p : ℤ)).mpr
      (by simpa only [Nat.isCoprime_iff_coprime] using hnc)

open AnalyticNumberTheory.Arithmetic in
/-- For the canonical odd nonsquare decomposition n=s²d, the primitive exclusion
cost at 2n is at most log(4d)+2sum over prime divisors of s of log p. Use the
ramified-support product estimate and the exact decomposition. This removes
the arithmetic cost envelope from the square-factor witness theorem. -/
theorem primitiveQuadraticExclusionCost_le_square_factor {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) :
    characterExclusionCost (NumberTheory.primitiveQuadraticCharacter n hn) (2 * n) ≤
      Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) +
        2 * ∑ p ∈ bridge.squareFactor.primeFactors, Real.log p := by
  have hc :=
    characterExclusionCost_square_factor_le (NumberTheory.primitiveQuadraticCharacter n hn)
      bridge.squareFactor_odd.pos.ne' bridge.squarefreePart_pos.ne'
      (fun p hp ↦ primitiveQuadraticCharacter_zero_on_squarefreePart bridge hp)
  rw [bridge.squarefreePart_sq_mul] at hc
  exact hc

/-- Under GRH for an odd nonsquare n=s²d, an odd coprime negative prime lies
below (B+sqrt(B²+(8/3)E(s)))², B=(10/13)log(4d)+35. Use ramification to
bound the primitive exclusion cost, then absorb its conductor-linear term.
This closes the square-factor version without an external cost hypothesis. -/
theorem exists_prime_neg_one_le_cubic_square_factor {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        Nat.Coprime p n ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤
          (LLS.PaperStatements.cubicSquareFactorRadius
              (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ))
              (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r)) ^
            2 := by
  let : NeZero (4 * n) := ⟨mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hdvd : bridge.squarefreePart ∣ n :=
    ⟨bridge.squareFactor ^ 2, by simpa only [mul_comm] using bridge.squarefreePart_sq_mul.symm⟩
  have hf :
    (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ 4 * bridge.squarefreePart := by
    rw [NumberTheory.complexQuadraticCharacter_conductor_eq_discriminant bridge hdvd]
    exact bridge.discriminant_le_four_mul_squarefreePart
  have hlog :=
    Real.log_le_log
      (Nat.cast_pos.mpr
        (Nat.pos_of_ne_zero (NumberTheory.complexQuadraticCharacter n hn).conductor_ne_zero))
      (Nat.cast_le.mpr hf)
  have hG := Real.log_natCast_nonneg (4 * bridge.squarefreePart)
  have hE : 0 ≤ ∑ p ∈ bridge.squareFactor.primeFactors, Real.log (p : ℝ) :=
    Finset.sum_nonneg fun p _ ↦ Real.log_natCast_nonneg p
  obtain ⟨p, hp, ho, hc, hj, hb⟩ :=
    exists_prime_neg_one_le_cubic_sensitive_radius (hns := hns) hGRH hlog
      (primitiveQuadraticExclusionCost_le_square_factor bridge)
  have hr := LLS.PaperStatements.cubicExclusionRadius_le_square_factor hG hE
  have hcost0 :
    0 ≤
      Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) +
        2 * ∑ r ∈ bridge.squareFactor.primeFactors, Real.log r := by
    linarith only [hG, hE]
  have hn := (LLS.PaperStatements.cubicExclusionRadius_data hG hcost0).1
  have hs := pow_le_pow_left₀ ((by norm_num only : (0 : ℝ) ≤ 34).trans hn) hr 2
  exact ⟨p, hp, ho, hc, hj, hb.trans hs⟩

/-- For the standard decomposition and GRH, leastness gives the new cubic
square-factor bound for the least negative odd-prime witness. No additional
conductor or exclusion-cost hypotheses remain. -/
theorem primeNegOneWitness_le_cubic_square_factor {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      (LLS.PaperStatements.cubicSquareFactorRadius (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ))
          (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r)) ^
        2 := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ := exists_prime_neg_one_le_cubic_square_factor bridge hGRH
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hj⟩)).trans hb

/-- The least non-one odd-prime witness obeys the same cubic square-factor
bound under GRH. A negative Jacobi value is different from one; use this
constructed witness without identifying the two least-witness functions. -/
theorem primeNeOneWitness_le_cubic_square_factor {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤
      (LLS.PaperStatements.cubicSquareFactorRadius (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ))
          (∑ r ∈ bridge.squareFactor.primeFactors, Real.log r)) ^
        2 := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ := exists_prime_neg_one_le_cubic_square_factor bridge hGRH
  have hne : jacobiSym n p ≠ 1 := by
    rw [hj]; norm_num only
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hne⟩)).trans hb

/-- Under GRH, a positive target X bounds the least negative odd-prime witness
if 2B sqrt(X)+(8/3)E(s) is at most X. Apply the generic quadratic radius
criterion and leastness. This couples conductor and square-factor costs and
can be specialized to logarithmic powers without further analytic assumptions. -/
theorem primeNegOneWitness_le_of_cubic_square_factor_target {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) {X : ℝ} (hX : 0 < X)
    (hquad :
      2 * ((10 / 13 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 35) * Real.sqrt X +
          (8 / 3 : ℝ) * (∑ p ∈ bridge.squareFactor.primeFactors, Real.log p) ≤
        X) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ X := by
  have hG := Real.log_natCast_nonneg (4 * bridge.squarefreePart)
  have hE : 0 ≤ ∑ p ∈ bridge.squareFactor.primeFactors, Real.log (p : ℝ) :=
    Finset.sum_nonneg fun p _ ↦ Real.log_natCast_nonneg p
  have hq :
    2 * ((10 / 13 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 35) * Real.sqrt X +
        (8 / 3 : ℝ) * (∑ p ∈ bridge.squareFactor.primeFactors, Real.log p) ≤
      (Real.sqrt X) ^ 2 := by
    rw [Real.sq_sqrt hX.le]
    exact hquad
  have hr :=
    LLS.PaperStatements.cubicSquareFactorRadius_le_of_quadratic hG hE (Real.sqrt_pos.mpr hX) hq
  have hn := (LLS.PaperStatements.cubicSquareFactorRadius_data hG hE).1
  have hs := pow_le_pow_left₀ ((by norm_num only : (0 : ℝ) ≤ 70).trans hn) hr 2
  exact
    (primeNegOneWitness_le_cubic_square_factor bridge hGRH hw).trans
      (hs.trans_eq (Real.sq_sqrt hX.le))

open AnalyticNumberTheory.Arithmetic in
/-- Under GRH, arbitrary nonnegative conductor and square-factor cost envelopes
with E_chi(2n) at most G+2E give an odd coprime negative prime below the absorbed
cubic radius. This generic wrapper permits support-specific arithmetic estimates
without repeating the analytic extraction and radius absorption. -/
theorem exists_prime_neg_one_le_cubic_square_factor_of_envelopes {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {G E : ℝ}
    (hlog : Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ G) (hE : 0 ≤ E)
    (hcost :
      characterExclusionCost (NumberTheory.primitiveQuadraticCharacter n hn) (2 * n) ≤ G + 2 * E) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        Nat.Coprime p n ∧
        jacobiSym n p = -1 ∧ (p : ℝ) ≤ (LLS.PaperStatements.cubicSquareFactorRadius G E) ^ 2 := by
  have hG :=
    (Real.log_natCast_nonneg (NumberTheory.complexQuadraticCharacter n hn).conductor).trans hlog
  obtain ⟨p, hp, ho, hc, hj, hb⟩ :=
    exists_prime_neg_one_le_cubic_sensitive_radius (hns := hns) hGRH hlog hcost
  have hr := LLS.PaperStatements.cubicExclusionRadius_le_square_factor hG hE
  have hcost0 : 0 ≤ G + 2 * E := by linarith only [hG, hE]
  have hn := (LLS.PaperStatements.cubicExclusionRadius_data hG hcost0).1
  have hs := pow_le_pow_left₀ ((by norm_num only : (0 : ℝ) ≤ 34).trans hn) hr 2
  exact ⟨p, hp, ho, hc, hj, hb.trans hs⟩

end PseudoPrime.PseudoSquare
