/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.CompensatedPrimeRates
public import PseudoPrime.PseudoSquare.Bounds.ConductorSquareFactorJacobi

/-! # Negative Jacobi witnesses using exact conductor compensation -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Under GRH and x>=64, the compensated allowance at threshold
P>=2 and a negative comparison at 4n give an odd n-coprime negative Jacobi prime.
Insert proved unequal rates and compensated excesses into the coupled witness theorem.
No local-cost or untapered-budget assumptions remain in this statement. -/
theorem exists_prime_neg_one_of_compensated_rates {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 64 ≤ x) {P : ℕ}
    (hP : 2 ≤ P)
    (hsep :
      LLS.PaperStatements.oddEndpointTwoCostLimit (4 * n) x x 0 0 +
            LLS.PaperStatements.compensatedInputCost x P n -
          (LLS.PaperStatements.excludedReciprocalCoefficient x / x) * Real.log 2 <
        0) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p n ∧ jacobiSym n p = -1 := by
  have hx1 : 1 < x := by linarith only [hx]
  have ha := LLS.PaperStatements.explicitUntaperedPrimeRate_nonneg hx1 hP
  have hb := add_nonneg ha (LLS.PaperStatements.equalEndpointLevelCoefficient_pos hx1).le
  have hs := lt_of_le_of_lt (LLS.PaperStatements.compensatedComparison_le_input bridge hx1 P) hsep
  exact
    exists_prime_neg_one_of_conductor_square_rates bridge hGRH hx ha hb
      (LLS.PaperStatements.explicitUntaperedPrimeExceptions P)
      (LLS.PaperStatements.compensatedPrimeExcess x P)
      (fun p _ ↦ LLS.PaperStatements.compensatedPrimeExcess_nonneg x P p)
      (fun p hp hdiv ↦
        LLS.PaperStatements.untaperedPrimeCost_le_compensated_ramified hx1 hP
          (Nat.prime_of_mem_primeFactors hp)
          (hn.of_dvd_nat ((Nat.mem_primeFactors_of_ne_zero hn.pos.ne').mp hp).2) _ hdiv)
      (fun p hp hd ↦
        LLS.PaperStatements.untaperedPrimeCost_le_compensated_unramified hx1 hP
          (Nat.prime_of_mem_primeFactors hp)
          (hn.of_dvd_nat ((Nat.mem_primeFactors_of_ne_zero hn.pos.ne').mp hp).2) _ hd)
      hs

/-- Under the compensated prime-rate separation, the least negative
odd-prime Jacobi witness is at most x. Apply leastness to the constructed prime.
This exposes the local-hypothesis-free criterion to pointwise witness bounds. -/
theorem primeNegOneWitness_le_of_compensated_rates {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 64 ≤ x) {P : ℕ}
    (hP : 2 ≤ P)
    (hsep :
      LLS.PaperStatements.oddEndpointTwoCostLimit (4 * n) x x 0 0 +
            LLS.PaperStatements.compensatedInputCost x P n -
          (LLS.PaperStatements.excludedReciprocalCoefficient x / x) * Real.log 2 <
        0)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ x := by
  obtain ⟨p, hp, ho, hpx, _, hv⟩ := exists_prime_neg_one_of_compensated_rates bridge hGRH hx hP hsep
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hpx

/-- Under GRH, x>=64 and P>=2, the level-4B compensated comparison bounds
QNegOne(B) by x. Use level and allowance monotonicity, then construct each bridge
and apply the proved least-witness criterion. No finite input certificate is needed. -/
theorem QNegOne_le_of_compensated_rates {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 64 ≤ x) {P : ℕ}
    (hP : 2 ≤ P)
    (hsep :
      LLS.PaperStatements.oddEndpointTwoCostLimit (4 * B) x x 0 0 +
            LLS.PaperStatements.compensatedInputCost x P B -
          (LLS.PaperStatements.excludedReciprocalCoefficient x / x) * Real.log 2 <
        0) :
    (QNegOne B : ℝ) ≤ x := by
  have hx1 : 1 < x := by linarith only [hx]
  apply QNegOne_cast_le_of_forall (zero_lt_one.trans hx1).le
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  obtain ⟨bridge⟩ :=
    NumberTheory.exists_jacobiCharacterArithmeticData ha.odd.pos ha.odd ha.not_isSquare
  have hm :=
    LLS.PaperStatements.oddEndpointTwoCostLimit_mono_level (x := x) (Y := x) (c := 0) (D := 0)
      (Nat.mul_pos (by norm_num only : (0 : ℕ) < 4) ha.odd.pos) (Nat.mul_le_mul_left 4 ha.le) hx1.le
      hx
  have hc := LLS.PaperStatements.compensatedInputCost_mono ha.odd.pos ha.le hx1 hP
  have hs :
    LLS.PaperStatements.oddEndpointTwoCostLimit (4 * n) x x 0 0 +
          LLS.PaperStatements.compensatedInputCost x P n -
        (LLS.PaperStatements.excludedReciprocalCoefficient x / x) * Real.log 2 <
      0 := by
    linarith only [hm, hc, hsep]
  exact
    primeNegOneWitness_le_of_compensated_rates bridge hGRH hx hP hs
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)

end PseudoPrime.PseudoSquare
