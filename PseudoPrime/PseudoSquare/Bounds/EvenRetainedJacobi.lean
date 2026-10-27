/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.EvenRetainedPrimeRates
public import PseudoPrime.PseudoSquare.Bounds.ConductorSquareFactorJacobi

/-! # Negative Jacobi witnesses retaining local even-power cancellation -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Under GRH and x>=64, the even-retained prime-rate budget at threshold
P>=2 and a negative separation at 4d give an odd n-coprime negative Jacobi prime.
Insert proved common rates and even-retained excesses into the coupled witness theorem.
No local-cost or untapered-budget assumptions remain in this statement. -/
theorem exists_prime_neg_one_of_even_retained_budget {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 64 ≤ x) {P : ℕ}
    (hP : 2 ≤ P)
    (hsep :
      LLS.PaperStatements.oddEndpointTwoCostLimit (4 * bridge.squarefreePart) x x 0 0 +
            LLS.PaperStatements.evenRetainedInputBudget x P n -
          (LLS.PaperStatements.excludedReciprocalCoefficient x / x) * Real.log 2 <
        0) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p n ∧ jacobiSym n p = -1 := by
  have hx1 : 1 < x := by linarith only [hx]
  have ha := LLS.PaperStatements.explicitUntaperedPrimeRate_nonneg hx1 hP
  have hb := LLS.PaperStatements.conductorSquareBudget_le_even_retained bridge hx1 P
  exact
    exists_prime_neg_one_of_conductor_square_rates bridge hGRH hx ha ha
      (LLS.PaperStatements.explicitUntaperedPrimeExceptions P)
      (LLS.PaperStatements.evenRetainedPrimeExcess x P)
      (fun p _ ↦ LLS.PaperStatements.evenRetainedPrimeExcess_nonneg x P p)
      (fun p hp hdiv ↦
        LLS.PaperStatements.untaperedPrimeCost_le_even_retained_ramified hx1 hP
          (Nat.prime_of_mem_primeFactors hp)
          (hn.of_dvd_nat ((Nat.mem_primeFactors_of_ne_zero hn.pos.ne').mp hp).2) _ hdiv)
      (fun p hp hd ↦
        LLS.PaperStatements.untaperedPrimeCost_le_even_retained_unramified hx1 hP
          (Nat.prime_of_mem_primeFactors hp)
          (hn.of_dvd_nat ((Nat.mem_primeFactors_of_ne_zero hn.pos.ne').mp hp).2) _ hd)
      (by linarith only [hb, hsep])

/-- Under the even-retained prime-rate separation, the least negative
odd-prime Jacobi witness is at most x. Apply leastness to the constructed prime.
This exposes the local-hypothesis-free criterion to pointwise witness bounds. -/
theorem primeNegOneWitness_le_of_even_retained_budget {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 64 ≤ x) {P : ℕ}
    (hP : 2 ≤ P)
    (hsep :
      LLS.PaperStatements.oddEndpointTwoCostLimit (4 * bridge.squarefreePart) x x 0 0 +
            LLS.PaperStatements.evenRetainedInputBudget x P n -
          (LLS.PaperStatements.excludedReciprocalCoefficient x / x) * Real.log 2 <
        0)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ x := by
  obtain ⟨p, hp, ho, hpx, _, hv⟩ :=
    exists_prime_neg_one_of_even_retained_budget bridge hGRH hx hP hsep
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hpx

/-- Under GRH, x>=64 and P>=2, a negative even-retained separation at
4B bounds QNegOne(B) by x. For every admissible input construct its arithmetic
bridge, apply the proved untapered budget and use input monotonicity.
There is no finite input certificate or local cost premise. -/
theorem QNegOne_le_of_even_retained_budget {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 64 ≤ x) {P : ℕ}
    (hP : 2 ≤ P)
    (hsep :
      LLS.PaperStatements.oddEndpointTwoCostLimit (4 * B) x x 0 0 +
            LLS.PaperStatements.evenRetainedInputBudget x P B -
          (LLS.PaperStatements.excludedReciprocalCoefficient x / x) * Real.log 2 <
        0) :
    (QNegOne B : ℝ) ≤ x := by
  have hx1 : 1 < x := by linarith only [hx]
  apply QNegOne_le_of_finite_excluded_taper hGRH hx _ hsep
  intro n hn hodd
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  obtain ⟨bridge⟩ := NumberTheory.exists_jacobiCharacterArithmeticData hodd.pos hodd ha.not_isSquare
  exact
    (LLS.PaperStatements.untaperedBudget_le_even_retained bridge hx1 hP).trans
      (LLS.PaperStatements.evenRetainedInputBudget_mono hodd.pos ha.le hx1 hP)

end PseudoPrime.PseudoSquare
