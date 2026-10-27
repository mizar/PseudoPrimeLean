/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ConductorSquareFactorCost
public import PseudoPrime.PseudoSquare.Bounds.FiniteExcludedTaperJacobi

/-! # Negative Jacobi witnesses with coupled conductor and square-factor costs -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

open AnalyticNumberTheory.Arithmetic in
/-- Under GRH and local nonnegative ramified/unramified cost rates, a negative
coupled separation at level 4d yields an odd n-coprime Jacobi-minus-one prime
through x. Keep the squarefree part in the conductor level and in the cost
bound, then retain the finite log-two taper saving. No input enumeration is used. -/
theorem exists_prime_neg_one_of_conductor_square_rates {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x a b : ℝ} (hx : 64 ≤ x)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (T : Finset ℕ) (e : ℕ → ℝ) (he : ∀ p ∈ T, 0 ≤ e p)
    (hR :
      ∀ p ∈ n.primeFactors,
        p ∣ (NumberTheory.complexQuadraticCharacter n hn).conductor →
          quadraticExcludedPrimeCost (NumberTheory.complexQuadraticCharacter n hn).conductor x
              (LLS.PaperStatements.untaperedExcludedEndpointWeight x) p ≤
            a * Real.log p + if p ∈ T then e p else 0)
    (hE :
      ∀ p ∈ n.primeFactors,
        ¬p ∣ (NumberTheory.complexQuadraticCharacter n hn).conductor →
          quadraticExcludedPrimeCost (NumberTheory.complexQuadraticCharacter n hn).conductor x
              (LLS.PaperStatements.untaperedExcludedEndpointWeight x) p ≤
            2 * b * Real.log p + if p ∈ T then e p else 0)
    (hsep :
      LLS.PaperStatements.oddEndpointTwoCostLimit (4 * bridge.squarefreePart) x x 0 0 +
            LLS.PaperStatements.conductorSquareUntaperedBudget bridge x a b T e -
          (LLS.PaperStatements.excludedReciprocalCoefficient x / x) * Real.log 2 <
        0) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p n ∧ jacobiSym n p = -1 := by
  let _ : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  let χ := NumberTheory.primitiveQuadraticCharacter n hn
  let _ : NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    ⟨(NumberTheory.complexQuadraticCharacter n hn).conductor_ne_zero⟩
  have hp : χ.IsPrimitive :=
    (NumberTheory.complexQuadraticCharacter n hn).primitiveCharacter_isPrimitive
  have hquad : χ.IsQuadratic :=
    NumberTheory.isQuadratic_primitiveCharacter (NumberTheory.complexQuadraticCharacter n hn)
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn)
  have hne : χ ≠ 1 := NumberTheory.primitiveQuadraticCharacter_ne_one_of_not_square n hn hns
  have hq : 2 ≤ (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    (Nat.two_le_iff _).mpr ⟨NeZero.ne _, fun hf ↦ hne (DirichletCharacter.level_one' χ hf)⟩
  have hdvd : bridge.squarefreePart ∣ n :=
    ⟨bridge.squareFactor ^ 2, by simpa only [Nat.mul_comm] using bridge.squarefreePart_sq_mul.symm⟩
  have hqle :
    (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ 4 * bridge.squarefreePart := by
    rw [NumberTheory.complexQuadraticCharacter_conductor_eq_discriminant bridge hdvd]
    exact bridge.discriminant_le_four_mul_squarefreePart
  have hU :=
    LLS.PaperStatements.untaperedBudget_le_conductor_square_rates bridge
      (by linarith only [hx] : 0 ≤ x) ha hb T e he hR hE
  have hx1 : 1 < x := by linarith only [hx]
  have hm :=
    LLS.PaperStatements.oddEndpointTwoCostLimit_mono_level (x := x) (Y := x) (c := 0) (D := 0)
      (Nat.pos_of_ne_zero (NeZero.ne _)) hqle hx1.le hx
  have hs :
    LLS.PaperStatements.oddEndpointTwoCostLimit
            (NumberTheory.complexQuadraticCharacter n hn).conductor x x 0 0 +
          LLS.PaperStatements.conductorSquareUntaperedBudget bridge x a b T e -
        (LLS.PaperStatements.excludedReciprocalCoefficient x / x) * Real.log 2 <
      0 := by
    linarith only [hm, hsep]
  obtain ⟨p, hprime, hodd, hpx, hpc, hv⟩ :=
    LLS.PaperStatements.exists_prime_neg_one_of_finite_excluded_taper hq
      (NumberTheory.complexQuadraticCharacter n hn).conductor_dvd_level
      (show 2 ∣ 4 * n from ⟨2 * n, by ring⟩) hGRH hp hne hquad hx hU hs
  have hcp : Nat.Coprime p n := hpc.of_dvd_right (show n ∣ 4 * n from ⟨4, by ring⟩)
  have ht :=
    NumberTheory.primitiveQuadraticCharacter_apply_odd_prime hn hprime hodd
      (hprime.coprime_iff_not_dvd.mp hcp)
  simp only [Int.cast_natCast] at ht
  have hj : jacobiSym n p = -1 := by exact_mod_cast (ht.symm.trans hv)
  exact ⟨p, hprime, hodd, hpx, hcp, hj⟩

open AnalyticNumberTheory.Arithmetic in
/-- Under the same coupled local-rate and endpoint hypotheses, the least
negative odd-prime Jacobi witness is at most x. Apply leastness to the actual
constructed prime. The nonempty witness set supplies the existing definition. -/
theorem primeNegOneWitness_le_of_conductor_square_rates {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x a b : ℝ} (hx : 64 ≤ x)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (T : Finset ℕ) (e : ℕ → ℝ) (he : ∀ p ∈ T, 0 ≤ e p)
    (hR :
      ∀ p ∈ n.primeFactors,
        p ∣ (NumberTheory.complexQuadraticCharacter n hn).conductor →
          quadraticExcludedPrimeCost (NumberTheory.complexQuadraticCharacter n hn).conductor x
              (LLS.PaperStatements.untaperedExcludedEndpointWeight x) p ≤
            a * Real.log p + if p ∈ T then e p else 0)
    (hE :
      ∀ p ∈ n.primeFactors,
        ¬p ∣ (NumberTheory.complexQuadraticCharacter n hn).conductor →
          quadraticExcludedPrimeCost (NumberTheory.complexQuadraticCharacter n hn).conductor x
              (LLS.PaperStatements.untaperedExcludedEndpointWeight x) p ≤
            2 * b * Real.log p + if p ∈ T then e p else 0)
    (hsep :
      LLS.PaperStatements.oddEndpointTwoCostLimit (4 * bridge.squarefreePart) x x 0 0 +
            LLS.PaperStatements.conductorSquareUntaperedBudget bridge x a b T e -
          (LLS.PaperStatements.excludedReciprocalCoefficient x / x) * Real.log 2 <
        0)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ x := by
  obtain ⟨p, hp, ho, hpx, _, hv⟩ :=
    exists_prime_neg_one_of_conductor_square_rates bridge hGRH hx ha hb T e he hR hE hsep
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hpx

end PseudoPrime.PseudoSquare
