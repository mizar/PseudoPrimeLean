/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.OddEndpointCostMonotonicity
public import PseudoPrime.NumberTheory.JacobiWitness.ConductorTwo
public import PseudoPrime.PseudoSquare.Bounds.OddEndpointTwoCostNonOneJacobi

/-! # Non-one Jacobi witnesses with correlated conductor and value-at-two costs -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- For odd nonsquare n under GRH, two negative endpoint conditions give an
odd-prime non-one Jacobi witness at most x. The zero-at-two branch uses conductor
at most 4*n and smaller costs; the nonzero branch uses conductor at most n.
Transfer the primitive witness, allowing divisors of n as zero witnesses. -/
theorem exists_odd_prime_jacobi_ne_one_of_conductor_branch_limits_neg {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y : ℝ}
    (hx : 1 < x) (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hzero :
      LLS.PaperStatements.oddEndpointTwoCostLimit (4 * n) x Y (Real.log 2) ((Real.log x) ^ 2 / 2) <
        0)
    (hnonzero :
      LLS.PaperStatements.oddEndpointTwoCostLimit n x Y ((4 / 3 : ℝ) * Real.log 2)
          ((Real.log x) ^ 2 / 2 + Real.log 2 * (Real.log x - Real.log 2)) <
        0) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ jacobiSym n p ≠ 1 := by
  let _ : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  let χ := NumberTheory.complexQuadraticCharacter n hn
  let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hne : χ.primitiveCharacter ≠ 1 :=
    NumberTheory.primitiveQuadraticCharacter_ne_one_of_not_square n hn hns
  have hq : 2 ≤ χ.conductor :=
    (Nat.two_le_iff _).mpr
      ⟨χ.conductor_ne_zero, fun he ↦ hne (DirichletCharacter.level_one' χ.primitiveCharacter he)⟩
  have hquad : χ.primitiveCharacter.IsQuadratic :=
    NumberTheory.isQuadratic_primitiveCharacter χ
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn)
  have hx4 : 4 ≤ x := le_trans (by linarith only [hY] : 4 ≤ Y) hYx
  have hsep :
    LLS.PaperStatements.oddEndpointTwoCostLimit χ.conductor x Y
        (LLS.PaperStatements.quadraticTwoReciprocalCost (χ.primitiveCharacter 2))
        (LLS.PaperStatements.quadraticTwoLogCost x (χ.primitiveCharacter 2)) <
      0 := by
    by_cases h2 : χ.primitiveCharacter 2 = 0
    · rw [LLS.PaperStatements.quadraticTwoReciprocalCost, ite_eq_left h2,
        LLS.PaperStatements.quadraticTwoLogCost, ite_eq_left h2]
      have hqle := Nat.le_of_dvd (NeZero.pos (4 * n)) χ.conductor_dvd_level
      exact
        (LLS.PaperStatements.oddEndpointTwoCostLimit_mono_level
              (Nat.pos_of_ne_zero χ.conductor_ne_zero) hqle hx.le hY).trans_lt
          hzero
    · have hqle := NumberTheory.primitiveQuadratic_conductor_le_of_two_ne_zero hn h2
      have hmC :=
        LLS.PaperStatements.oddEndpointTwoCostLimit_mono_costs χ.conductor (Y := Y) hx.le
          (LLS.PaperStatements.quadraticTwoReciprocalCost_le_four_thirds (χ.primitiveCharacter 2))
          (LLS.PaperStatements.quadraticTwoLogCost_le_envelope hx4 (χ.primitiveCharacter 2))
      have hmL :=
        LLS.PaperStatements.oddEndpointTwoCostLimit_mono_level (c := (4 / 3 : ℝ) * Real.log 2) (D :=
          (Real.log x) ^ 2 / 2 + Real.log 2 * (Real.log x - Real.log 2))
          (Nat.pos_of_ne_zero χ.conductor_ne_zero) hqle hx.le hY
      exact (hmC.trans hmL).trans_lt hnonzero
  obtain ⟨p, hp, ho, hpx, hv⟩ :=
    LLS.PaperStatements.exists_odd_prime_inducing_ne_one_of_twoCostLimit_neg χ hq hne hquad hGRH hx
      hY hYx (le_refl _) (le_refl _) hsep
  exact
    ⟨p, hp, ho, hpx, NumberTheory.jacobi_ne_one_of_primitiveQuadraticCharacter_ne_one hn hp ho hv⟩

/-- Under the conductor-correlated endpoint conditions, the least odd-prime
non-one Jacobi witness is at most x. Apply leastness to the prime witness;
the nonempty-set input supplies the existing least-witness definition. -/
theorem primeNeOneWitness_cast_le_of_conductor_branch_limits_neg {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y : ℝ}
    (hx : 1 < x) (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hzero :
      LLS.PaperStatements.oddEndpointTwoCostLimit (4 * n) x Y (Real.log 2) ((Real.log x) ^ 2 / 2) <
        0)
    (hnonzero :
      LLS.PaperStatements.oddEndpointTwoCostLimit n x Y ((4 / 3 : ℝ) * Real.log 2)
          ((Real.log x) ^ 2 / 2 + Real.log 2 * (Real.log x - Real.log 2)) <
        0)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ x := by
  obtain ⟨p, hp, ho, hpx, hv⟩ :=
    exists_odd_prime_jacobi_ne_one_of_conductor_branch_limits_neg hn hns hGRH hx hY hYx hzero
      hnonzero
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hpx

/-- Under GRH and the zero/nonzero conductor branch conditions at 4*B and B,
the finite maximum QNeOne(B) is at most x. Level monotonicity supplies both
conditions for each admissible n<=B; no finite input certificate is required. -/
theorem QNeOne_cast_le_of_conductor_branch_limits_neg {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y : ℝ} (hx : 1 < x)
    (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hzero :
      LLS.PaperStatements.oddEndpointTwoCostLimit (4 * B) x Y (Real.log 2) ((Real.log x) ^ 2 / 2) <
        0)
    (hnonzero :
      LLS.PaperStatements.oddEndpointTwoCostLimit B x Y ((4 / 3 : ℝ) * Real.log 2)
          ((Real.log x) ^ 2 / 2 + Real.log 2 * (Real.log x - Real.log 2)) <
        0) :
    (QNeOne B : ℝ) ≤ x := by
  apply QNeOne_cast_le_of_forall (zero_lt_one.trans hx).le
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  have hm0 :=
    LLS.PaperStatements.oddEndpointTwoCostLimit_mono_level (c := Real.log 2) (D :=
      (Real.log x) ^ 2 / 2) (Nat.mul_pos (by norm_num only : 0 < 4) ha.odd.pos)
      (Nat.mul_le_mul_left 4 ha.le) hx.le hY
  have hm1 :=
    LLS.PaperStatements.oddEndpointTwoCostLimit_mono_level (c := (4 / 3 : ℝ) * Real.log 2) (D :=
      (Real.log x) ^ 2 / 2 + Real.log 2 * (Real.log x - Real.log 2)) ha.odd.pos ha.le hx.le hY
  exact
    primeNeOneWitness_cast_le_of_conductor_branch_limits_neg ha.odd ha.not_isSquare hGRH hx hY hYx
      (hm0.trans_lt hzero) (hm1.trans_lt hnonzero)
      (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare))

end PseudoPrime.PseudoSquare
