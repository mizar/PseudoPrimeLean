/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.OddEndpointBranchWitness
public import PseudoPrime.NumberTheory.JacobiWitness.PrimitiveTransfer
public import PseudoPrime.PseudoSquare.QNeOneHalfShiftBounds

/-! # Jacobi non-one witnesses and finite maxima with refined two-adic endpoint costs -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- For odd nonsquare n under GRH and 64<=Y<=x, negativity of the cost endpoint
limit at 4*n with reciprocal cost (4/3)log 2 yields an odd non-one Jacobi prime
at most x. Use the quadratic two-value correction and conductor monotonicity,
then transfer primitive values allowing primes dividing n as zero witnesses. -/
theorem exists_odd_prime_jacobi_ne_one_of_four_thirds_costLimit_neg {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y : ℝ}
    (hx : 1 < x) (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hlim : LLS.PaperStatements.oddEndpointCostLimit (4 * n) x Y ((4 / 3 : ℝ) * Real.log 2) < 0) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ jacobiSym n p ≠ 1 := by
  let _ : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) (Odd.pos hn).ne'⟩
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
  have hqle := Nat.le_of_dvd (NeZero.pos (4 * n)) χ.conductor_dvd_level
  have hm :=
    LLS.PaperStatements.oddEndpointCostLimit_mono_level (c := (4 / 3 : ℝ) * Real.log 2)
      (Nat.pos_of_ne_zero χ.conductor_ne_zero) hqle hx.le hY
  obtain ⟨p, hp, ho, hpx, hv⟩ :=
    LLS.PaperStatements.exists_odd_prime_inducing_ne_one_of_costLimit_neg χ hq hne hquad hGRH hx hY
      hYx (LLS.PaperStatements.quadraticTwoReciprocalCost_le_four_thirds _) (hm.trans_lt hlim)
  exact
    ⟨p, hp, ho, hpx, NumberTheory.jacobi_ne_one_of_primitiveQuadraticCharacter_ne_one hn hp ho hv⟩

/-- Under the same refined endpoint condition, the least odd-prime non-one
Jacobi witness is at most x. The nonempty-set argument supplies the existing
least-witness definition. Obtain the actual prime and apply leastness. -/
theorem primeNeOneWitness_cast_le_of_four_thirds_costLimit_neg {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y : ℝ}
    (hx : 1 < x) (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hlim : LLS.PaperStatements.oddEndpointCostLimit (4 * n) x Y ((4 / 3 : ℝ) * Real.log 2) < 0)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ x := by
  obtain ⟨p, hp, ho, hpx, hv⟩ :=
    exists_odd_prime_jacobi_ne_one_of_four_thirds_costLimit_neg hn hns hGRH hx hY hYx hlim
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hpx

/-- Under GRH,64<=Y<=x and the refined cost condition at 4*B, the finite maximum
QNeOne(B) is at most x. Apply conductor-level monotonicity for each admissible
n<=B and the least-witness theorem. No finite classification or extra small-input
certificate is used; this is a sufficient scalar condition, not a fitted bound. -/
theorem QNeOne_cast_le_of_four_thirds_costLimit_neg {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y : ℝ} (hx : 1 < x)
    (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hlim : LLS.PaperStatements.oddEndpointCostLimit (4 * B) x Y ((4 / 3 : ℝ) * Real.log 2) < 0) :
    (QNeOne B : ℝ) ≤ x := by
  apply QNeOne_cast_le_of_forall (zero_lt_one.trans hx).le
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  have hq0 : 0 < 4 * n := Nat.mul_pos (by norm_num only) ha.odd.pos
  have hle : 4 * n ≤ 4 * B := Nat.mul_le_mul_left 4 ha.le
  have hm :=
    LLS.PaperStatements.oddEndpointCostLimit_mono_level (c := (4 / 3 : ℝ) * Real.log 2) hq0 hle
      hx.le hY
  exact
    primeNeOneWitness_cast_le_of_four_thirds_costLimit_neg ha.odd ha.not_isSquare hGRH hx hY hYx
      (hm.trans_lt hlim)
      (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare))

end PseudoPrime.PseudoSquare
