/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PreciseSavingTheorem11S1
public import PseudoPrime.PseudoSquare.Bounds.RefinedElementaryBounds

/-! # Factor-aware negative Jacobi witnesses from precise reciprocal saving

The precise-saving character theorem gives a coprime actual prime at the original
quadratic level four times the input. This module transfers that prime to the negative
Jacobi witness set without discarding factor information from the cutoff. Cumulative
majorants are separate: substituting an endpoint into this factor-aware expression does
not by itself bound every earlier input. Small inputs use the existing finite branch.
-/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Precise reciprocal saving supplies an actual negative Jacobi witness for large odd nonsquares.
Input: an odd nonsquare at least 750 and GRH. Claim: a witness meets the factor-aware cutoff.
Proof: apply the nonprincipal quadratic character theorem at level four times the input;
coprimality yields an odd prime with negative Jacobi value.
Role: retain the original factor data before deriving input-independent cumulative bounds. -/
theorem existsWitness_le_preciseSaving {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n) (hn750 : 750 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p ∈ NumberTheory.primeNegOneWitnessSet n ∧
        (p : ℝ) ≤ LLS.preciseSavingRadiusRoot (4 * n) ^ 2 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  obtain ⟨p, hp, hd, hv, hb⟩ :=
    LLS.exists_prime_neOne_preciseSaving_GRH (NumberTheory.complexQuadraticCharacter n hn)
      (Nat.mul_le_mul_left 4 hn750)
      (NumberTheory.complexQuadraticCharacter_ne_one_of_not_square n hn hns) hGRH
  exact ⟨p, NumberTheory.negOneWitness_mem_of_quadratic_ne_one n hn hp hd hv, hb⟩

/-- The least negative witness satisfies the same factor-aware precise-saving cutoff.
Input: an odd nonsquare at least 750, GRH and witness nonemptiness.
Claim: its least odd-prime negative Jacobi witness is bounded by the certified squared root.
Proof: minimize the actual witness. Role: preserve a factor-aware pointwise candidate. -/
theorem leastWitness_le_preciseSaving {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n) (hn750 : 750 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ LLS.preciseSavingRadiusRoot (4 * n) ^ 2 :=
  Exists.elim (existsWitness_le_preciseSaving hn hns hn750 hGRH) fun _p hp ↦
    (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw hp.1)).trans hp.2

end PseudoPrime.PseudoSquare
