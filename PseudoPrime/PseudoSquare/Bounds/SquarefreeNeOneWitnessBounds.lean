/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.JacobiWitness.SquarefreeReduction
public import PseudoPrime.PseudoSquare.QNeOneFinal

/-! # Non-one witness bounds depending only on the squarefree part -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Under GRH, the least non-one odd-prime witness for an odd nonsquare
input is at most max(5,log(d)^2), where d is its squarefree part. The three small
parts have witnesses three or five; larger parts use the existing log-square
bound before unconditional squarefree transfer. No square-factor exclusion cost remains. -/
theorem primeNeOneWitness_le_squarefree_log_square {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ max 5 ((Real.log bridge.squarefreePart) ^ 2) := by
  have transfer {p : ℕ} (hp : p ∈ NumberTheory.primeNeOneWitnessSet bridge.squarefreePart)
    (hb : p ≤ 5) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ max 5 ((Real.log bridge.squarefreePart) ^ 2) :=
    (Nat.cast_le.mpr
          (NumberTheory.primeNeOneWitness_le n hw
            (NumberTheory.primeNeOneWitness_mem_of_squarefreePart_mem bridge hp))).trans
      ((Nat.cast_le.mpr hb).trans (le_max_left _ _))
  by_cases h3 : bridge.squarefreePart = 3
  · apply transfer (p := 3) _ (by decide : 3 ≤ 5)
    rw [h3]
    exact NumberTheory.primeNeOneWitness_mem_of_dvd Nat.prime_three (by decide : Odd 3) (dvd_refl 3)
  by_cases h5 : bridge.squarefreePart = 5
  · apply transfer (p := 3) _ (by decide : 3 ≤ 5)
    rw [h5]
    exact ⟨Nat.prime_three, by decide, NumberTheory.jacobiSym_five_three_ne_one⟩
  by_cases h7 : bridge.squarefreePart = 7
  · apply transfer (p := 5) _ (le_refl 5)
    rw [h7]
    exact ⟨Nat.prime_five, by decide, NumberTheory.jacobiSym_seven_five_ne_one⟩
  have hd11 := bridge.squarefreePart_ge_eleven_of_not_small h3 h5 h7
  obtain ⟨hd, hb⟩ :=
    exists_primeNeOneWitness_cast_le_log_sq_of_odd_nonsquare hGRH bridge.squarefreePart_odd
      bridge.squarefreePart_not_isSquare hd11
  have htr := NumberTheory.primeNeOneWitness_le_of_squarefreePart bridge (hd := hd)
  exact (Nat.cast_le.mpr htr).trans (hb.trans (le_max_right _ _))

/-- Under GRH, if log(d) is at most log(n)^(1-epsilon/2) and the target
power is at least five, the least non-one odd-prime witness is at most
log(n)^(2-epsilon). Square the nonnegative squarefree logarithm bound.
This is a structured-input exponent estimate with coefficient one. -/
theorem primeNeOneWitness_le_log_power_of_squarefree_log {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) {epsilon : ℝ}
    (hsmall : (5 : ℝ) ≤ (Real.log n) ^ (2 - epsilon))
    (hd : Real.log bridge.squarefreePart ≤ (Real.log n) ^ (1 - epsilon / 2)) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ (Real.log n) ^ (2 - epsilon) := by
  have hb := primeNeOneWitness_le_squarefree_log_square bridge hGRH hw
  have hs := pow_le_pow_left₀ (Real.log_natCast_nonneg bridge.squarefreePart) hd 2
  have he : ((Real.log n) ^ (1 - epsilon / 2)) ^ (2 : ℕ) = (Real.log n) ^ (2 - epsilon) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (Real.log_natCast_nonneg n)]
    congr 1
    ring
  rw [he] at hs
  exact hb.trans (max_le hsmall hs)

/-- Under GRH, an actual non-one odd-prime witness lies below the squarefree
log-square bound. Use unconditional nonemptiness and take the least witness.
The resulting prime may divide n, in which case its Jacobi value is zero. -/
theorem exists_odd_prime_ne_one_le_squarefree_log_square {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧ jacobiSym n p ≠ 1 ∧ (p : ℝ) ≤ max 5 ((Real.log bridge.squarefreePart) ^ 2) := by
  have hw :=
    NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)
  have hp := NumberTheory.primeNeOneWitness_mem n hw
  exact
    ⟨NumberTheory.primeNeOneWitness n hw, hp.1, hp.2.1, hp.2.2,
      primeNeOneWitness_le_squarefree_log_square bridge hGRH hw⟩

/-- Under the squarefree logarithm and target-size conditions, GRH gives
an actual non-one odd-prime witness below log(n)^(2-epsilon). Instantiate the
least-witness estimate using unconditional existence, with no added coprimality
condition. This is the prime-existence interface for the exponent improvement. -/
theorem exists_odd_prime_ne_one_le_log_power_of_squarefree_log {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {epsilon : ℝ}
    (hsmall : (5 : ℝ) ≤ (Real.log n) ^ (2 - epsilon))
    (hd : Real.log bridge.squarefreePart ≤ (Real.log n) ^ (1 - epsilon / 2)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ jacobiSym n p ≠ 1 ∧ (p : ℝ) ≤ (Real.log n) ^ (2 - epsilon) := by
  have hw :=
    NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)
  have hp := NumberTheory.primeNeOneWitness_mem n hw
  exact
    ⟨NumberTheory.primeNeOneWitness n hw, hp.1, hp.2.1, hp.2.2,
      primeNeOneWitness_le_log_power_of_squarefree_log bridge hGRH hw hsmall hd⟩

end PseudoPrime.PseudoSquare
