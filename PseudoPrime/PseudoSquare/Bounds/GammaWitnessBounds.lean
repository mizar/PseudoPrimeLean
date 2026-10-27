/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaQuadraticNoWitness
public import PseudoPrime.Analysis.QuadraticGammaErrorBounds
public import PseudoPrime.Analysis.QuadraticGammaDecimalRefinement
public import PseudoPrime.NumberTheory.JacobiCharacterPrimeEvaluation

/-! # Direct Gamma bounds for negative and non-one quadratic prime witnesses -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Under GRH, an odd nonsquare n with 4n≥20000 and log(n)≥46000 has a
negative odd-prime Jacobi witness at most (4/5)log(n)².
A counterexample makes the original quadratic character trivial on eligible primes.
The smoothed Gamma comparison retains the signed local correction and conductor deficit.
This is the primary pointwise API at the natural-logarithm threshold;
the decimal-input theorems are its public wrappers. -/
theorem exists_primeNegOneWitness_le_gamma_of_large_log {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hq : 20000 ≤ 4 * n) (hL : 46000 ≤ Real.log n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p ∈ NumberTheory.primeNegOneWitnessSet n ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n) ^ 2 := by
  let _ : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) (Odd.pos hn).ne'⟩
  let x := (32 / 99 : ℝ) * (Real.log n) ^ 2
  have hcut : (99 / 40 : ℝ) * x = (4 / 5 : ℝ) * (Real.log n) ^ 2 := by
    dsimp only [x]
    ring
  by_contra hnone
  have hsmall :
    ∀ p : ℕ,
      p.Prime →
        ¬p ∣ 4 * n →
        (p : ℝ) ≤ (99 / 40 : ℝ) * x → NumberTheory.complexQuadraticCharacter n hn p = 1 := by
    intro p hp hd hb
    by_contra hv
    have hm := NumberTheory.primeNegOneWitness_mem_of_complexQuadraticCharacter_ne_one n hn hp hd hv
    rw [hcut] at hb
    exact hnone ⟨p, hm, hb⟩
  exact
    LLS.gamma_ramp_prime_trivial_false hn (NumberTheory.complexQuadraticCharacter n hn)
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn)
      (NumberTheory.complexQuadraticCharacter_ne_one_of_not_square n hn hns) hq hL hGRH hsmall

/-- For decimal exponent at least five, the power of ten is at least 20000.
Prove the comparison with a variable exponent to avoid evaluating enormous integer powers.
This supplies the ambient-level starting condition of the Gamma theorem. -/
private theorem decimal_cutoff_ge_twenty_thousand (d : ℕ) (hd : 5 ≤ d) : 20000 ≤ 10 ^ d := by
  exact (by decide : 20000 ≤ 10 ^ 5).trans (Nat.pow_le_pow_right (by decide : 0 < 10) hd)

/-- Under GRH, an odd nonsquare n≥10^20000 has an odd prime p with
Jacobi value −1 and p≤(4/5)log(n)².
The decimal threshold supplies log(n)≥3·10¹⁰ and the ambient-level condition;
the original-level Gamma contradiction supplies the witness.
This is the direct coefficient 0.8 theorem with an explicit universal pointwise threshold. -/
theorem exists_prime_neg_one_witness_le_gamma
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hN : 10 ^ 20000 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n) ^ 2 ∧ jacobiSym n p = -1 := by
  have hnlarge : 20000 ≤ n :=
    (decimal_cutoff_ge_twenty_thousand 20000 (by decide : 5 ≤ 20000)).trans hN
  have hq : 20000 ≤ 4 * n :=
    (by norm_num only : 20000 ≤ 4 * 20000).trans (Nat.mul_le_mul_left 4 hnlarge)
  have hL := (Analysis.log_nat_gt_46000_of_decimal hN).le
  obtain ⟨p, hm, hb⟩ := exists_primeNegOneWitness_le_gamma_of_large_log hn hns hq hL hGRH
  exact ⟨p, hm.1, hm.2.1, hb, hm.2.2⟩

/-- Under GRH, an odd nonsquare n≥10^20000 has an odd prime p with
Jacobi value different from one and p≤(4/5)log(n)².
Use the negative-witness theorem, which is stronger than the non-one condition.
This supplies the second direct coefficient 0.8 target without treating a zero value as negative. -/
theorem exists_prime_ne_one_witness_le_gamma
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hN : 10 ^ 20000 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n) ^ 2 ∧ jacobiSym n p ≠ 1 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_prime_neg_one_witness_le_gamma hGRH hn hns hN
  refine ⟨p, hp, ho, hb, ?_⟩
  rw [hv]
  norm_num only

/-- Under GRH, the least negative odd-prime Jacobi witness of an odd nonsquare
n≥10^20000 is at most (4/5)log(n)². Minimize the bounded prime witness
from the direct Gamma theorem. This supplies pointwise bounds for witness maxima. -/
theorem primeNegOneWitness_cast_le_gamma
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hN : 10 ^ 20000 ≤ n)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n) ^ 2 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_prime_neg_one_witness_le_gamma hGRH hn hns hN
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH, the least non-one odd-prime Jacobi witness of an odd nonsquare
n≥10^20000 is at most (4/5)log(n)². Minimize the bounded non-one prime witness
from the direct Gamma theorem. This supplies the least-witness form of the second target. -/
theorem primeNeOneWitness_cast_le_gamma
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hN : 10 ^ 20000 ≤ n)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n) ^ 2 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_prime_ne_one_witness_le_gamma hGRH hn hns hN
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH, an odd nonsquare n≥10^19978 has an odd prime negative
Jacobi witness at most (4/5)log(n)². The sharper decimal logarithm certificate
supplies the existing analytic threshold 46000; the proof keeps the coefficient
and all original-level local corrections. This is the refined pointwise public start. -/
theorem exists_prime_neg_one_witness_le_gamma_19978
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hN : 10 ^ 19978 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n) ^ 2 ∧ jacobiSym n p = -1 := by
  have hL := (Analysis.log_nat_gt_46000_of_decimal_19978 hN).le
  have hnlarge : 20000 ≤ n := by
    apply Nat.cast_le (α := ℝ).mp
    norm_num only [Nat.cast_ofNat]
    linarith only [hL, Real.log_le_self (Nat.cast_nonneg n)]
  have hq : 20000 ≤ 4 * n :=
    (by norm_num only : 20000 ≤ 4 * 20000).trans (Nat.mul_le_mul_left 4 hnlarge)
  obtain ⟨p, hm, hb⟩ := exists_primeNegOneWitness_le_gamma_of_large_log hn hns hq hL hGRH
  exact ⟨p, hm.1, hm.2.1, hb, hm.2.2⟩

/-- Under GRH for odd nonsquare n≥10^19978, the least odd-prime negative
Jacobi witness is at most (4/5)log(n)². Minimize the refined pointwise witness.
This connects the same decimal start to the least-witness API. -/
theorem primeNegOneWitness_cast_le_gamma_19978
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hN : 10 ^ 19978 ≤ n)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n) ^ 2 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_prime_neg_one_witness_le_gamma_19978 hGRH hn hns hN
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

end PseudoPrime.PseudoSquare
