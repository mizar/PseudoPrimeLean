/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaNearSquareNegativeBounds
public import PseudoPrime.LLS.GammaPairedNearSquareNegativeBounds
public import PseudoPrime.PseudoSquare.Bounds.PointwiseWitness
public import PseudoPrime.PseudoSquare.Bounds.QNeOneLogSq
public import PseudoPrime.NumberTheory.JacobiCharacterPrimeEvaluation

/-! # Negative Jacobi witnesses below near-square endpoints from log 1000 -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- For an odd nonsquare n with 4n ≥ 20000, GRH, L ≥ 700 and log n ≤ L,
there is an odd-prime negative Jacobi witness at most (99/100)L².
Absence of a witness makes the level-4n character trivial on eligible primes;
the conductor-retaining analytic comparison rules this out. -/
theorem exists_prime_neg_one_witness_le_paired_nearSquare_endpoint {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hq : 20000 ≤ 4 * n) {L : ℝ} (hL : 700 ≤ L) (hlogn : Real.log n ≤ L)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 100 : ℝ) * L ^ 2 ∧ jacobiSym n p = -1 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hlogq : Real.log (4 * n : ℕ) ≤ L + 7 / 5 := by
    rw [LLS.log_original_quadratic_level hn.pos]
    linarith only [hlogn, Analysis.log_four_le_seven_fifths]
  by_contra hnone
  have hsmall :
    ∀ p : ℕ,
      p.Prime →
        ¬p ∣ 4 * n →
        (p : ℝ) ≤ (99 / 40 : ℝ) * ((2 / 5 : ℝ) * L ^ 2) →
        NumberTheory.complexQuadraticCharacter n hn p = 1 := by
    intro p hp hd hb
    by_contra hv
    have hm := NumberTheory.primeNegOneWitness_mem_of_complexQuadraticCharacter_ne_one n hn hp hd hv
    have hb' : (p : ℝ) ≤ (99 / 100 : ℝ) * L ^ 2 := by nlinarith only [hb]
    exact hnone ⟨p, hm.1, hm.2.1, hb', hm.2.2⟩
  exact
    LLS.gamma_ramp_prime_trivial_false_paired_nearSquare_endpoint hn
      (NumberTheory.complexQuadraticCharacter n hn)
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn)
      (NumberTheory.complexQuadraticCharacter_ne_one_of_not_square n hn hns) hq hL hlogq hGRH hsmall

/-- For an odd nonsquare n with 4n ≥ 20000, GRH, L ≥ 1000 and log n ≤ L,
there is an odd-prime negative Jacobi witness at most (99/100)L².
Absence of a witness makes the level-4n character trivial on eligible primes;
the conductor-retaining analytic comparison rules this out. -/
theorem exists_prime_neg_one_witness_le_nearSquare_endpoint {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hq : 20000 ≤ 4 * n) {L : ℝ} (hL : 1000 ≤ L) (hlogn : Real.log n ≤ L)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 100 : ℝ) * L ^ 2 ∧ jacobiSym n p = -1 := by
  exact
    exists_prime_neg_one_witness_le_paired_nearSquare_endpoint hn hns hq (by linarith only [hL])
      hlogn hGRH

/-- Under GRH, for any odd nonsquare n and common endpoint L ≥ 700 with
log n ≤ L, the least odd-prime negative witness is at most (99/100)L².
Use the analytic comparison at levels at least 20000 and bound the existing
global elementary root by seventy at smaller levels. This covers all inputs
without finite input certificates and supports finite witness maxima. -/
theorem primeNegOneWitness_cast_le_paired_nearSquare_endpoint
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) {L : ℝ} (hL : 700 ≤ L) (hlogn : Real.log n ≤ L)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (99 / 100 : ℝ) * L ^ 2 := by
  by_cases hq : 20000 ≤ 4 * n
  · obtain ⟨p, hp, ho, hb, hv⟩ :=
      exists_prime_neg_one_witness_le_paired_nearSquare_endpoint hn hns hq hL hlogn hGRH
    exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb
  · have hnR : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn.pos
    have hq0 : 0 < 4 * (n : ℝ) := by linarith only [hnR]
    have hqR : 4 * (n : ℝ) ≤ 46000 := by
      exact_mod_cast (show 4 * n ≤ 46000 by linarith only [lt_of_not_ge hq])
    have hlog := (Real.log_le_log hq0 hqR).trans Analysis.log_46000_lt_eleven.le
    have hlow :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 4) (show (4 : ℝ) ≤ 4 * n by linarith only [hnR])
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num only, Real.log_pow] at hlow
    norm_num only [Nat.cast_ofNat] at hlow
    have hbase : 1 ≤ Real.log (4 * (n : ℝ)) := by linarith only [hlow, Real.log_two_gt_d9]
    have hll0 := Real.log_nonneg hbase
    have hll := Real.log_le_self (zero_le_one.trans hbase)
    have hr0 :
      0 ≤ Real.log (4 * (n : ℝ)) + (24 / 5 : ℝ) * Real.log (Real.log (4 * (n : ℝ))) + 3 := by
      linarith only [hbase, hll0]
    have hr :
      Real.log (4 * (n : ℝ)) + (24 / 5 : ℝ) * Real.log (Real.log (4 * (n : ℝ))) + 3 ≤ 70 := by
      linarith only [hlog, hll]
    have hs := (sq_le_sq₀ hr0 (by norm_num only : (0 : ℝ) ≤ 70)).mpr hr
    have hbudget : (70 : ℝ) ^ 2 ≤ (99 / 100 : ℝ) * L ^ 2 := by
      nlinarith only [hL, sq_nonneg (L - 700)]
    obtain ⟨p, hp, ho, hb, hv⟩ := exists_prime_neg_one_witness_of_grh hGRH hn.pos hn hns
    exact
      (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans
        (hb.trans (hs.trans hbudget))

/-- Under GRH, for any odd nonsquare n and common endpoint L ≥ 1000 with
log n ≤ L, the least odd-prime negative witness is at most (99/100)L².
Use the analytic comparison at levels at least 20000 and bound the existing
global elementary root by seventy at smaller levels. This covers all inputs
without finite input certificates and supports finite witness maxima. -/
theorem primeNegOneWitness_cast_le_nearSquare_endpoint
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) {L : ℝ} (hL : 1000 ≤ L) (hlogn : Real.log n ≤ L)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (99 / 100 : ℝ) * L ^ 2 := by
  exact
    primeNegOneWitness_cast_le_paired_nearSquare_endpoint hGRH hn hns (by linarith only [hL]) hlogn
      hw

/-- Under GRH, every odd nonsquare n with log n ≥ 700 has an odd-prime
negative Jacobi witness at most (99/100)(log n)².
Apply the common endpoint least-witness theorem and witness membership.
There are no input-factorization, ambient-level or unproved-gap hypotheses. -/
theorem exists_prime_neg_one_witness_le_nearSquare_gamma_log_700
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hL : 700 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 100 : ℝ) * (Real.log n) ^ 2 ∧ jacobiSym n p = -1 := by
  let hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  have hm := NumberTheory.primeNegOneWitness_mem n hw
  exact
    ⟨NumberTheory.primeNegOneWitness n hw, hm.1, hm.2.1,
      primeNegOneWitness_cast_le_paired_nearSquare_endpoint hGRH hn hns hL (le_refl _) hw, hm.2.2⟩

/-- Under GRH, every odd nonsquare n with log n ≥ 1000 has an odd-prime
negative Jacobi witness at most (99/100)(log n)².
Apply the common endpoint least-witness theorem and witness membership.
There are no input-factorization, ambient-level or unproved-gap hypotheses. -/
theorem exists_prime_neg_one_witness_le_nearSquare_gamma_log_1000
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hL : 1000 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 100 : ℝ) * (Real.log n) ^ 2 ∧ jacobiSym n p = -1 := by
  exact exists_prime_neg_one_witness_le_nearSquare_gamma_log_700 hGRH hn hns (by linarith only [hL])

/-- Under GRH and log B ≥ 700, the finite maximum of least negative
odd-prime Jacobi witnesses through B is at most (99/100)(log B)².
The common endpoint theorem covers every admissible input, including those
below the original analytic level gate. No finite enumeration is used. -/
theorem QNegOne_le_nearSquare_gamma_log_700 {B : ℕ} (hB : 700 ≤ Real.log B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ (99 / 100 : ℝ) * (Real.log B) ^ 2 := by
  apply QNegOne_cast_le_of_forall (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 99 / 100) (sq_nonneg _))
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr ha.odd.pos
  have hnB : (n : ℝ) ≤ B := Nat.cast_le.mpr ha.le
  exact
    primeNegOneWitness_cast_le_paired_nearSquare_endpoint hGRH ha.odd ha.not_isSquare hB
      (Real.log_le_log hn0 hnB)
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)

/-- Under GRH and log B ≥ 1000, the finite maximum of least negative
odd-prime Jacobi witnesses through B is at most (99/100)(log B)².
The common endpoint theorem covers every admissible input, including those
below the original analytic level gate. No finite enumeration is used. -/
theorem QNegOne_le_nearSquare_gamma_log_1000 {B : ℕ} (hB : 1000 ≤ Real.log B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ (99 / 100 : ℝ) * (Real.log B) ^ 2 := by
  exact QNegOne_le_nearSquare_gamma_log_700 (by linarith only [hB]) hGRH

end PseudoPrime.PseudoSquare
