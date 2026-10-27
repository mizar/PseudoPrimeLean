/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Phase64SharpFixedJacobiCell

/-! # Separate the fixed spectral scale from the input logarithm -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: odd n and log(n) >= 10. Claim: 4*n is a valid ambient modulus and
its logarithm exceeds log(n) by at most 7/5. Bound small n by 2^13 and use the
conductor divisibility theorem. Role: avoid tying input n to the spectral level 64. -/
theorem phase64_ambient_four_mul_data_from_log_ten {n : ℕ} (hn : Odd n)
    (hlo : (10 : ℝ) ≤ Real.log n) :
    20000 ≤ 4 * n ∧
      (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ 4 * n ∧
      Real.log (4 * (n : ℝ)) ≤ Real.log n + 7 / 5 := by
  have hn5000 : 5000 ≤ n := by
    by_contra hsmall
    have hnsmall : n < 5000 := Nat.lt_of_not_ge hsmall
    have hnb : (n : ℝ) ≤ 8192 := Nat.cast_le.mpr (hnsmall.le.trans (by norm_num only : 5000 ≤ 8192))
    have hl := Real.log_le_log (Nat.cast_pos.mpr hn.pos) hnb
    rw [show (8192 : ℝ) = 2 ^ 13 by norm_num only, Real.log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    linarith only [hlo, hl, Real.log_two_lt_d9]
  have hq : 20000 ≤ 4 * n := by
    exact (by norm_num only : 20000 = 4 * 5000).trans_le (Nat.mul_le_mul_left 4 hn5000)
  have hm : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ 4 * n :=
    Nat.le_of_dvd (Nat.mul_pos (by norm_num only) hn.pos)
      (DirichletCharacter.conductor_dvd_level (NumberTheory.complexQuadraticCharacter n hn))
  have h4 : Real.log (4 : ℝ) ≤ 7 / 5 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9]
  refine ⟨hq, hm, ?_⟩
  rw [Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) (Nat.cast_pos.mpr hn.pos).ne']
  linarith only [h4]

/-- Input: a prime p <= B and a composite endpoint B. Claim: p <= B-1.
Exclude equality and descend one natural step. Role: sharpen a witness cutoff
without enumerating any range of input integers. -/
theorem prime_le_pred_of_le_composite {p B : ℕ} (hp : p.Prime) (hb : p ≤ B) (hB : ¬B.Prime) :
    p ≤ B - 1 := by
  have hlt : p < B := lt_of_le_of_ne hb (fun he ↦ hB (he ▸ hp))
  exact Nat.le_pred_of_lt hlt

/-- Input: a prime p <= 4096. Claim: p <= 4093.
Exclude the three endpoints using their explicit factorizations.
Role: improve the threshold for comparison with log(n)^2 without search certificates. -/
theorem prime_le_4093_of_le_4096 {p : ℕ} (hp : p.Prime) (hb : p ≤ 4096) : p ≤ 4093 := by
  have h4096 : ¬Nat.Prime 4096 :=
    Nat.not_prime_of_mul_eq (by norm_num only : 2 * 2048 = 4096) (by norm_num only)
      (by norm_num only)
  have h4095 : ¬Nat.Prime 4095 :=
    Nat.not_prime_of_mul_eq (by norm_num only : 3 * 1365 = 4095) (by norm_num only)
      (by norm_num only)
  have h4094 : ¬Nat.Prime 4094 :=
    Nat.not_prime_of_mul_eq (by norm_num only : 2 * 2047 = 4094) (by norm_num only)
      (by norm_num only)
  exact
    prime_le_pred_of_le_composite hp
      (prime_le_pred_of_le_composite hp (prime_le_pred_of_le_composite hp hb h4096) h4095) h4094

/-- Under GRH, odd nonsquare n and 10 <= log(n) <= 64.18, a negative odd-prime
Jacobi witness is at most 4093. Use the certified level-64 scale independently
of log(n), then exclude three composite endpoints. Role: separate the fixed
analytic scale from the input interval. -/
theorem exists_odd_prime_negative_phase64_fixed_cap_from_log_ten
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : (10 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 3209 / 50) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ≤ 4093 ∧ jacobiSym n p = -1 := by
  obtain ⟨bridge⟩ := NumberTheory.exists_jacobiCharacterArithmeticData hn.pos hn hns
  obtain ⟨hq, hm, hlog⟩ := phase64_ambient_four_mul_data_from_log_ten hn hlo
  have hqlog : Real.log ((4 * n : ℕ) : ℝ) ≤ 3279 / 50 := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    linarith only [hlog, hhi]
  have hB := phase64_sharp_fixed_budget_lt_margin hn.pos hhi hqlog
  have hA := phase64_principalRamp_sharp_lower
  have hgap :
    phase64NumericalJacobiBudget n (4 * n) (64 ^ 2 / (99 / 40)) <
      principalRampDifference (64 ^ 2 / (99 / 40)) := by
    norm_num only at hA hB ⊢
    exact hB.trans_le hA
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_odd_prime_negative_of_phase64_numerical_gap bridge hGRH hq hm
      (by norm_num only : (64 : ℝ) ≤ 64) (by norm_num only : (64 : ℝ) ≤ 64001 / 1000) hgap
  have hbN : p ≤ 4096 :=
    Nat.cast_le.mp
      (show (p : ℝ) ≤ ((4096 : ℕ) : ℝ) from by
        norm_num only at hb
        exact hb)
  exact ⟨p, hp, ho, prime_le_4093_of_le_4096 hp hbN, hv⟩

/-- Under GRH, odd nonsquare n and 63.977 <= log(n) <= 64.18, there is a negative
odd-prime Jacobi witness strictly below log(n)^2. Compare the proved cutoff 4093
with the square of the input lower bound. Role: lower the start of the certified
bounded interval without any new large finite sum. -/
theorem exists_odd_prime_negative_phase64_lower_start
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : (63977 / 1000 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 3209 / 50) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) < (Real.log n) ^ 2 ∧ jacobiSym n p = -1 := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_odd_prime_negative_phase64_fixed_cap_from_log_ten hGRH hn hns
      ((by norm_num only : (10 : ℝ) ≤ 63977 / 1000).trans hlo) hhi
  have hs : (4093 : ℝ) < (Real.log n) ^ 2 := by nlinarith only [hlo]
  exact ⟨p, hp, ho, (Nat.cast_le.mpr hb).trans_lt hs, hv⟩

/-- Under the same GRH and odd-nonsquare interval hypotheses, obtain a non-one
odd-prime Jacobi witness strictly below log(n)^2. Use the negative witness.
Role: export the lowered bounded interval for the non-one predicate. -/
theorem exists_odd_prime_not_one_phase64_lower_start
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : (63977 / 1000 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 3209 / 50) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) < (Real.log n) ^ 2 ∧ jacobiSym n p ≠ 1 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_odd_prime_negative_phase64_lower_start hGRH hn hns hlo hhi
  exact
    ⟨p, hp, ho, hb, by
      rw [hv]; norm_num only⟩

/-- Under the wider bounded cell and an explicit nonempty negative witness
set, its least odd-prime witness is strictly below log(n)^2. Compare the minimum
with the proved pointwise witness. No search-range bound is used in minimality. -/
theorem primeNegOneWitness_lt_phase64_lower_start
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : (63977 / 1000 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 3209 / 50)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) < (Real.log n) ^ 2 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_odd_prime_negative_phase64_lower_start hGRH hn hns hlo hhi
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans_lt hb

/-- Under the wider bounded cell and an explicit nonempty non-one witness
set, its least odd-prime witness is strictly below log(n)^2. Apply the existing
least-witness comparison to the newly proved pointwise witness. -/
theorem primeNeOneWitness_lt_phase64_lower_start
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : (63977 / 1000 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 3209 / 50)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) < (Real.log n) ^ 2 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_odd_prime_not_one_phase64_lower_start hGRH hn hns hlo hhi
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans_lt hb

end PseudoPrime.LLS
