/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Phase64EndpointJacobiBudget
public import PseudoPrime.Analysis.Phase64EndpointCertificates
public import PseudoPrime.NumberTheory.JacobiWitness.Existence

/-! # Fully certified Jacobi witnesses on the first phase64 logarithmic cell -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For an odd integer with log(n)>=64, the ambient choice q=4*n is at least
20000, bounds the quadratic conductor and has log(q)<=log(n)+7/5. Exclude n<5000
using the logarithm of 2^13, then use conductor divisibility and the logarithm product. -/
theorem phase64_ambient_four_mul_data {n : ℕ} (hn : Odd n) (hlo : (64 : ℝ) ≤ Real.log n) :
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

/-- Under GRH, an odd nonsquare integer with 64<=log(n)<=64.001 has an odd
prime p<=log(n)^2 with Jacobi value -1. Instantiate the proved endpoint caps and
choose the ambient modulus 4*n. Every numerical and spectral premise is discharged;
this is a bounded real logarithmic cell, not a whole-half-line theorem. -/
theorem exists_odd_prime_negative_phase64_log_cell
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : (64 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 64001 / 1000) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (Real.log n) ^ 2 ∧ jacobiSym n p = -1 := by
  obtain ⟨bridge⟩ := NumberTheory.exists_jacobiCharacterArithmeticData hn.pos hn hns
  obtain ⟨hq, hm, hlog⟩ := phase64_ambient_four_mul_data hn hlo
  have hqlog : Real.log ((4 * n : ℕ) : ℝ) ≤ Real.log n + 7 / 5 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlog
  exact
    exists_odd_prime_negative_of_phase64_prefix_caps bridge hGRH hq hm hlo hhi le_rfl hqlog
      Analysis.Phase64EndpointCertificates.phase64_ramp_endpoint_lower
      Analysis.Phase64EndpointCertificates.phase64_principal_endpoint_upper

/-- Under GRH, an odd nonsquare in the same bounded logarithmic cell has
an odd-prime Jacobi witness different from one through log(n)^2. A certified negative
witness is also a non-one witness. -/
theorem exists_odd_prime_not_one_phase64_log_cell
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : (64 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 64001 / 1000) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (Real.log n) ^ 2 ∧ jacobiSym n p ≠ 1 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_odd_prime_negative_phase64_log_cell hGRH hn hns hlo hhi
  exact
    ⟨p, hp, ho, hb, by
      rw [hv]; norm_num only⟩

/-- Under GRH and the bounded logarithmic-cell hypotheses, the least odd-prime
negative Jacobi witness is at most log(n)^2. Compare the least witness with the proved
pointwise witness. Its nonemptiness proof remains an explicit API argument. -/
theorem primeNegOneWitness_le_phase64_log_cell
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : (64 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 64001 / 1000)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (Real.log n) ^ 2 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_odd_prime_negative_phase64_log_cell hGRH hn hns hlo hhi
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH and the bounded logarithmic-cell hypotheses, the least odd-prime
non-one Jacobi witness is at most log(n)^2. Apply the pointwise non-one witness theorem
and the existing least-witness comparison. -/
theorem primeNeOneWitness_le_phase64_log_cell
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hlo : (64 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 64001 / 1000)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ (Real.log n) ^ 2 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_odd_prime_not_one_phase64_log_cell hGRH hn hns hlo hhi
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

end PseudoPrime.LLS
