/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaPrincipalEulerNonOneBounds
public import PseudoPrime.PseudoSquare.Bounds.GammaNonOneAdaptiveBounds

/-! # Coefficient-four-fifths Jacobi non-one bounds from logarithmic scale 22221 -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- For an odd nonsquare n with 4n ≥ 20000, GRH, L ≥ 22920 and log n ≤ L,
there is an odd-prime Jacobi non-one witness at most (4/5)L².
Apply the improved character theorem at level 4n and transfer prime values,
including nonunits. This is the large-level endpoint existence interface. -/
theorem exists_prime_ne_one_witness_le_gamma_endpoint_principal_euler {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hq : 20000 ≤ 4 * n) {L : ℝ} (hL : 22920 ≤ L) (hlogn : Real.log n ≤ L)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * L ^ 2 ∧ jacobiSym n p ≠ 1 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) (Odd.pos hn).ne'⟩
  have hlogq : Real.log (4 * n : ℕ) ≤ L + 7 / 5 := by
    rw [LLS.log_original_quadratic_level (Odd.pos hn)]
    linarith only [hlogn, Analysis.log_four_le_seven_fifths]
  obtain ⟨p, hp, hodd, hbound, hval⟩ :=
    LLS.exists_odd_prime_ne_one_of_gamma_log_22920 hq (NumberTheory.complexQuadraticCharacter n hn)
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn)
      (NumberTheory.complexQuadraticCharacter_ne_one_of_not_square n hn hns)
      (by exact ⟨2 * n, by ring⟩) hGRH hL hlogq
  refine ⟨p, hp, hodd, hbound, ?_⟩
  by_cases hc : Nat.Coprime p n
  · intro hv
    have he := NumberTheory.complexQuadraticCharacter_apply_odd_prime n hn hp hodd hc
    rw [hv, Int.cast_one] at he
    exact hval he
  · let : NeZero p := ⟨hp.ne_zero⟩
    have hg : (n : ℤ).gcd p ≠ 1 := by
      simpa only [Int.gcd_natCast_natCast, ← Nat.coprime_iff_gcd_eq_one, Nat.coprime_comm] using hc
    rw [NumberTheory.jacobi_eq_zero_iff_not_coprime.mpr hg]
    norm_num only

/-- Under GRH, for every odd nonsquare n and endpoint L ≥ 22920 with log n ≤ L,
the least odd-prime non-one Jacobi witness is at most (4/5)L².
Use the signed principal Euler theorem at large levels and the established global
log-square envelope at smaller levels. All inputs share the same endpoint.
The witness-set nonemptiness proof is explicit for finite-maximum consumers. -/
theorem primeNeOneWitness_cast_le_gamma_endpoint_principal_euler
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) {L : ℝ} (hL : 22920 ≤ L) (hlogn : Real.log n ≤ L)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ (4 / 5 : ℝ) * L ^ 2 := by
  by_cases hq : 20000 ≤ 4 * n
  · obtain ⟨p, hp, ho, hb, hv⟩ :=
      exists_prime_ne_one_witness_le_gamma_endpoint_principal_euler hn hns hq hL hlogn hGRH
    exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb
  · have hnsmall : n ≤ 46000 := by
      have ht := lt_of_not_ge hq
      nlinarith only [ht]
    have hnR : (n : ℝ) ≤ 46000 := by exact_mod_cast hnsmall
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Odd.pos hn
    have hl := (Real.log_le_log hn0 hnR).trans Analysis.log_46000_lt_eleven.le
    have hl0 : 0 ≤ Real.log n :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Odd.pos hn).ne')
    have hs : (Real.log n) ^ 2 ≤ (11 : ℝ) ^ 2 := (sq_le_sq₀ hl0 (by norm_num only)).mpr hl
    obtain ⟨p, hp, ho, hb, hv⟩ := exists_prime_ne_one_witness_of_grh hGRH (Odd.pos hn) hn hns
    have hmax : max (5 : ℝ) ((Real.log n) ^ 2) ≤ (11 : ℝ) ^ 2 := max_le (by norm_num only) hs
    have hbudget : (11 : ℝ) ^ 2 ≤ (4 / 5 : ℝ) * L ^ 2 := by
      nlinarith only [hL, sq_nonneg (L - 22920)]
    exact
      (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans
        (hb.trans (hmax.trans hbudget))

/-- Under GRH, every odd nonsquare n with log n ≥ 22920 has an odd-prime
Jacobi non-one witness at most (4/5)(log n)². Apply the endpoint least-witness
bound and use membership in the witness set. No modulus-size or numerical-gap
hypothesis remains. This is the pointwise coefficient-preserving start improvement. -/
theorem exists_prime_ne_one_witness_le_gamma_log_22920
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hL : 22920 ≤ Real.log n) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n) ^ 2 ∧ jacobiSym n p ≠ 1 := by
  let hw :=
    NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)
  have hm := NumberTheory.primeNeOneWitness_mem n hw
  exact
    ⟨NumberTheory.primeNeOneWitness n hw, hm.1, hm.2.1,
      primeNeOneWitness_cast_le_gamma_endpoint_principal_euler hGRH hn hns hL (le_refl _) hw,
      hm.2.2⟩

/-- Under GRH and log B ≥ 22920, the finite maximum of least non-one
Jacobi witnesses through B is at most (4/5)(log B)².
Cover each admissible input with the common endpoint bound, including small inputs.
This keeps the pointwise and finite-maximum conclusions separate. -/
theorem QNeOne_le_gamma_log_22920 {B : ℕ} (hB : 22920 ≤ Real.log B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNeOne B : ℝ) ≤ (4 / 5 : ℝ) * (Real.log B) ^ 2 := by
  apply QNeOne_cast_le_of_forall (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4 / 5) (sq_nonneg _))
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Odd.pos ha.odd
  have hnB : (n : ℝ) ≤ B := by exact_mod_cast ha.le
  exact
    primeNeOneWitness_cast_le_gamma_endpoint_principal_euler hGRH ha.odd ha.not_isSquare hB
      (Real.log_le_log hn0 hnB)
      (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare))

end PseudoPrime.PseudoSquare

namespace PseudoPrime.PseudoSquare

/-- For an odd nonsquare n with 4n ≥ 20000, GRH, L ≥ 22221 and log n ≤ L,
there is an odd-prime Jacobi non-one witness at most (4/5)L².
Apply the improved character theorem at level 4n and transfer prime values,
including nonunits. This is the large-level endpoint existence interface. -/
theorem exists_prime_ne_one_witness_le_gamma_endpoint_principal_euler_even {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hq : 20000 ≤ 4 * n) {L : ℝ} (hL : 22221 ≤ L) (hlogn : Real.log n ≤ L)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * L ^ 2 ∧ jacobiSym n p ≠ 1 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) (Odd.pos hn).ne'⟩
  have hlogq : Real.log (4 * n : ℕ) ≤ L + 7 / 5 := by
    rw [LLS.log_original_quadratic_level (Odd.pos hn)]
    linarith only [hlogn, Analysis.log_four_le_seven_fifths]
  obtain ⟨p, hp, hodd, hbound, hval⟩ :=
    LLS.exists_odd_prime_ne_one_of_even_gamma_log_22221 hq
      (NumberTheory.complexQuadraticCharacter n hn)
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn)
      (NumberTheory.complexQuadraticCharacter_ne_one_of_not_square n hn hns)
      (NumberTheory.complexQuadraticCharacter_isEven n hn) (by exact ⟨2 * n, by ring⟩) hGRH hL hlogq
  refine ⟨p, hp, hodd, hbound, ?_⟩
  by_cases hc : Nat.Coprime p n
  · intro hv
    have he := NumberTheory.complexQuadraticCharacter_apply_odd_prime n hn hp hodd hc
    rw [hv, Int.cast_one] at he
    exact hval he
  · let : NeZero p := ⟨hp.ne_zero⟩
    have hg : (n : ℤ).gcd p ≠ 1 := by
      simpa only [Int.gcd_natCast_natCast, ← Nat.coprime_iff_gcd_eq_one, Nat.coprime_comm] using hc
    rw [NumberTheory.jacobi_eq_zero_iff_not_coprime.mpr hg]
    norm_num only

/-- Under GRH, for every odd nonsquare n and endpoint L ≥ 22221 with log n ≤ L,
the least odd-prime non-one Jacobi witness is at most (4/5)L².
Use the signed principal Euler theorem at large levels and the established global
log-square envelope at smaller levels. All inputs share the same endpoint.
The witness-set nonemptiness proof is explicit for finite-maximum consumers. -/
theorem primeNeOneWitness_cast_le_gamma_endpoint_principal_euler_even
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) {L : ℝ} (hL : 22221 ≤ L) (hlogn : Real.log n ≤ L)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ (4 / 5 : ℝ) * L ^ 2 := by
  by_cases hq : 20000 ≤ 4 * n
  · obtain ⟨p, hp, ho, hb, hv⟩ :=
      exists_prime_ne_one_witness_le_gamma_endpoint_principal_euler_even hn hns hq hL hlogn hGRH
    exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb
  · have hnsmall : n ≤ 46000 := by
      have ht := lt_of_not_ge hq
      nlinarith only [ht]
    have hnR : (n : ℝ) ≤ 46000 := by exact_mod_cast hnsmall
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Odd.pos hn
    have hl := (Real.log_le_log hn0 hnR).trans Analysis.log_46000_lt_eleven.le
    have hl0 : 0 ≤ Real.log n :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Odd.pos hn).ne')
    have hs : (Real.log n) ^ 2 ≤ (11 : ℝ) ^ 2 := (sq_le_sq₀ hl0 (by norm_num only)).mpr hl
    obtain ⟨p, hp, ho, hb, hv⟩ := exists_prime_ne_one_witness_of_grh hGRH (Odd.pos hn) hn hns
    have hmax : max (5 : ℝ) ((Real.log n) ^ 2) ≤ (11 : ℝ) ^ 2 := max_le (by norm_num only) hs
    have hbudget : (11 : ℝ) ^ 2 ≤ (4 / 5 : ℝ) * L ^ 2 := by
      nlinarith only [hL, sq_nonneg (L - 22221)]
    exact
      (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans
        (hb.trans (hmax.trans hbudget))

/-- Under GRH, every odd nonsquare n with log n ≥ 22221 has an odd-prime
Jacobi non-one witness at most (4/5)(log n)². Apply the endpoint least-witness
bound and use membership in the witness set. No modulus-size or numerical-gap
hypothesis remains. This is the pointwise coefficient-preserving start improvement. -/
theorem exists_prime_ne_one_witness_le_gamma_log_22221
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hL : 22221 ≤ Real.log n) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n) ^ 2 ∧ jacobiSym n p ≠ 1 := by
  let hw :=
    NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)
  have hm := NumberTheory.primeNeOneWitness_mem n hw
  exact
    ⟨NumberTheory.primeNeOneWitness n hw, hm.1, hm.2.1,
      primeNeOneWitness_cast_le_gamma_endpoint_principal_euler_even hGRH hn hns hL (le_refl _) hw,
      hm.2.2⟩

/-- Under GRH and log B ≥ 22221, the finite maximum of least non-one
Jacobi witnesses through B is at most (4/5)(log B)².
Cover each admissible input with the common endpoint bound, including small inputs.
This keeps the pointwise and finite-maximum conclusions separate. -/
theorem QNeOne_le_gamma_log_22221 {B : ℕ} (hB : 22221 ≤ Real.log B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNeOne B : ℝ) ≤ (4 / 5 : ℝ) * (Real.log B) ^ 2 := by
  apply QNeOne_cast_le_of_forall (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4 / 5) (sq_nonneg _))
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Odd.pos ha.odd
  have hnB : (n : ℝ) ≤ B := by exact_mod_cast ha.le
  exact
    primeNeOneWitness_cast_le_gamma_endpoint_principal_euler_even hGRH ha.odd ha.not_isSquare hB
      (Real.log_le_log hn0 hnB)
      (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare))

end PseudoPrime.PseudoSquare
