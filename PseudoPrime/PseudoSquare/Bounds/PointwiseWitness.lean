/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PseudoSquare.Bounds.ElementaryOmegaFinal
import PseudoPrime.PseudoSquare.QNeOneFinal

/-! # Public pointwise bounds for least odd-prime witnesses -/

namespace PseudoPrime.PseudoSquare

/--
Under GRH, an odd nonsquare `n ≥ 3` has least odd-prime witnesses satisfying
`q_ne1 ≤ q_neg1 ≤ R(n)` after casting to the reals, where
`R(n) = (log(4n) + (24/5)·loglog(4n) + 3)^2`.
The witness sets' nonemptiness is supplied internally. The proof combines witness comparison,
`q_neg1 ≤ QNegOne n`, and the explicit finite-maximum bound.
This is the public pointwise elementary-radius estimate.
-/
theorem primeWitness_elementary_bound_explicit
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn3 : 3 ≤ n)
    (hn : Odd n) (hns : ¬IsSquare n) :
    (NumberTheory.primeNeOneWitness n
            (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
              (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) :
          ℝ) ≤
        (NumberTheory.primeNegOneWitness n
            (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns) :
          ℝ) ∧
      (NumberTheory.primeNegOneWitness n
            (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns) :
          ℝ) ≤
        (Real.log (4 * (n : ℝ)) + (24 / 5 : ℝ) * Real.log (Real.log (4 * (n : ℝ))) + 3) ^ 2 := by
  have hmem : n ∈ NumberTheory.admissibleFinset n :=
    NumberTheory.mem_admissibleFinset_iff.mpr ⟨by omega, le_rfl, hn, hns⟩
  exact
    ⟨Nat.cast_le.mpr
        (NumberTheory.primeNeOneWitness_le_primeNegOneWitness n
          (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)),
      (Nat.cast_le.mpr (primeNegOneWitness_le_QNegOne hmem)).trans
        (elementary_formula_explicit hGRH hn3).2⟩

/--
Under GRH, the least odd-prime Jacobi `≠ 1` witness of an odd nonsquare `n ≥ 11`
is at most `(log n)^2`. The proof extracts the existing existential bound and uses proof
irrelevance to identify the witness defined with a different nonemptiness proof.
This is the direct public pointwise logarithmic-square bound.
-/
theorem primeNeOneWitness_cast_le_log_sq_of_11_le
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn11 : 11 ≤ n)
    (hn : Odd n) (hns : ¬IsSquare n) :
    (NumberTheory.primeNeOneWitness n
          (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
            (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) :
        ℝ) ≤
      (Real.log (n : ℝ)) ^ 2 := by
  obtain ⟨hw, hbound⟩ := exists_primeNeOneWitness_cast_le_log_sq_of_odd_nonsquare hGRH hn hns hn11
  exact hbound

/--
Under GRH, every positive odd nonsquare `n` has an odd prime `p` with
`jacobiSym n p ≠ 1` and `p ≤ max 5 (log n)^2` after casting to the reals.
The proof combines membership of the least witness with the logarithmic-square bound for
`n ≥ 11` and the finite bound `p ≤ 5` for smaller inputs.
This supplies an explicit existence bound for Jacobi `≠ 1` witnesses.
-/
theorem exists_prime_ne_one_witness_of_grh
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hnpos : 0 < n)
    (hn : Odd n) (hns : ¬IsSquare n) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ max 5 (Real.log (n : ℝ) ^ 2) ∧ jacobiSym n p ≠ 1 := by
  let hneg := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  let hne := NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne hneg
  have hn1 : n ≠ 1 := by
    intro hn1
    subst n
    exact hns ⟨1, by simp only⟩
  have hn3 : 3 ≤ n := by
    obtain ⟨k, hk⟩ := hn
    omega
  have hmemNe := NumberTheory.primeNeOneWitness_mem n hne
  refine ⟨NumberTheory.primeNeOneWitness n hne, hmemNe.1, hmemNe.2.1, ?_, hmemNe.2.2⟩
  by_cases hn11 : 11 ≤ n
  · exact (primeNeOneWitness_cast_le_log_sq_of_11_le hGRH hn11 hn hns).trans (le_max_right _ _)
  · have hsmall := primeNeOneWitness_le_five_of_lt_sixteen hn hns (by omega)
    exact (Nat.cast_le.mpr hsmall).trans (le_max_left _ _)

/--
Under GRH, every positive odd nonsquare `n` has an odd prime `p` with
`jacobiSym n p = -1` and `p ≤ (log(4n) + (24/5)·loglog(4n) + 3)^2` in the reals.
The proof combines membership of the least `-1` witness with the upper bound from
`primeWitness_elementary_bound_explicit`.
This supplies an explicit existence bound for Jacobi `-1` witnesses.
-/
theorem exists_prime_neg_one_witness_of_grh
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hnpos : 0 < n)
    (hn : Odd n) (hns : ¬IsSquare n) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        (p : ℝ) ≤
          (Real.log (4 * (n : ℝ)) + (24 / 5 : ℝ) * Real.log (Real.log (4 * (n : ℝ))) + 3) ^ 2 ∧
        jacobiSym n p = -1 := by
  let hneg := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  have hn1 : n ≠ 1 := by
    intro hn1
    subst n
    exact hns ⟨1, by simp only⟩
  have hn3 : 3 ≤ n := by
    obtain ⟨k, hk⟩ := hn
    omega
  have hbound := (primeWitness_elementary_bound_explicit hGRH hn3 hn hns).2
  have hmemNeg := NumberTheory.primeNegOneWitness_mem n hneg
  exact ⟨NumberTheory.primeNegOneWitness n hneg, hmemNeg.1, hmemNeg.2.1, hbound, hmemNeg.2.2⟩

end PseudoPrime.PseudoSquare
