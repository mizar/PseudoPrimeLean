/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.Analysis.QNeOneElementaryBounds
import PseudoPrime.PseudoSquare.Bounds.WitnessMaximum
import PseudoPrime.AnalyticNumberTheory.Arithmetic.OddPrimeCutoff
import PseudoPrime.PseudoSquare.QNeOneFinal

/-!
# A uniform logarithmic bound on the admissible domain

This file consumes the pointwise `log n` witness theorem and lifts it to the
fixed radius `log B` used by the finite `QNeOne` maximum.
-/

namespace PseudoPrime.PseudoSquare

private lemma exists_primeNeOneWitness_cast_le_log_sq_of_small_admissible {B n : ℕ} (hB : 10 ≤ B)
    (hn : n ∈ NumberTheory.admissibleFinset B) (hn3 : n = 3 ∨ n = 5 ∨ n = 7) :
    ∃ hdn : (NumberTheory.PrimeNeOneWitnessSet n).Nonempty,
      (NumberTheory.primeNeOneWitness n hdn : ℝ) ≤ (Real.log (B : ℝ)) ^ 2 := by
  rcases hn3 with rfl | rfl | rfl
  · let hdn : (NumberTheory.PrimeNeOneWitnessSet 3).Nonempty :=
      NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare (by decide)
          (not_isSquare_of_fin_certificate (n := 3) (K := 2) (by norm_num only) (by decide)))
    refine ⟨hdn, ?_⟩
    have hle5 :=
      NumberTheory.primeNeOneWitness_le 3 hdn
        (show 5 ∈ NumberTheory.PrimeNeOneWitnessSet 3 from
          ⟨by decide, by decide, by
            norm_num only [NumberTheory.Internal.jacobiSym_three_five_eq_neg_one]⟩)
    have hle5R : (NumberTheory.primeNeOneWitness 3 hdn : ℝ) ≤ 5 := by exact_mod_cast hle5
    exact hle5R.trans (le_of_lt (Analysis.five_lt_log_sq_of_ten_le hB))
  · let hdn : (NumberTheory.PrimeNeOneWitnessSet 5).Nonempty :=
      NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare (by decide)
          (not_isSquare_of_fin_certificate (n := 5) (K := 3) (by norm_num only) (by decide)))
    refine ⟨hdn, ?_⟩
    have hle3 :=
      NumberTheory.primeNeOneWitness_le 5 hdn
        (show 3 ∈ NumberTheory.PrimeNeOneWitnessSet 5 from
          ⟨by decide, by decide, NumberTheory.jacobiSym_five_three_ne_one⟩)
    have hle3R : (NumberTheory.primeNeOneWitness 5 hdn : ℝ) ≤ 3 := by exact_mod_cast hle3
    have hBbound : (3 : ℝ) ≤ (Real.log (B : ℝ)) ^ 2 := by
      nlinarith only [Analysis.five_lt_log_sq_of_ten_le hB]
    exact hle3R.trans hBbound
  · let hdn : (NumberTheory.PrimeNeOneWitnessSet 7).Nonempty :=
      NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare (by decide)
          (not_isSquare_of_fin_certificate (n := 7) (K := 3) (by norm_num only) (by decide)))
    refine ⟨hdn, ?_⟩
    have hle5 :=
      NumberTheory.primeNeOneWitness_le 7 hdn
        (show 5 ∈ NumberTheory.PrimeNeOneWitnessSet 7 from
          ⟨by decide, by decide, NumberTheory.jacobiSym_seven_five_ne_one⟩)
    have hle5R : (NumberTheory.primeNeOneWitness 7 hdn : ℝ) ≤ 5 := by exact_mod_cast hle5
    exact hle5R.trans (le_of_lt (Analysis.five_lt_log_sq_of_ten_le hB))

/-
Input/assumptions: GRH, `B ≥ 10`, and `n` belongs to the admissible finite domain.
Conclusion: the least odd-prime Jacobi-`≠ 1` witness for `n` is below the
fixed radius `(log B)^2`.
Content: the cases `n = 3, 5, 7` use explicit Jacobi witnesses; `n ≥ 11`
consumes the analytic `log n` bound and monotonicity of the logarithm.
Proof: split at `11 ≤ n`, classify the remaining positive odd nonsquares,
and compare logarithmic radii after casting the natural inequalities to `ℝ`.
Role: the pointwise input to `QNeOne_le_log_sq_of_grh`.
-/
theorem exists_primeNeOneWitness_cast_le_log_sq_of_admissible
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {B n : ℕ} (hB : 10 ≤ B)
    (hn : n ∈ NumberTheory.admissibleFinset B) :
    ∃ hdn : (NumberTheory.PrimeNeOneWitnessSet n).Nonempty,
      (NumberTheory.primeNeOneWitness n hdn : ℝ) ≤ (Real.log (B : ℝ)) ^ 2 := by
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  by_cases hn11 : 11 ≤ n
  · obtain ⟨hdn, hdnBound⟩ :=
      exists_primeNeOneWitness_cast_le_log_sq_of_odd_nonsquare hGRH ha.odd ha.not_isSquare hn11
    refine ⟨hdn, ?_⟩
    have hnposR : (0 : ℝ) < n := by exact_mod_cast ha.pos
    have hBposR : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
    have hnleR : (n : ℝ) ≤ B := by exact_mod_cast ha.le
    have hlog : Real.log (n : ℝ) ≤ Real.log (B : ℝ) :=
      Real.strictMonoOn_log.monotoneOn hnposR hBposR hnleR
    have hlogn : 0 ≤ Real.log (n : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ n by omega)
    have hlogB : 0 ≤ Real.log (B : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ B by omega)
    nlinarith only [hdnBound, hlog, hlogn, hlogB, sq_nonneg (Real.log (B : ℝ) - Real.log (n : ℝ))]
  · have hcases : n = 3 ∨ n = 5 ∨ n = 7 := by
      obtain ⟨k, hk⟩ := ha.odd
      have hn1 : n ≠ 1 := by
        intro h
        apply ha.not_isSquare
        exact ⟨1, by omega⟩
      have hn9 : n ≠ 9 := by
        intro h
        apply ha.not_isSquare
        exact ⟨3, by omega⟩
      omega
    exact exists_primeNeOneWitness_cast_le_log_sq_of_small_admissible hB hn hcases

/-
Input/assumptions: a nonnegative real pointwise bound for every admissible
input up to `B`.
Conclusion: the cast of the finite maximum `QNeOne B` satisfies the same
bound.
Content: the attached admissible finset is consumed by `Finset.sup_induction`.
Proof: the empty maximum is bounded by `hR`, the maximum case follows from
`Nat.cast_max`, and each attached element is discharged by `hbound`.
Role: the finite-max interface for `QNeOne_le_log_sq_of_grh`.
-/
theorem QNeOne_cast_le_of_forall {B : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (hbound :
      ∀ n,
        (hn : n ∈ NumberTheory.admissibleFinset B) →
          (NumberTheory.primeNeOneWitness n
                (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
                  (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare
                    ((NumberTheory.mem_admissibleFinset_iff.mp hn).odd)
                    ((NumberTheory.mem_admissibleFinset_iff.mp hn).not_isSquare))) :
              ℝ) ≤
            R) :
    (QNeOne B : ℝ) ≤ R := by
  classical
  unfold QNeOne
  apply
    Finset.sup_induction (p := fun k : ℕ => (k : ℝ) ≤ R)
      (by
        rw [Nat.bot_eq_zero, Nat.cast_zero]
        exact hR)
  · intro a ha b hb
    simpa only [Nat.cast_max] using max_le ha hb
  · intro n _
    exact hbound n.val n.property

/-
Input/assumptions: GRH and `B ≥ 10`.
Conclusion: `(QNeOne B : ℝ) ≤ (log B)^2`.
Content: `exists_primeNeOneWitness_cast_le_log_sq_of_admissible` is lifted through the finite
maximum.
Proof: apply `QNeOne_cast_le_of_forall` with the nonnegative logarithmic square
and discharge each admissible member using the fixed-radius consumer.
Role: the real-valued uniform logarithmic-square bound.
-/
theorem QNeOne_le_log_sq_of_grh (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {B : ℕ} (hB : 10 ≤ B) : (QNeOne B : ℝ) ≤ (Real.log (B : ℝ)) ^ 2 := by
  apply QNeOne_cast_le_of_forall (sq_nonneg _)
  intro n hn
  exact exists_primeNeOneWitness_cast_le_log_sq_of_admissible hGRH hB hn |>.choose_spec

/-
Input/assumptions: GRH and `B ≥ 10`.
Conclusion: the natural maximum `QNeOne B` is below the greatest odd prime
not exceeding the real radius `(log B)^2`.
Content: each least witness is prime and odd, so `Arithmetic.le_greatestOddPrimeLE`
rounds its real bound before the finite supremum is taken.
Proof: use `Finset.sup_induction` on the attached admissible finset and the
fixed-radius pointwise theorem for each element.
Role: the integer odd-prime-cutoff form of the uniform bound.
-/
theorem QNeOne_le_greatestOddPrimeLE_of_grh
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {B : ℕ} (hB : 10 ≤ B) :
    QNeOne B ≤ AnalyticNumberTheory.Arithmetic.greatestOddPrimeLE ((Real.log (B : ℝ)) ^ 2) := by
  classical
  unfold QNeOne
  apply
    Finset.sup_induction (p := fun k : ℕ =>
      k ≤ AnalyticNumberTheory.Arithmetic.greatestOddPrimeLE ((Real.log (B : ℝ)) ^ 2))
      (Nat.zero_le _)
  · intro a ha b hb
    exact max_le ha hb
  · intro n _
    obtain ⟨hdn, hbound⟩ := exists_primeNeOneWitness_cast_le_log_sq_of_admissible hGRH hB n.property
    have hmem := NumberTheory.primeNeOneWitness_mem n.val hdn
    apply AnalyticNumberTheory.Arithmetic.le_greatestOddPrimeLE hmem.1 hmem.2.1
    exact hbound

end PseudoPrime.PseudoSquare
