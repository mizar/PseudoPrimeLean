/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PseudoSquare.Computation.SmallN
import PseudoPrime.PseudoSquare.Computation.SmallWheelCertificates

/-!
# Q-side threshold adapters

This module contains threshold facts stated only with the neutral `QNegOne` maximum.
Selfridge maximum equalities and GRH applications remain in the integration layer.
-/

namespace PseudoPrime.PseudoSquare

theorem exists_qNeOneSmall750_to_or {P : ℕ → Prop} (h : ∃ p ∈ qNeOneSmall750Primes, P p) :
    P 3 ∨ P 5 ∨ P 7 ∨ P 11 ∨ P 13 := by
  rcases h with ⟨p, hp, hP⟩
  simp only [qNeOneSmall750Primes, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl hP
  · exact Or.inr (Or.inl hP)
  · exact Or.inr (Or.inr (Or.inl hP))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hP)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hP)))

theorem exists_qNeOneSmall1000_to_or {P : ℕ → Prop} (h : ∃ p ∈ qNeOneSmall1000Primes, P p) :
    P 3 ∨ P 5 ∨ P 7 ∨ P 11 ∨ P 13 ∨ P 17 := by
  rcases h with ⟨p, hp, hP⟩
  simp only [qNeOneSmall1000Primes, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl hP
  · exact Or.inr (Or.inl hP)
  · exact Or.inr (Or.inr (Or.inl hP))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hP)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hP))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hP))))

theorem exists_qNeOneSmall1500_to_or {P : ℕ → Prop} (h : ∃ p ∈ qNeOneSmall1500Primes, P p) :
    P 3 ∨ P 5 ∨ P 7 ∨ P 11 ∨ P 13 ∨ P 17 ∨ P 19 := by
  rcases h with ⟨p, hp, hP⟩
  simp only [qNeOneSmall1500Primes, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl hP
  · exact Or.inr (Or.inl hP)
  · exact Or.inr (Or.inr (Or.inl hP))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hP)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hP))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hP)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hP)))))

/-- A bounded finite square exclusion supplies the nonsquare hypothesis of the wheel. -/
theorem not_isSquare_of_fin_certificate {n K : ℕ} (hB : n < K ^ 2)
    (hns : ∀ k : Fin K, n ≠ k.val ^ 2) : ¬IsSquare n := by
  rintro ⟨k, hk⟩
  have hk2 : n = k ^ 2 := by simpa only [pow_two] using hk
  have hkK : k < K := by
    by_contra hnot
    have hKk : K ≤ k := by omega
    have hsq : K ^ 2 ≤ k ^ 2 := by simpa only [pow_two] using Nat.mul_self_le_mul_self hKk
    omega
  exact hns ⟨k, hkK⟩ hk2

/--
For `399 ≤ B`, the maximum `QNegOne B` is greater than `27`.
The proof places `399` in `PseudoPrime.NumberTheory.admissibleFinset B` and uses its
least witness `31` as a lower bound for the maximum. This supplies the threshold
without using any equality between Selfridge scan maxima.
-/
theorem twenty_seven_lt_QNegOne_of_399_le {B : ℕ} (hB : 399 ≤ B) : 27 < QNegOne B := by
  have hadm : 399 ∈ NumberTheory.admissibleFinset B := by
    apply NumberTheory.mem_admissibleFinset_iff.mpr
    exact ⟨by norm_num only, hB, by decide, not_isSquare_399⟩
  have hw :=
    NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare (by decide)
      not_isSquare_399
  have hle := primeNegOneWitness_le_QNegOne hadm
  rw [primeNegOneWitness_399_eq_31 hw] at hle
  omega

/-! The finite 750-bound certificate and its exact Q maximum. -/

def Through750NeOneCertificate : Prop :=
  ∀ n : Fin 750,
    n.val % 2 = 1 →
      (∀ k : Fin 28, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 ≠ 1 ∨
        jacobiSym n.val 5 ≠ 1 ∨
        jacobiSym n.val 7 ≠ 1 ∨ jacobiSym n.val 11 ≠ 1 ∨ jacobiSym n.val 13 ≠ 1

theorem through750NeOneCertificate_valid : Through750NeOneCertificate := by
  intro n hnodd hns
  have hsq := not_isSquare_of_fin_certificate (by omega) hns
  have hw := qNeOneSmall750_exists (Nat.odd_iff.mpr hnodd) hsq n.isLt
  exact exists_qNeOneSmall750_to_or hw

theorem primeNeOneWitness_le_thirteen_of_le_750 {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hn750 : n ≤ 750) :
    NumberTheory.primeNeOneWitness n
        (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
          (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) ≤
      13 := by
  have hnosquare : ∀ k : Fin 28, n ≠ k.val ^ 2 := by
    intro k hk
    exact hns ⟨k.val, by simpa only [pow_two] using hk⟩
  have hnlt750 : n < 750 := by
    rcases hn with ⟨k, hk⟩
    omega
  have hcertificate := through750NeOneCertificate_valid ⟨n, hnlt750⟩ (Nat.odd_iff.mp hn) hnosquare
  obtain hjacobi | hjacobi | hjacobi | hjacobi | hjacobi := hcertificate
  all_goals
    exact
      (NumberTheory.primeNeOneWitness_le n _ ⟨by decide, by decide, hjacobi⟩).trans
        (by norm_num only)

theorem not_isSquare_331 : ¬IsSquare 331 := by
  intro hsquare
  obtain ⟨k, hk⟩ := (isSquare_iff_exists_sq 331).mp hsquare
  have hk28 := square_root_lt_twenty_eight_of_lt_750 (n := 331) (by norm_num only) hk
  interval_cases k <;> norm_num only at hk

theorem primeNeOneWitness_331_eq_13
    (hw : (NumberTheory.PrimeNeOneWitnessSet 331).Nonempty) :
    NumberTheory.primeNeOneWitness 331 hw = 13 := by
  have hle : NumberTheory.primeNeOneWitness 331 hw ≤ 13 := by
    apply NumberTheory.primeNeOneWitness_le
    exact ⟨by decide, by decide, by norm_num only⟩
  have hmem := NumberTheory.primeNeOneWitness_mem 331 hw
  by_contra hne
  have hlt : NumberTheory.primeNeOneWitness 331 hw < 13 := by omega
  rcases hmem with ⟨_hprime, hodd, hjacobi⟩
  rcases hodd with ⟨k, hk⟩
  interval_cases NumberTheory.primeNeOneWitness 331 hw <;> try omega
  all_goals norm_num only at hjacobi

theorem QNeOne_750_eq_13 : QNeOne 750 = 13 := by
  apply Nat.le_antisymm
  · classical
    unfold QNeOne
    apply Finset.sup_le
    intro n _hn
    have hadm := NumberTheory.mem_admissibleFinset_iff.mp n.property
    exact primeNeOneWitness_le_thirteen_of_le_750 hadm.odd hadm.not_isSquare hadm.le
  · have hadm : 331 ∈ NumberTheory.admissibleFinset 750 := by
      apply NumberTheory.mem_admissibleFinset_iff.mpr
      exact ⟨by norm_num only, by norm_num only, by decide, not_isSquare_331⟩
    have hw : (NumberTheory.PrimeNeOneWitnessSet 331).Nonempty :=
      NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare (by decide)
          not_isSquare_331)
    rw [← primeNeOneWitness_331_eq_13 hw]
    exact primeNeOneWitness_le_QNeOne hadm

/-- The number `751` is not a square. -/
theorem not_isSquare_751 : ¬IsSquare 751 := by
  intro hsquare
  obtain ⟨k, hk⟩ := (isSquare_iff_exists_sq 751).mp hsquare
  have hk28 : k < 28 := by
    by_contra hnot
    have hk28' : 28 ≤ k := by omega
    have h784 : 784 ≤ k ^ 2 := by simpa only [pow_two] using Nat.mul_self_le_mul_self hk28'
    omega
  interval_cases k <;> norm_num only at hk

/-- At the next input, the least odd-prime Jacobi witness different from `1` jumps to `17`. -/
theorem primeNeOneWitness_751_eq_17
    (hw : (NumberTheory.PrimeNeOneWitnessSet 751).Nonempty) :
    NumberTheory.primeNeOneWitness 751 hw = 17 := by
  have hle : NumberTheory.primeNeOneWitness 751 hw ≤ 17 := by
    apply NumberTheory.primeNeOneWitness_le
    exact ⟨by decide, by decide, by norm_num only⟩
  have hmem := NumberTheory.primeNeOneWitness_mem 751 hw
  by_contra hne
  have hlt : NumberTheory.primeNeOneWitness 751 hw < 17 := by omega
  rcases hmem with ⟨_hprime, hodd, hjacobi⟩
  rcases hodd with ⟨k, hk⟩
  interval_cases NumberTheory.primeNeOneWitness 751 hw <;> try omega
  all_goals norm_num only at hjacobi

theorem QNeOne_751_eq_17 : QNeOne 751 = 17 := by
  apply Nat.le_antisymm
  · classical
    unfold QNeOne
    apply Finset.sup_le
    intro n _hn
    have hadm : NumberTheory.Admissible 751 n.val :=
      NumberTheory.mem_admissibleFinset_iff.mp n.property
    by_cases hn750 : n.val ≤ 750
    · exact
        (primeNeOneWitness_le_thirteen_of_le_750 hadm.odd hadm.not_isSquare hn750).trans
          (by norm_num only)
    · have hnle : n.val ≤ 751 := hadm.le
      have hn751 : n.val = 751 := by omega
      apply NumberTheory.primeNeOneWitness_le
      refine ⟨by decide, by decide, ?_⟩
      norm_num only [hn751]
  · have hadm : 751 ∈ NumberTheory.admissibleFinset 751 := by
      apply NumberTheory.mem_admissibleFinset_iff.mpr
      exact ⟨by norm_num only, by norm_num only, by decide, not_isSquare_751⟩
    have hw : (NumberTheory.PrimeNeOneWitnessSet 751).Nonempty :=
      NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare (by decide)
          not_isSquare_751)
    rw [← primeNeOneWitness_751_eq_17 hw]
    exact primeNeOneWitness_le_QNeOne hadm

end PseudoPrime.PseudoSquare
