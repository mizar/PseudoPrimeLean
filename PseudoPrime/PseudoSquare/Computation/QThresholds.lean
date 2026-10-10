/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Computation.SmallN
public import PseudoPrime.PseudoSquare.Computation.SmallWheelCertificates

/-!
# Q-side threshold adapters

This module contains threshold facts stated only with the neutral `QNegOne` maximum.
Selfridge maximum equalities and GRH applications remain in the integration layer.
-/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/--
For any predicate `P`, an existential witness in `qNeOneSmall750Primes` gives
the disjunction of `P` at `3, 5, 7, 11, 13`. The proof expands finite-set membership and
inserts the witness into the corresponding disjunct. This converts CRT witness existence
to the finite certificate propositions used by the threshold adapters.
-/
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

/--
For any predicate `P`, an existential witness in `qNeOneSmall1000Primes` gives
the disjunction of `P` at `3, 5, 7, 11, 13, 17`. The proof expands finite-set membership and
inserts the witness into the corresponding disjunct. This converts CRT witness existence
to the finite certificate propositions used by the threshold adapters.
-/
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

/--
For any predicate `P`, an existential witness in `qNeOneSmall1500Primes` gives
the disjunction of `P` at `3, 5, 7, 11, 13, 17, 19`. The proof expands finite-set membership and
inserts the witness into the corresponding disjunct. This converts CRT witness existence
to the finite certificate propositions used by the threshold adapters.
-/
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

/--
For naturals `n` and `K`, assume `n < K^2` and `n ≠ k^2` for every `k : Fin K`.
Then `n` is not a square: any hypothetical square root must be below `K` by monotonicity
of natural squares, contradicting the finite exclusion. This converts executable finite
certificate assumptions into the nonsquare input required by CRT witness theorems.
-/
theorem not_isSquare_of_fin_certificate {n K : ℕ} (hB : n < K ^ 2)
    (hns : ∀ k : Fin K, n ≠ k.val ^ 2) : ¬IsSquare n := by
  rintro ⟨k, hk⟩
  have hk2 : n = k ^ 2 := by simpa only [pow_two] using hk
  have hkK : k < K := by
    by_contra hnot
    have hKk : K ≤ k := Nat.le_of_not_lt hnot
    have hsq : K ^ 2 ≤ k ^ 2 := by simpa only [pow_two] using Nat.mul_self_le_mul_self hKk
    have hlt : k ^ 2 < K ^ 2 := by
      rw [← hk2]; exact hB
    exact (Nat.not_lt_of_ge hsq) hlt
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
    NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare (by decide) not_isSquare_399
  have hle := primeNegOneWitness_le_QNegOne hadm
  rw [primeNegOneWitness_399_eq_31 hw] at hle
  exact lt_of_lt_of_le (by norm_num only : 27 < 31) hle

/-! The finite 750-bound certificate and its exact Q maximum. -/

/--
The finite proposition that every odd `n : Fin 750` excluding squares with roots in
`Fin 28` has Jacobi value different from `1` at one of `3, 5, 7, 11, 13`.
Since `750 < 28^2`, the finite exclusions cover every possible square root.
This certificate supplies the least-witness bound `13` through the endpoint `750`.
-/
def Through750NeOneCertificate : Prop :=
  ∀ n : Fin 750,
    n.val % 2 = 1 →
      (∀ k : Fin 28, n.val ≠ k.val ^ 2) →
      jacobiSym n.val 3 ≠ 1 ∨
        jacobiSym n.val 5 ≠ 1 ∨
        jacobiSym n.val 7 ≠ 1 ∨ jacobiSym n.val 11 ≠ 1 ∨ jacobiSym n.val 13 ≠ 1

/--
Verify `Through750NeOneCertificate` without analytic assumptions. The proof turns the
finite square exclusions into nonsquareness, applies the small CRT wheel below `750`,
and expands its prime-set witness into the required disjunction.
This is the certificate consumed by the least-witness threshold bound.
-/
theorem through750NeOneCertificate_valid : Through750NeOneCertificate := by
  intro n hnodd hns
  have hsq :=
    not_isSquare_of_fin_certificate (lt_trans n.isLt (by norm_num only : 750 < 28 ^ 2)) hns
  have hw := qNeOneSmall750_exists (Nat.odd_iff.mpr hnodd) hsq n.isLt
  exact exists_qNeOneSmall750_to_or hw

/--
For odd nonsquare `n ≤ 750`, the least odd-prime Jacobi `≠ 1` witness is at most `13`.
Oddness excludes the even endpoint `750`, so the finite certificate applies below `750`.
Each of its five disjuncts supplies a witness, and minimality gives the bound.
This provides the upper bound for `QNeOne 750` and the small logarithmic-square range.
-/
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
    have hne : n ≠ 750 := by
      intro heq
      subst n
      exact (Nat.not_even_iff_odd.mpr hn) ⟨375, by norm_num only⟩
    exact lt_of_le_of_ne hn750 hne
  have hcertificate := through750NeOneCertificate_valid ⟨n, hnlt750⟩ (Nat.odd_iff.mp hn) hnosquare
  obtain hjacobi | hjacobi | hjacobi | hjacobi | hjacobi := hcertificate
  all_goals
    exact
      (NumberTheory.primeNeOneWitness_le n _ ⟨by decide, by decide, hjacobi⟩).trans
        (by norm_num only)

/--
The natural number `331` is not a square. A hypothetical square root is bounded by
`28`; enumerating those roots and normalizing their squares gives a contradiction.
This supplies admissibility of the input attaining the finite maximum.
-/
theorem not_isSquare_331 : ¬IsSquare 331 := by
  intro hsquare
  obtain ⟨k, hk⟩ := (isSquare_iff_exists_sq 331).mp hsquare
  have hk28 := square_root_lt_twenty_eight_of_lt_750 (n := 331) (by norm_num only) hk
  interval_cases k <;> norm_num only at hk

/--
For any nonemptiness proof `hw`, the least odd-prime Jacobi `≠ 1` witness of `331`
is exactly `13`. The proof first exhibits `13` as a witness, then excludes every smaller
odd candidate by checking its Jacobi value. This gives the lower bound attaining the
corresponding finite maximum.
-/
theorem primeNeOneWitness_331_eq_13 (hw : (NumberTheory.PrimeNeOneWitnessSet 331).Nonempty) :
    NumberTheory.primeNeOneWitness 331 hw = 13 := by
  have hle : NumberTheory.primeNeOneWitness 331 hw ≤ 13 := by
    apply NumberTheory.primeNeOneWitness_le
    exact ⟨by decide, by decide, by norm_num only⟩
  have hmem := NumberTheory.primeNeOneWitness_mem 331 hw
  by_contra hne
  have hlt : NumberTheory.primeNeOneWitness 331 hw < 13 := by
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exact False.elim (hne heq)
  rcases hmem with ⟨_hprime, hodd, hjacobi⟩
  have hpmod : NumberTheory.primeNeOneWitness 331 hw % 2 = 1 := Nat.odd_iff.mp hodd
  interval_cases NumberTheory.primeNeOneWitness 331 hw <;> norm_num only at hpmod
  all_goals norm_num only at hjacobi

/--
The finite maximum of least odd-prime Jacobi `≠ 1` witnesses through `750` is `13`.
For the upper bound, the proof applies the uniform bound `13` to every admissible member.
The lower bound comes from the admissible input `331` with least witness `13`.
This records the exact small threshold of the neutral `QNeOne` maximum.
-/
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
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare (by decide) not_isSquare_331)
    rw [← primeNeOneWitness_331_eq_13 hw]
    exact primeNeOneWitness_le_QNeOne hadm

/--
The natural number `751` is not a square. A hypothetical square root is bounded by
`28`; enumerating those roots and normalizing their squares gives a contradiction.
This supplies admissibility of the input attaining the finite maximum.
-/
theorem not_isSquare_751 : ¬IsSquare 751 := by
  intro hsquare
  obtain ⟨k, hk⟩ := (isSquare_iff_exists_sq 751).mp hsquare
  have hk28 : k < 28 := by
    by_contra hnot
    have hk28' : 28 ≤ k := Nat.le_of_not_lt hnot
    have h784 : 784 ≤ k ^ 2 := by simpa only [pow_two] using Nat.mul_self_le_mul_self hk28'
    rw [← hk] at h784
    norm_num only at h784
  interval_cases k <;> norm_num only at hk

/--
For any nonemptiness proof `hw`, the least odd-prime Jacobi `≠ 1` witness of `751`
is exactly `17`. The proof first exhibits `17` as a witness, then excludes every smaller
odd candidate by checking its Jacobi value. This gives the lower bound attaining the
corresponding finite maximum.
-/
theorem primeNeOneWitness_751_eq_17 (hw : (NumberTheory.PrimeNeOneWitnessSet 751).Nonempty) :
    NumberTheory.primeNeOneWitness 751 hw = 17 := by
  have hle : NumberTheory.primeNeOneWitness 751 hw ≤ 17 := by
    apply NumberTheory.primeNeOneWitness_le
    exact ⟨by decide, by decide, by norm_num only⟩
  have hmem := NumberTheory.primeNeOneWitness_mem 751 hw
  by_contra hne
  have hlt : NumberTheory.primeNeOneWitness 751 hw < 17 := by
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exact False.elim (hne heq)
  rcases hmem with ⟨_hprime, hodd, hjacobi⟩
  have hpmod : NumberTheory.primeNeOneWitness 751 hw % 2 = 1 := Nat.odd_iff.mp hodd
  interval_cases NumberTheory.primeNeOneWitness 751 hw <;> norm_num only at hpmod
  all_goals norm_num only at hjacobi

/--
The finite maximum of least odd-prime Jacobi `≠ 1` witnesses through `751` is `17`.
For the upper bound, the proof splits admissible inputs at `750`, using the bound `13` below and
witness `17` at `751`.
The lower bound comes from the admissible input `751` with least witness `17`.
This records the exact small threshold of the neutral `QNeOne` maximum.
-/
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
      have hn751 : n.val = 751 := by
        rcases Nat.lt_or_eq_of_le hnle with hlt | heq
        · exact False.elim (hn750 (Nat.le_of_lt_succ hlt))
        · exact heq
      apply NumberTheory.primeNeOneWitness_le
      refine ⟨by decide, by decide, ?_⟩
      norm_num only [hn751]
  · have hadm : 751 ∈ NumberTheory.admissibleFinset 751 := by
      apply NumberTheory.mem_admissibleFinset_iff.mpr
      exact ⟨by norm_num only, by norm_num only, by decide, not_isSquare_751⟩
    have hw : (NumberTheory.PrimeNeOneWitnessSet 751).Nonempty :=
      NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare (by decide) not_isSquare_751)
    rw [← primeNeOneWitness_751_eq_17 hw]
    exact primeNeOneWitness_le_QNeOne hadm

end PseudoPrime.PseudoSquare
