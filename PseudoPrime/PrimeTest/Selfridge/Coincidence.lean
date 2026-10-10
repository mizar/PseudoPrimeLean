/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import PseudoPrime.PrimeTest.Selfridge.FirstStop

/-!
# Coincidence of Selfridge stopping rules for PrimeTest

This file independently relates the pure `-1` stopping rule to the
factor-detecting `≠ 1` rule for a common candidate predicate.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Every pure-minus-one stop is a valid factor-detecting stop when `1 < n`.
For arbitrary candidate predicate `C`, Jacobi value `-1` excludes a gcd different from one
and hence excludes `n ∣ i`; it also excludes Jacobi value one. These facts prove inclusion
of the complete stopping sets. This establishes that the broader rule stops no later.
-/
theorem FirstStopNegOneSet.subset_firstStopNeOneSet {C : ℕ → Prop} {n : ℕ} (hn : 1 < n) :
    FirstStopNegOneSet C n ⊆ FirstStopNeOneSet C n := by
  intro i hi
  refine ⟨hi.1, ?_, ?_⟩
  · intro hndvd
    have hnatdvd : n ∣ (selfridgeD i).natAbs := by
      rw [selfridgeD_natAbs]
      exact hndvd
    have hgcdvd : n ∣ (selfridgeD i).gcd n := by
      rw [Int.gcd_eq_natAbs]
      exact Nat.dvd_gcd hnatdvd (dvd_refl n)
    have hgcdne : (selfridgeD i).gcd n ≠ 1 := by
      intro hgcd
      rw [hgcd] at hgcdvd
      have hnle : n ≤ 1 := Nat.le_of_dvd Nat.one_pos hgcdvd
      exact (not_le_of_gt hn) hnle
    let _ : NeZero n := ⟨Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one hn)⟩
    have hzero : jacobiSym (selfridgeD i) n = 0 := jacobiSym.eq_zero_iff_not_coprime.mpr hgcdne
    rw [hi.2] at hzero
    exact Int.noConfusion hzero
  · intro hone
    rw [hi.2] at hone
    exact Int.noConfusion hone

/--
Nonemptiness of the pure-minus-one stopping set implies nonemptiness of the broader set.
The premise `1 < n` lets the previous inclusion transport a witness for the same candidate
predicate `C`. This supplies the existence proof required to define the broader first stop.
-/
theorem firstStopNeOneSet_nonempty_of_negOne {C : ℕ → Prop} {n : ℕ} (hn : 1 < n)
    (hneg : (FirstStopNegOneSet C n).Nonempty) : (FirstStopNeOneSet C n).Nonempty :=
  hneg.mono (FirstStopNegOneSet.subset_firstStopNeOneSet hn)

/--
For a shared candidate predicate and `1 < n`, the broader first stop is no later than the pure stop.
Assume the pure-minus-one set is nonempty. Its least element belongs to the broader set by
inclusion, so broader leastness gives the inequality. No primality hypothesis is needed;
factor detection may make the inequality strict on composite inputs.
-/
theorem firstStopNeOne_le_firstStopNegOne_same_candidates {C : ℕ → Prop} {n : ℕ} (hn : 1 < n)
    (hneg : (FirstStopNegOneSet C n).Nonempty) :
    firstStopNeOne C n (firstStopNeOneSet_nonempty_of_negOne hn hneg) ≤
      firstStopNegOne C n hneg := by
  apply firstStopNeOne_le C n (firstStopNeOneSet_nonempty_of_negOne hn hneg)
  exact FirstStopNegOneSet.subset_firstStopNeOneSet hn (firstStopNegOne_mem C n hneg)

/--
The two stopping rules have the same least element for a prime modulus and common candidates.
Assume `Nat.Prime n` and nonemptiness of both sets; no bound relating `n` to the first stop
is required. The broader stop excludes divisibility by `n`, so its discriminant is coprime
and its Jacobi value is either one or minus one. Excluding one gives pure-stop membership;
leastness in both directions proves equality. This removes factor-detection divergence on primes.
-/
theorem firstStopNeOne_eq_firstStopNegOne_of_prime {C : ℕ → Prop} {n : ℕ} (hnprime : Nat.Prime n)
    (hneg : (FirstStopNegOneSet C n).Nonempty) (hne : (FirstStopNeOneSet C n).Nonempty) :
    firstStopNeOne C n hne = firstStopNegOne C n hneg := by
  have hn1 : 1 < n := hnprime.one_lt
  apply Nat.le_antisymm
  · exact
      firstStopNeOne_le C n hne
        (FirstStopNegOneSet.subset_firstStopNeOneSet hn1 (firstStopNegOne_mem C n hneg))
  · apply firstStopNegOne_le C n hneg
    have hstop := firstStopNeOne_mem C n hne
    have hcopNat : (selfridgeD (firstStopNeOne C n hne)).natAbs.Coprime n := by
      rw [selfridgeD_natAbs]
      exact (hnprime.coprime_iff_not_dvd.mpr hstop.2.1).symm
    have hcop : (selfridgeD (firstStopNeOne C n hne)).gcd n = 1 := by
      rw [Int.gcd_eq_natAbs]
      exact hcopNat.gcd_eq_one
    refine ⟨hstop.1, ?_⟩
    rcases jacobiSym.eq_one_or_neg_one hcop with hone | hnegone
    · exact False.elim (hstop.2.2 hone)
    · exact hnegone

/--
A pure-minus-one first stop cannot have magnitude equal to its prime modulus `n`.
The premise supplies `Nat.Prime n` and a nonempty stopping set. Equality would make `n`
divide the discriminant's absolute value, forcing Jacobi zero and contradicting stop membership.
This supports exclusion of the trivial full-modulus candidate in search comparisons.
-/
theorem firstStopNegOne_ne_input_of_prime {C : ℕ → Prop} {n : ℕ} (hnprime : Nat.Prime n)
    (hneg : (FirstStopNegOneSet C n).Nonempty) : firstStopNegOne C n hneg ≠ n := by
  intro heq
  have hstop := firstStopNegOne_mem C n hneg
  have hnatdvd : n ∣ (selfridgeD (firstStopNegOne C n hneg)).natAbs := by
    rw [selfridgeD_natAbs, heq]
  have hgcdvd : n ∣ (selfridgeD (firstStopNegOne C n hneg)).gcd n := by
    rw [Int.gcd_eq_natAbs]
    exact Nat.dvd_gcd hnatdvd (dvd_refl n)
  have hgcdne : (selfridgeD (firstStopNegOne C n hneg)).gcd n ≠ 1 := by
    intro hgcd
    rw [hgcd] at hgcdvd
    have hnle : n ≤ 1 := Nat.le_of_dvd Nat.one_pos hgcdvd
    exact (not_le_of_gt hnprime.two_le) hnle
  let _ : NeZero n := ⟨hnprime.ne_zero⟩
  have hzero : jacobiSym (selfridgeD (firstStopNegOne C n hneg)) n = 0 :=
    jacobiSym.eq_zero_iff_not_coprime.mpr hgcdne
  rw [hstop.2] at hzero
  exact Int.noConfusion hzero

/--
Mutual inclusion of two nonempty pure-minus-one stopping sets gives equal least stops.
The candidate predicates `C₁`, `C₂` need not be globally equal; only their stopping sets at
this `n` must include each other. Apply leastness to the transported least elements in both
directions. This compares searches after proving equality of their actual admissible stops.
-/
theorem firstStopNegOne_eq_of_mutual_subset {C₁ C₂ : ℕ → Prop} {n : ℕ}
    (h₁ : (FirstStopNegOneSet C₁ n).Nonempty) (h₂ : (FirstStopNegOneSet C₂ n).Nonempty)
    (h12 : FirstStopNegOneSet C₁ n ⊆ FirstStopNegOneSet C₂ n)
    (h21 : FirstStopNegOneSet C₂ n ⊆ FirstStopNegOneSet C₁ n) :
    firstStopNegOne C₁ n h₁ = firstStopNegOne C₂ n h₂ := by
  apply Nat.le_antisymm
  · exact firstStopNegOne_le C₁ n h₁ (h21 (firstStopNegOne_mem C₂ n h₂))
  · exact firstStopNegOne_le C₂ n h₂ (h12 (firstStopNegOne_mem C₁ n h₁))

/--
Mutual inclusion of two nonempty factor-detecting stopping sets gives equal least stops.
The hypotheses concern the stopping sets at the same modulus `n`, not equality of all
candidates. Their least elements give the two inequalities by membership and leastness.
Candidate-filter equivalence proofs use this to transfer the first stopping magnitude.
-/
theorem firstStopNeOne_eq_of_mutual_subset {C₁ C₂ : ℕ → Prop} {n : ℕ}
    (h₁ : (FirstStopNeOneSet C₁ n).Nonempty) (h₂ : (FirstStopNeOneSet C₂ n).Nonempty)
    (h12 : FirstStopNeOneSet C₁ n ⊆ FirstStopNeOneSet C₂ n)
    (h21 : FirstStopNeOneSet C₂ n ⊆ FirstStopNeOneSet C₁ n) :
    firstStopNeOne C₁ n h₁ = firstStopNeOne C₂ n h₂ := by
  apply Nat.le_antisymm
  · exact firstStopNeOne_le C₁ n h₁ (h21 (firstStopNeOne_mem C₂ n h₂))
  · exact firstStopNeOne_le C₂ n h₂ (h12 (firstStopNeOne_mem C₁ n h₁))

end PseudoPrime.PrimeTest
