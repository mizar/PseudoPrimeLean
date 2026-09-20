/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Algebra.Order.Ring.Abs
import PseudoPrime.NumberTheory.Jacobi.Basic
import PseudoPrime.PrimeTest.Selfridge.Witness

/-!
# Prime-factor extraction from composite Selfridge stops

This file supplies the common structural step in the two composite first-stop classifications.
A composite stopping candidate has a strictly smaller odd prime factor that already carries the
relevant Jacobi value.  The remaining classification isolates the exceptional factor `3`.
-/

namespace PseudoPrime.PrimeTest

namespace Internal

/--
A prime divisor of a positive nonprime natural number is strictly smaller than that number.
This local order lemma is used after extracting a prime factor from a Jacobi product.
-/
theorem prime_dvd_lt_of_not_prime {p i : ℕ} (hi : 0 < i) (hp : p.Prime) (hpdvd : p ∣ i)
    (hcomp : ¬i.Prime) : p < i := by
  have hple : p ≤ i := Nat.le_of_dvd hi hpdvd
  exact hple.lt_of_ne fun h ↦ hcomp (h ▸ hp)

/-- A positive divisor of `9` is `1`, `3`, or `9`. -/
theorem eq_one_or_three_or_nine_of_dvd_nine {n : ℕ} (hn : 0 < n) (hdvd : n ∣ 9) :
    n = 1 ∨ n = 3 ∨ n = 9 := by
  have hnle : n ≤ 9 := Nat.le_of_dvd (by norm_num only) hdvd
  interval_cases n <;> norm_num only at hn <;> norm_num only at hdvd <;> decide

/-- A positive divisor of `15` is `1`, `3`, `5`, or `15`. -/
theorem eq_one_or_three_or_five_or_fifteen_of_dvd_fifteen {n : ℕ} (hn : 0 < n) (hdvd : n ∣ 15) :
    n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 15 := by
  have hnle : n ≤ 15 := Nat.le_of_dvd (by norm_num only) hdvd
  interval_cases n <;> omega

/-- The fixed Jacobi value needed for the input `3` is not `1`. -/
theorem jacobiSym_five_three_ne_one : jacobiSym 5 3 ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym 3 5]
  intro h
  have hpow := legendreSym.eq_pow 3 5
  rw [h] at hpow
  have hne : (1 : ZMod 3) ≠ 5 := by
    intro hmod
    have hval := congrArg ZMod.val hmod
    change 1 = 2 at hval
    norm_num only at hval
  exact hne hpow

/-- The fixed Jacobi value needed for the input `5` is not `1`. -/
theorem jacobiSym_neg_seven_five_ne_one : jacobiSym (-7) 5 ≠ 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym 5 (-7)]
  intro h
  have hpow := legendreSym.eq_pow 5 (-7)
  rw [h] at hpow
  have hne : (1 : ZMod 5) ≠ 49 := by
    intro hmod
    have hval := congrArg ZMod.val hmod
    change 1 = 4 at hval
    norm_num only at hval
  exact hne hpow

/-- The fixed Jacobi value with non-coprime arguments `5` and `15` is zero. -/
theorem jacobiSym_five_fifteen_eq_zero : jacobiSym 5 15 = 0 := by
  rw [NumberTheory.jacobi_eq_zero_iff_not_coprime]
  norm_num only

end Internal

/--
A positive composite member of the factor-detecting stopping set has a strictly smaller odd
prime divisor at which `J(n | p) ≠ 1`.  Reciprocity converts the stopping value before the
prime-factor extraction lemma is applied.
-/
theorem exists_odd_prime_lt_of_composite_mem_firstStopNeOneSet {C : ℕ → Prop} {n i : ℕ}
    (hC : CandidateOdd C) (hn : Odd n) (hi : 0 < i) (hcomp : ¬i.Prime)
    (hstop : i ∈ FirstStopNeOneSet C n) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ i ∧ p < i ∧ jacobiSym n p ≠ 1 := by
  have hvalue : jacobiSym n i ≠ 1 := by
    rw [← jacobi_selfridgeD (hC hstop.1) hn]
    exact hstop.2.2
  obtain ⟨p, hp, hpdvd, hpvalue⟩ := NumberTheory.exists_prime_dvd_jacobi_ne_one hi.ne' hvalue
  exact
    ⟨p, hp, (hC hstop.1).of_dvd_nat hpdvd, hpdvd,
      Internal.prime_dvd_lt_of_not_prime hi hp hpdvd hcomp, hpvalue⟩

/--
A positive composite member of the pure `-1` stopping set has a strictly smaller odd prime
divisor at which `J(n | p) = -1`.  This is the common reduction used to show that only the
missing candidate prime `3` can cause a composite first-stop.
-/
theorem exists_odd_prime_lt_of_composite_mem_firstStopNegOneSet {C : ℕ → Prop} {n i : ℕ}
    (hC : CandidateOdd C) (hn : Odd n) (hi : 0 < i) (hcomp : ¬i.Prime)
    (hstop : i ∈ FirstStopNegOneSet C n) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ i ∧ p < i ∧ jacobiSym n p = -1 := by
  have hvalue : jacobiSym n i = -1 := by
    rw [← jacobi_selfridgeD (hC hstop.1) hn]
    exact hstop.2
  obtain ⟨p, hp, hpdvd, hpvalue⟩ := NumberTheory.exists_prime_dvd_jacobi_eq_neg_one hvalue
  exact
    ⟨p, hp, (hC hstop.1).of_dvd_nat hpdvd, hpdvd,
      Internal.prime_dvd_lt_of_not_prime hi hp hpdvd hcomp, hpvalue⟩

/--
A composite minimal `≠ 1` stop in the classical candidate sequence is divisible by `3`, and
`J(n | 3) ≠ 1`.  Any extracted prime factor at least `5` would itself be a valid earlier
classical candidate; divisibility by `n` is ruled out using the stop's factor-detection condition.
-/
theorem three_dvd_of_composite_minimal_classical_neOne {n i : ℕ} (hn : Odd n) (hi : 0 < i)
    (hcomp : ¬i.Prime) (hstop : i ∈ FirstStopNeOneSet isClassicalCandidate n)
    (hmin : ∀ j < i, j ∉ FirstStopNeOneSet isClassicalCandidate n) : 3 ∣ i ∧ jacobiSym n 3 ≠ 1 := by
  obtain ⟨p, hp, hpodd, hpdvd, hplt, hpvalue⟩ :=
    exists_odd_prime_lt_of_composite_mem_firstStopNeOneSet isClassicalCandidate_odd hn hi hcomp
      hstop
  have hp3 : p = 3 := by
    by_contra hpne
    have hp5 : 5 ≤ p := by
      have hp2 : 2 ≤ p := hp.two_le
      have hpmod : p % 2 = 1 := Nat.odd_iff.mp hpodd
      omega
    have hndvd : ¬n ∣ p := fun hnp ↦ hstop.2.1 (hnp.trans hpdvd)
    exact
      hmin p hplt
        ⟨⟨hp5, hpodd⟩, hndvd, by
          rw [jacobi_selfridgeD hpodd hn]
          exact hpvalue⟩
  subst p
  exact ⟨hpdvd, hpvalue⟩

/--
A composite minimal pure `-1` stop in the classical candidate sequence is divisible by `3`,
and `J(n | 3) = -1`.  A prime factor at least `5` would be an earlier classical stopping
candidate, contradicting minimality.
-/
theorem three_dvd_of_composite_minimal_classical_negOne {n i : ℕ} (hn : Odd n) (hi : 0 < i)
    (hcomp : ¬i.Prime) (hstop : i ∈ FirstStopNegOneSet isClassicalCandidate n)
    (hmin : ∀ j < i, j ∉ FirstStopNegOneSet isClassicalCandidate n) :
    3 ∣ i ∧ jacobiSym n 3 = -1 := by
  obtain ⟨p, hp, hpodd, hpdvd, hplt, hpvalue⟩ :=
    exists_odd_prime_lt_of_composite_mem_firstStopNegOneSet isClassicalCandidate_odd hn hi hcomp
      hstop
  have hp3 : p = 3 := by
    by_contra hpne
    have hp5 : 5 ≤ p := by
      have hp2 : 2 ≤ p := hp.two_le
      have hpmod : p % 2 = 1 := Nat.odd_iff.mp hpodd
      omega
    exact
      hmin p hplt
        ⟨⟨hp5, hpodd⟩, by
          rw [jacobi_selfridgeD hpodd hn]
          exact hpvalue⟩
  subst p
  exact ⟨hpdvd, hpvalue⟩

/--
If `J(n | 3) = 0` and `9` is valid for factor detection, every classical `≠ 1` first-stop is at
most `9`.  The square denominator gives `J(n | 9) = J(n | 3)^2 = 0`.
-/
theorem firstStopNeOne_le_nine_of_jacobi_three_eq_zero {n : ℕ} (hn : Odd n) (hndvd : ¬n ∣ 9)
    (h3 : jacobiSym n 3 = 0) (hs : (FirstStopNeOneSet isClassicalCandidate n).Nonempty) :
    firstStopNeOne isClassicalCandidate n hs ≤ 9 := by
  apply firstStopNeOne_le
  refine ⟨⟨by norm_num only, by decide⟩, hndvd, ?_⟩
  rw [jacobi_selfridgeD (by decide) hn, show 9 = 3 ^ 2 by norm_num only, jacobiSym.pow_right, h3]
  norm_num only

/--
If `J(n | 3) = -1`, `J(n | 5) = 1`, and `15` is valid for factor detection, every classical
`≠ 1` first-stop is at most `15`, since multiplicativity gives `J(n | 15) = -1`.
-/
theorem firstStopNeOne_le_fifteen_of_jacobi_three_eq_neg_one {n : ℕ} (hn : Odd n) (hndvd : ¬n ∣ 15)
    (h3 : jacobiSym n 3 = -1) (h5 : jacobiSym n 5 = 1)
    (hs : (FirstStopNeOneSet isClassicalCandidate n).Nonempty) :
    firstStopNeOne isClassicalCandidate n hs ≤ 15 := by
  apply firstStopNeOne_le
  refine ⟨⟨by norm_num only, by decide⟩, hndvd, ?_⟩
  rw [jacobi_selfridgeD (by decide) hn, show 15 = 3 * 5 by norm_num only, jacobiSym.mul_right, h3,
    h5]
  norm_num only

/--
Subject to validity of the two exceptional composite candidates, a composite classical `≠ 1`
first-stop is exactly `9` or `15`.  The common extraction theorem forces the bad prime factor
to be `3`; Jacobi trichotomy then selects the candidate `9` or `15`.
-/
theorem composite_minimal_classical_neOne_eq_nine_or_fifteen_of_not_dvd {n i : ℕ} (hn : Odd n)
    (hi : 0 < i) (hcomp : ¬i.Prime) (hstop : i ∈ FirstStopNeOneSet isClassicalCandidate n)
    (hmin : ∀ j < i, j ∉ FirstStopNeOneSet isClassicalCandidate n) (hndvd9 : ¬n ∣ 9)
    (hndvd15 : ¬n ∣ 15) : i = 9 ∨ i = 15 := by
  obtain ⟨h3dvd, h3ne⟩ := three_dvd_of_composite_minimal_classical_neOne hn hi hcomp hstop hmin
  have hi_ge : 5 ≤ i := hstop.1.1
  have hle : i ≤ 15 := by
    rcases jacobiSym.trichotomy (n : ℤ) 3 with h3 | h3 | h3
    · have h9mem : 9 ∈ FirstStopNeOneSet isClassicalCandidate n := by
        exact
          ⟨⟨by norm_num only, by decide⟩, hndvd9, by
            rw [jacobi_selfridgeD (by decide) hn, show 9 = 3 ^ 2 by norm_num only,
              jacobiSym.pow_right, h3]
            norm_num only⟩
      have hi9 : i ≤ 9 := by
        by_contra hle9
        exact hmin 9 (Nat.lt_of_not_ge hle9) h9mem
      omega
    · exact False.elim (h3ne h3)
    · have hndvd5 : ¬n ∣ 5 := fun h ↦ hndvd15 (h.trans (by norm_num only))
      have hi5 : i ≠ 5 := by
        intro hieq
        subst i
        exact hcomp (by decide)
      have h5lt : 5 < i := by omega
      have h5 : jacobiSym n 5 = 1 := by
        rcases jacobiSym.trichotomy (n : ℤ) 5 with h50 | h51 | h5m
        · exact
            False.elim <|
              hmin 5 h5lt
                ⟨⟨by norm_num only, by decide⟩, hndvd5, by
                  rw [jacobi_selfridgeD (by decide) hn, h50]; norm_num only⟩
        · exact h51
        · exact
            False.elim <|
              hmin 5 h5lt
                ⟨⟨by norm_num only, by decide⟩, hndvd5, by
                  rw [jacobi_selfridgeD (by decide) hn, h5m]; norm_num only⟩
      have h15mem : 15 ∈ FirstStopNeOneSet isClassicalCandidate n := by
        exact
          ⟨⟨by norm_num only, by decide⟩, hndvd15, by
            rw [jacobi_selfridgeD (by decide) hn, show 15 = 3 * 5 by norm_num only,
              jacobiSym.mul_right, h3, h5]
            norm_num only⟩
      by_contra hle
      exact hmin 15 (Nat.lt_of_not_ge hle) h15mem
  have himod : i % 2 = 1 := Nat.odd_iff.mp hstop.1.2
  obtain ⟨k, rfl⟩ := h3dvd
  omega

/--
For a positive nonsquare input, `9` cannot divide the input of a composite minimal classical
`≠ 1` stop.  The only nonsquare positive divisor of `9` is `3`, where the prime candidate `5`
already stops and contradicts minimality.
-/
theorem not_dvd_nine_of_nonsquare_composite_minimal_classical_neOne {n i : ℕ} (hnpos : 0 < n)
    (hns : ¬IsSquare n) (hcomp : ¬i.Prime) (hstop : i ∈ FirstStopNeOneSet isClassicalCandidate n)
    (hmin : ∀ j < i, j ∉ FirstStopNeOneSet isClassicalCandidate n) : ¬n ∣ 9 := by
  intro hdvd
  rcases Internal.eq_one_or_three_or_nine_of_dvd_nine hnpos hdvd with rfl | rfl | rfl
  · exact hns ⟨1, by norm_num only⟩
  · have h5lt : 5 < i := by
      have hi5le : 5 ≤ i := hstop.1.1
      have hi5 : i ≠ 5 := fun h ↦ hcomp (h ▸ by decide)
      omega
    exact
      hmin 5 h5lt
        (by
          refine ⟨⟨by norm_num only, by decide⟩, by norm_num only, ?_⟩
          exact Internal.jacobiSym_five_three_ne_one)
  · exact hns ⟨3, by norm_num only⟩

/--
For a positive nonsquare input, `15` cannot divide the input of a composite minimal classical
`≠ 1` stop.  Its nonsquare divisors `3`, `5`, and `15` have an earlier concrete prime stop at
`5`, `7`, and `5`, respectively.
-/
theorem not_dvd_fifteen_of_nonsquare_composite_minimal_classical_neOne {n i : ℕ} (hnpos : 0 < n)
    (hns : ¬IsSquare n) (hcomp : ¬i.Prime) (hstop : i ∈ FirstStopNeOneSet isClassicalCandidate n)
    (hmin : ∀ j < i, j ∉ FirstStopNeOneSet isClassicalCandidate n) : ¬n ∣ 15 := by
  intro hdvd
  rcases Internal.eq_one_or_three_or_five_or_fifteen_of_dvd_fifteen hnpos hdvd with rfl | rfl |
    rfl | rfl
  · exact hns ⟨1, by norm_num only⟩
  · have h5lt : 5 < i := by
      have hi5le : 5 ≤ i := hstop.1.1
      have hi5 : i ≠ 5 := fun h ↦ hcomp (h ▸ by decide)
      omega
    exact
      hmin 5 h5lt
        (by
          refine ⟨⟨by norm_num only, by decide⟩, by norm_num only, ?_⟩
          exact Internal.jacobiSym_five_three_ne_one)
  · have h7lt : 7 < i := by
      have hi5le : 5 ≤ i := hstop.1.1
      have hi5 : i ≠ 5 := fun h ↦ hcomp (h ▸ by decide)
      have hi7 : i ≠ 7 := fun h ↦ hcomp (h ▸ by decide)
      have himod : i % 2 = 1 := Nat.odd_iff.mp hstop.1.2
      omega
    exact
      hmin 7 h7lt
        (by
          refine ⟨⟨by norm_num only, by decide⟩, by norm_num only, ?_⟩
          exact Internal.jacobiSym_neg_seven_five_ne_one)
  · have h5lt : 5 < i := by
      have hi5le : 5 ≤ i := hstop.1.1
      have hi5 : i ≠ 5 := fun h ↦ hcomp (h ▸ by decide)
      omega
    exact
      hmin 5 h5lt
        (by
          refine ⟨⟨by norm_num only, by decide⟩, by norm_num only, ?_⟩
          change jacobiSym 5 15 ≠ 1
          rw [Internal.jacobiSym_five_fifteen_eq_zero]
          norm_num only)

/--
A composite minimal classical `≠ 1` stop for a positive odd nonsquare input is exactly `9` or
`15`.  Positivity and nonsquareness make both exceptional composite candidates valid for
factor detection, removing the auxiliary divisibility assumptions from the classification.
-/
theorem composite_minimal_classical_neOne_eq_nine_or_fifteen {n i : ℕ} (hnpos : 0 < n) (hn : Odd n)
    (hns : ¬IsSquare n) (hi : 0 < i) (hcomp : ¬i.Prime)
    (hstop : i ∈ FirstStopNeOneSet isClassicalCandidate n)
    (hmin : ∀ j < i, j ∉ FirstStopNeOneSet isClassicalCandidate n) : i = 9 ∨ i = 15 := by
  apply composite_minimal_classical_neOne_eq_nine_or_fifteen_of_not_dvd hn hi hcomp hstop hmin
  · exact not_dvd_nine_of_nonsquare_composite_minimal_classical_neOne hnpos hns hcomp hstop hmin
  · exact not_dvd_fifteen_of_nonsquare_composite_minimal_classical_neOne hnpos hns hcomp hstop hmin

/--
If the Jacobi values at `3` and `5` are `-1` and `1`, respectively, candidate `15` is a pure
`-1` stop.  Minimality therefore bounds the classical first-stop by `15`.
-/
theorem minimal_classical_negOne_le_fifteen {n i : ℕ} (hn : Odd n) (h3 : jacobiSym n 3 = -1)
    (h5 : jacobiSym n 5 = 1) (hmin : ∀ j < i, j ∉ FirstStopNegOneSet isClassicalCandidate n) :
    i ≤ 15 := by
  by_contra hle
  apply hmin 15 (Nat.lt_of_not_ge hle)
  refine ⟨⟨by norm_num only, by decide⟩, ?_⟩
  rw [jacobi_selfridgeD (by decide) hn, show 15 = 3 * 5 by norm_num only, jacobiSym.mul_right, h3,
    h5]
  norm_num only

/--
If the Jacobi values at `3` and `7` are `-1` and `1`, respectively, candidate `21` is a pure
`-1` stop.  Minimality therefore bounds the classical first-stop by `21`.
-/
theorem minimal_classical_negOne_le_twenty_one {n i : ℕ} (hn : Odd n) (h3 : jacobiSym n 3 = -1)
    (h7 : jacobiSym n 7 = 1) (hmin : ∀ j < i, j ∉ FirstStopNegOneSet isClassicalCandidate n) :
    i ≤ 21 := by
  by_contra hle
  apply hmin 21 (Nat.lt_of_not_ge hle)
  refine ⟨⟨by norm_num only, by decide⟩, ?_⟩
  rw [jacobi_selfridgeD (by decide) hn, show 21 = 3 * 7 by norm_num only, jacobiSym.mul_right, h3,
    h7]
  norm_num only

/--
If `J(n | 3) = -1`, candidate `27` is a pure `-1` stop because its denominator is the third
power of `3`.  Minimality therefore bounds the classical first-stop by `27`.
-/
theorem minimal_classical_negOne_le_twenty_seven {n i : ℕ} (hn : Odd n) (h3 : jacobiSym n 3 = -1)
    (hmin : ∀ j < i, j ∉ FirstStopNegOneSet isClassicalCandidate n) : i ≤ 27 := by
  by_contra hle
  apply hmin 27 (Nat.lt_of_not_ge hle)
  refine ⟨⟨by norm_num only, by decide⟩, ?_⟩
  rw [jacobi_selfridgeD (by decide) hn, show 27 = 3 ^ 3 by norm_num only, jacobiSym.pow_right, h3]
  norm_num only

/--
A composite minimal pure `-1` stop in the classical candidate sequence is exactly `15`, `21`,
or `27`.  The extracted factor `3` supplies value `-1`; trichotomy at `5` and then at `7`
selects the first available composite product or the fallback cube `27`.
-/
theorem composite_minimal_classical_negOne_eq_fifteen_or_twenty_one_or_twenty_seven {n i : ℕ}
    (hn : Odd n) (hi : 0 < i) (hcomp : ¬i.Prime)
    (hstop : i ∈ FirstStopNegOneSet isClassicalCandidate n)
    (hmin : ∀ j < i, j ∉ FirstStopNegOneSet isClassicalCandidate n) : i = 15 ∨ i = 21 ∨ i = 27 := by
  obtain ⟨h3dvd, h3⟩ := three_dvd_of_composite_minimal_classical_negOne hn hi hcomp hstop hmin
  have hi_ge : 5 ≤ i := hstop.1.1
  have hi5 : i ≠ 5 := fun h ↦ hcomp (h ▸ by decide)
  have h5lt : 5 < i := by omega
  have hi9 : i ≠ 9 := by
    intro hieq
    subst i
    have hvalue := hstop.2
    rw [jacobi_selfridgeD (by decide) hn, show 9 = 3 ^ 2 by norm_num only, jacobiSym.pow_right,
      h3] at hvalue
    norm_num only at hvalue
  rcases jacobiSym.trichotomy (n : ℤ) 5 with h50 | h51 | h5m
  · have hi15 : i ≠ 15 := by
      intro hieq
      subst i
      have hvalue := hstop.2
      rw [jacobi_selfridgeD (by decide) hn, show 15 = 3 * 5 by norm_num only, jacobiSym.mul_right,
        h3, h50] at hvalue
      norm_num only at hvalue
    rcases jacobiSym.trichotomy (n : ℤ) 7 with h70 | h71 | h7m
    · have hle := minimal_classical_negOne_le_twenty_seven hn h3 hmin
      have hi21 : i ≠ 21 := by
        intro hieq
        subst i
        have hvalue := hstop.2
        rw [jacobi_selfridgeD (by decide) hn, show 21 = 3 * 7 by norm_num only, jacobiSym.mul_right,
          h3, h70] at hvalue
        norm_num only at hvalue
      have himod : i % 2 = 1 := Nat.odd_iff.mp hstop.1.2
      obtain ⟨k, rfl⟩ := h3dvd
      omega
    · have hle := minimal_classical_negOne_le_twenty_one hn h3 h71 hmin
      have himod : i % 2 = 1 := Nat.odd_iff.mp hstop.1.2
      obtain ⟨k, rfl⟩ := h3dvd
      omega
    · have hi7 : i ≠ 7 := fun h ↦ hcomp (h ▸ by decide)
      have himod : i % 2 = 1 := Nat.odd_iff.mp hstop.1.2
      have h7lt : 7 < i := by omega
      exact
        False.elim <|
          hmin 7 h7lt
            ⟨⟨by norm_num only, by decide⟩, by
              rw [jacobi_selfridgeD (by decide) hn]
              exact h7m⟩
  · have hle := minimal_classical_negOne_le_fifteen hn h3 h51 hmin
    have himod : i % 2 = 1 := Nat.odd_iff.mp hstop.1.2
    obtain ⟨k, rfl⟩ := h3dvd
    omega
  · exact
      False.elim <|
        hmin 5 h5lt
          ⟨⟨by norm_num only, by decide⟩, by
            rw [jacobi_selfridgeD (by decide) hn]
            exact h5m⟩

/--
If `J(n | 3) = -1` and `J(n | 5) = 0`, then `n` is divisible by `5` but not by `3`, so its
greatest common divisor with `15` is exactly `5`.
-/
theorem gcd_fifteen_eq_five_of_jacobi_three_neg_one_five_zero {n : ℕ} (h3 : jacobiSym n 3 = -1)
    (h5 : jacobiSym n 5 = 0) : n.gcd 15 = 5 := by
  have hfive : 5 ∣ n := by
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hleg : legendreSym 5 n = 0 := by
      rw [jacobiSym.legendreSym.to_jacobiSym]
      exact h5
    have hz : ((n : ℤ) : ZMod 5) = 0 := (legendreSym.eq_zero_iff 5 n).mp hleg
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (n : ℤ) 5).mp hz
  have hthree : ¬3 ∣ n := by
    intro hdvd
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hz : ((n : ℤ) : ZMod 3) = 0 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd (n : ℤ) 3).mpr
      exact_mod_cast hdvd
    have hleg : legendreSym 3 n = 0 := (legendreSym.eq_zero_iff 3 n).mpr hz
    have hjac : jacobiSym n 3 = 0 := by
      rw [← jacobiSym.legendreSym.to_jacobiSym]
      exact hleg
    rw [hjac] at h3
    norm_num only at h3
  have hfivedvdgcd : 5 ∣ n.gcd 15 := (Nat.dvd_gcd hfive (by norm_num only))
  have hgcdpos : 0 < n.gcd 15 := Nat.gcd_pos_of_pos_right n (by norm_num only)
  have hgcddiv : n.gcd 15 ∣ 15 := Nat.gcd_dvd_right n 15
  rcases Internal.eq_one_or_three_or_five_or_fifteen_of_dvd_fifteen hgcdpos hgcddiv with h | h | h |
    h
  · rw [h] at hfivedvdgcd
    norm_num only at hfivedvdgcd
  · rw [h] at hfivedvdgcd
    norm_num only at hfivedvdgcd
  · exact h
  · have hthreegcd : 3 ∣ n.gcd 15 := by
      rw [h]
      norm_num only
    exact False.elim (hthree (hthreegcd.trans (Nat.gcd_dvd_left n 15)))

end PseudoPrime.PrimeTest
