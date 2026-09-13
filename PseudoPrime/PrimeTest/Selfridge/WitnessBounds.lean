/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PrimeTest.Selfridge.Composite
import PseudoPrime.NumberTheory.JacobiWitness.Smaller

/-!
# Pointwise bounds between prime witnesses and classical Selfridge stops

This file compares least odd-prime Jacobi witnesses with classical first stops. The pure
`-1` comparison is unconditional once both least elements exist.  The factor-detecting upper
bound additionally uses the canonical smaller-witness theorem from `NumberTheory`.
-/

namespace PseudoPrime.PrimeTest

/--
The least odd-prime `≠ 1` witness is no larger than the classical factor-detecting first-stop.
For a prime stop this is the direct correspondence; for a composite stop, prime-factor
extraction supplies a smaller odd-prime witness.
-/
theorem primeNeOneWitness_le_classicalFirstStop {n : ℕ} (hn : Odd n)
    (hw : (PrimeNeOneWitnessSet n).Nonempty)
    (hs : (FirstStopNeOneSet isClassicalCandidate n).Nonempty) :
    primeNeOneWitness n hw ≤ firstStopNeOne isClassicalCandidate n hs := by
  by_cases hp : (firstStopNeOne isClassicalCandidate n hs).Prime
  · exact primeNeOneWitness_le_firstStopNeOne_of_prime isClassicalCandidate_odd hn hw hs hp
  · have hstop := firstStopNeOne_mem isClassicalCandidate n hs
    have hi : 0 < firstStopNeOne isClassicalCandidate n hs := by
      have hi5 := hstop.1.1
      omega
    obtain ⟨p, hprime, hodd, _, hplt, hvalue⟩ :=
      exists_odd_prime_lt_of_composite_mem_firstStopNeOneSet isClassicalCandidate_odd hn hi hp hstop
    exact (primeNeOneWitness_le n hw (p := p) ⟨hprime, hodd, hvalue⟩).trans hplt.le

/--
The least odd-prime `-1` witness is no larger than the classical pure `-1` first-stop.  A
composite first-stop yields a smaller prime witness by the common factor-extraction theorem.
-/
theorem primeNegOneWitness_le_classicalFirstStop {n : ℕ} (hn : Odd n)
    (hw : (PrimeNegOneWitnessSet n).Nonempty)
    (hs : (FirstStopNegOneSet isClassicalCandidate n).Nonempty) :
    primeNegOneWitness n hw ≤ firstStopNegOne isClassicalCandidate n hs := by
  by_cases hp : (firstStopNegOne isClassicalCandidate n hs).Prime
  · exact primeNegOneWitness_le_firstStopNegOne_of_prime isClassicalCandidate_odd hn hw hs hp
  · have hstop := firstStopNegOne_mem isClassicalCandidate n hs
    have hi : 0 < firstStopNegOne isClassicalCandidate n hs := by
      have hi5 := hstop.1.1
      omega
    obtain ⟨p, hprime, hodd, _, hplt, hvalue⟩ :=
      exists_odd_prime_lt_of_composite_mem_firstStopNegOneSet isClassicalCandidate_odd hn hi hp
        hstop
    exact (primeNegOneWitness_le n hw (p := p) ⟨hprime, hodd, hvalue⟩).trans hplt.le

/--
The classical pure `-1` first-stop is at most the larger of `27` and the least odd-prime
`-1` witness.  If that witness is at least `5`, it is itself a classical candidate; if it is
`3`, multiplicativity makes candidate `27` a stopping point.
-/
theorem classicalFirstStopNegOne_le_max_twenty_seven_primeWitness {n : ℕ} (hn : Odd n)
    (hw : (PrimeNegOneWitnessSet n).Nonempty)
    (hs : (FirstStopNegOneSet isClassicalCandidate n).Nonempty) :
    firstStopNegOne isClassicalCandidate n hs ≤ max 27 (primeNegOneWitness n hw) := by
  have hp := primeNegOneWitness_mem n hw
  by_cases hp3 : primeNegOneWitness n hw = 3
  · have h3 : jacobiSym n 3 = -1 := by
      rw [← hp3]
      exact hp.2.2
    have hle : firstStopNegOne isClassicalCandidate n hs ≤ 27 := by
      apply firstStopNegOne_le
      refine ⟨⟨by norm_num only, by decide⟩, ?_⟩
      rw [jacobi_selfridgeD (by decide) hn, show 27 = 3 ^ 3 by norm_num only, jacobiSym.pow_right,
        h3]
      norm_num only
    exact hle.trans (Nat.le_max_left 27 (primeNegOneWitness n hw))
  · have hp5 : 5 ≤ primeNegOneWitness n hw := by
      have hp2 := hp.1.two_le
      have hpmod : primeNegOneWitness n hw % 2 = 1 := Nat.odd_iff.mp hp.2.1
      omega
    have hle : firstStopNegOne isClassicalCandidate n hs ≤ primeNegOneWitness n hw :=
      firstStopNegOne_le_primeNegOneWitness hn hw hs ⟨hp5, hp.2.1⟩
    exact hle.trans (Nat.le_max_right 27 (primeNegOneWitness n hw))

/--
Combined pointwise pure `-1` comparison: the classical first-stop lies between the least prime
witness and the maximum of that witness with the exceptional bound `27`.
-/
theorem primeNegOneWitness_le_classicalFirstStop_le_max {n : ℕ} (hn : Odd n)
    (hw : (PrimeNegOneWitnessSet n).Nonempty)
    (hs : (FirstStopNegOneSet isClassicalCandidate n).Nonempty) :
    primeNegOneWitness n hw ≤ firstStopNegOne isClassicalCandidate n hs ∧
      firstStopNegOne isClassicalCandidate n hs ≤ max 27 (primeNegOneWitness n hw) := by
  exact
    ⟨primeNegOneWitness_le_classicalFirstStop hn hw hs,
      classicalFirstStopNegOne_le_max_twenty_seven_primeWitness hn hw hs⟩

/--
For a nonsquare input, a least `≠ 1` prime witness above `3` is not divisible by the input.
Divisibility would force the input to equal that prime; the smaller-witness theorem would
then produce a smaller prime witness, contradicting minimality.
-/
theorem not_dvd_primeNeOneWitness_of_three_lt {n : ℕ} (hns : ¬IsSquare n)
    (hw : (PrimeNeOneWitnessSet n).Nonempty) (hp3 : 3 < primeNeOneWitness n hw) :
    ¬n ∣ primeNeOneWitness n hw := by
  intro hdiv
  have hp := primeNeOneWitness_mem n hw
  rcases hp.1.eq_one_or_self_of_dvd n hdiv with hn1 | hnp
  · exact hns ⟨1, by omega⟩
  · obtain ⟨q, hqprime, hqodd, hqlt, hqvalue⟩ :=
      NumberTheory.primeHasSmallerNegOneWitness hp.1 hp3
    have hqmem : q ∈ PrimeNeOneWitnessSet n := by
      exact
        ⟨hqprime, hqodd, by
          rw [hnp, hqvalue]; norm_num only⟩
    exact (Nat.not_le_of_lt hqlt) (primeNeOneWitness_le n hw hqmem)

/--
For an odd nonsquare input, if the least `≠ 1` prime witness is above `3`, the classical
factor-detecting first-stop is no larger than that witness itself. The proof uses the
smaller-witness theorem to exclude divisibility by the input.
-/
theorem classicalFirstStopNeOne_le_primeWitness_of_three_lt {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hw : (PrimeNeOneWitnessSet n).Nonempty)
    (hs : (FirstStopNeOneSet isClassicalCandidate n).Nonempty) (hp3 : 3 < primeNeOneWitness n hw) :
    firstStopNeOne isClassicalCandidate n hs ≤ primeNeOneWitness n hw := by
  have hp := primeNeOneWitness_mem n hw
  apply firstStopNeOne_le_primeNeOneWitness hn hw hs
  · have hpmod : primeNeOneWitness n hw % 2 = 1 := Nat.odd_iff.mp hp.2.1
    exact ⟨by omega, hp.2.1⟩
  · exact not_dvd_primeNeOneWitness_of_three_lt hns hw hp3

/--
Equivalent convenient form of the preceding bound: for an odd-prime witness, being different
from `3` forces it above `3`.
-/
theorem classicalFirstStopNeOne_le_primeWitness_of_ne_three {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hw : (PrimeNeOneWitnessSet n).Nonempty)
    (hs : (FirstStopNeOneSet isClassicalCandidate n).Nonempty) (hp3 : primeNeOneWitness n hw ≠ 3) :
    firstStopNeOne isClassicalCandidate n hs ≤ primeNeOneWitness n hw := by
  have hp := primeNeOneWitness_mem n hw
  have hp2 := hp.1.two_le
  have hpmod : primeNeOneWitness n hw % 2 = 1 := Nat.odd_iff.mp hp.2.1
  apply classicalFirstStopNeOne_le_primeWitness_of_three_lt hn hns hw hs
  omega

/--
If the least odd-prime `≠ 1` witness is `3`, the classical factor-detecting first-stop is at
most `15`.  Divisibility exceptions among `5`, `9`, and `15` reduce to the positive divisors of
these fixed numbers; nonsquareness or the concrete candidate `7` handles every exception.
-/
theorem classicalFirstStopNeOne_le_fifteen_of_primeWitness_eq_three {n : ℕ} (hnpos : 0 < n)
    (hn : Odd n) (hns : ¬IsSquare n) (hw : (PrimeNeOneWitnessSet n).Nonempty)
    (hs : (FirstStopNeOneSet isClassicalCandidate n).Nonempty) (hp3 : primeNeOneWitness n hw = 3) :
    firstStopNeOne isClassicalCandidate n hs ≤ 15 := by
  have hp := primeNeOneWitness_mem n hw
  have h3ne : jacobiSym n 3 ≠ 1 := by
    rw [← hp3]
    exact hp.2.2
  rcases jacobiSym.trichotomy (n : ℤ) 3 with h30 | h31 | h3m
  · by_cases hndvd9 : n ∣ 9
    · rcases Internal.eq_one_or_three_or_nine_of_dvd_nine hnpos hndvd9 with rfl | rfl | rfl
      · exact False.elim (hns ⟨1, by norm_num only⟩)
      · exact
          (firstStopNeOne_le isClassicalCandidate 3 hs (i := 5) <| by
                refine ⟨⟨by norm_num only, by decide⟩, by norm_num only, ?_⟩
                exact Internal.jacobiSym_five_three_ne_one).trans
            (by norm_num only)
      · exact False.elim (hns ⟨3, by norm_num only⟩)
    · exact
        (firstStopNeOne_le_nine_of_jacobi_three_eq_zero hn hndvd9 h30 hs).trans (by norm_num only)
  · exact False.elim (h3ne h31)
  · rcases jacobiSym.trichotomy (n : ℤ) 5 with h50 | h51 | h5m
    · by_cases hndvd5 : n ∣ 5
      · rcases (Nat.prime_five.eq_one_or_self_of_dvd n hndvd5) with rfl | rfl
        · exact False.elim (hns ⟨1, by norm_num only⟩)
        · exact
            (firstStopNeOne_le isClassicalCandidate 5 hs (i := 7) <| by
                  refine ⟨⟨by norm_num only, by decide⟩, by norm_num only, ?_⟩
                  exact Internal.jacobiSym_neg_seven_five_ne_one).trans
              (by norm_num only)
      · exact
          (firstStopNeOne_le isClassicalCandidate n hs <| by
                refine ⟨⟨by norm_num only, by decide⟩, hndvd5, ?_⟩
                rw [jacobi_selfridgeD (by decide) hn, h50]
                norm_num only).trans
            (by norm_num only)
    · by_cases hndvd15 : n ∣ 15
      · rcases Internal.eq_one_or_three_or_five_or_fifteen_of_dvd_fifteen hnpos hndvd15 with rfl |
          rfl | rfl | rfl
        · exact False.elim (hns ⟨1, by norm_num only⟩)
        · have hz : jacobiSym (3 : ℤ) 3 = 0 := by
            rw [NumberTheory.jacobi_eq_zero_iff_not_coprime]
            norm_num only
          change jacobiSym (3 : ℤ) 3 = -1 at h3m
          rw [hz] at h3m
          norm_num only at h3m
        · have hz : jacobiSym (5 : ℤ) 5 = 0 := by
            rw [NumberTheory.jacobi_eq_zero_iff_not_coprime]
            norm_num only
          change jacobiSym (5 : ℤ) 5 = 1 at h51
          rw [hz] at h51
          norm_num only at h51
        · have hz : jacobiSym (15 : ℤ) 5 = 0 := by
            rw [NumberTheory.jacobi_eq_zero_iff_not_coprime]
            norm_num only
          change jacobiSym (15 : ℤ) 5 = 1 at h51
          rw [hz] at h51
          norm_num only at h51
      · exact firstStopNeOne_le_fifteen_of_jacobi_three_eq_neg_one hn hndvd15 h3m h51 hs
    · by_cases hndvd5 : n ∣ 5
      · rcases (Nat.prime_five.eq_one_or_self_of_dvd n hndvd5) with rfl | rfl
        · exact False.elim (hns ⟨1, by norm_num only⟩)
        · exact
            (firstStopNeOne_le isClassicalCandidate 5 hs (i := 7) <| by
                  refine ⟨⟨by norm_num only, by decide⟩, by norm_num only, ?_⟩
                  exact Internal.jacobiSym_neg_seven_five_ne_one).trans
              (by norm_num only)
      · exact
          (firstStopNeOne_le isClassicalCandidate n hs <| by
                refine ⟨⟨by norm_num only, by decide⟩, hndvd5, ?_⟩
                rw [jacobi_selfridgeD (by decide) hn, h5m]
                norm_num only).trans
            (by norm_num only)

/-- The classical factor-detecting first-stop is at most the maximum of `15` and the least
odd-prime `≠ 1` witness.
-/
theorem classicalFirstStopNeOne_le_max_fifteen_primeWitness {n : ℕ} (hnpos : 0 < n) (hn : Odd n)
    (hns : ¬IsSquare n) (hw : (PrimeNeOneWitnessSet n).Nonempty)
    (hs : (FirstStopNeOneSet isClassicalCandidate n).Nonempty) :
    firstStopNeOne isClassicalCandidate n hs ≤ max 15 (primeNeOneWitness n hw) := by
  by_cases hp3 : primeNeOneWitness n hw = 3
  · exact
      (classicalFirstStopNeOne_le_fifteen_of_primeWitness_eq_three hnpos hn hns hw hs hp3).trans
        (Nat.le_max_left 15 (primeNeOneWitness n hw))
  · exact
      (classicalFirstStopNeOne_le_primeWitness_of_ne_three hn hns hw hs hp3).trans
        (Nat.le_max_right 15 (primeNeOneWitness n hw))

/-- Combined conditional pointwise comparison for the classical factor-detecting scan. -/
theorem primeNeOneWitness_le_classicalFirstStop_le_max {n : ℕ} (hnpos : 0 < n) (hn : Odd n)
    (hns : ¬IsSquare n) (hw : (PrimeNeOneWitnessSet n).Nonempty)
    (hs : (FirstStopNeOneSet isClassicalCandidate n).Nonempty) :
    primeNeOneWitness n hw ≤ firstStopNeOne isClassicalCandidate n hs ∧
      firstStopNeOne isClassicalCandidate n hs ≤ max 15 (primeNeOneWitness n hw) := by
  exact
    ⟨primeNeOneWitness_le_classicalFirstStop hn hw hs,
      classicalFirstStopNeOne_le_max_fifteen_primeWitness hnpos hn hns hw hs⟩

/-- The previous factor-detecting comparison with the proved smaller-witness theorem supplied. -/
theorem primeNeOneWitness_le_classicalFirstStop_le_max_unconditional {n : ℕ} (hnpos : 0 < n)
    (hn : Odd n) (hns : ¬IsSquare n) (hw : (PrimeNeOneWitnessSet n).Nonempty)
    (hs : (FirstStopNeOneSet isClassicalCandidate n).Nonempty) :
    primeNeOneWitness n hw ≤ firstStopNeOne isClassicalCandidate n hs ∧
      firstStopNeOne isClassicalCandidate n hs ≤ max 15 (primeNeOneWitness n hw) := by
  exact primeNeOneWitness_le_classicalFirstStop_le_max hnpos hn hns hw hs

/--
Assumptions: `n` is odd, nonsquare, and `3 < n`; `hw` is nonemptiness of the neutral witness
set.
Conclusion: the least odd-prime witness with Jacobi value different from `1` is strictly below `n`.
Proof: obtain the smaller pure `-1` witness from the canonical NumberTheory theorem; its value is
also different from `1`, so witness minimality gives the strict bound.
Role: supplies the direct `g_{\ne1}` finite argument.
-/
theorem primeNeOneWitness_lt_of_odd_nonsquare_of_three_lt {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hn3 : 3 < n) (hw : (PrimeNeOneWitnessSet n).Nonempty) : primeNeOneWitness n hw < n := by
  obtain ⟨q, hqprime, hqodd, hq_lt, hqvalue⟩ :=
    NumberTheory.oddNonsquareHasSmallerNegOneWitness hn hn3 hns
  have hqmem : q ∈ PrimeNeOneWitnessSet n := by
    exact
      ⟨hqprime, hqodd, by
        rw [hqvalue]; norm_num only⟩
  exact (primeNeOneWitness_le n hw hqmem).trans_lt hq_lt

/--
Assumptions: `n` is odd, nonsquare, and `15 < n`; both the neutral witness set and classical
factor-detecting stopping set are nonempty.
Conclusion: the classical factor-detecting first stop is strictly below `n`.
Proof: the exceptional least witness `3` is handled by the established bound `15`; otherwise the
canonical smaller-witness bound makes the least witness a valid classical candidate below `n`.
Role: provides the `g_{\ne1}` analogue of the direct finite Selfridge improvement.
-/
theorem classicalFirstStopNeOne_lt_of_odd_nonsquare_of_fifteen_lt {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hn15 : 15 < n) (hw : (PrimeNeOneWitnessSet n).Nonempty)
    (hs : (FirstStopNeOneSet isClassicalCandidate n).Nonempty) :
    firstStopNeOne isClassicalCandidate n hs < n := by
  have hp := primeNeOneWitness_mem n hw
  by_cases hp3 : primeNeOneWitness n hw = 3
  · exact
      (classicalFirstStopNeOne_le_fifteen_of_primeWitness_eq_three (Odd.pos hn) hn hns hw hs
            hp3).trans_lt
        hn15
  · have hn3 : 3 < n := by
      by_contra hn3
      have hnle : n ≤ 3 := by omega
      have : n = 3 := by
        obtain ⟨k, hk⟩ := hn
        omega
      subst n
      have hp5 := hp.1.two_le
      have hpmod := Nat.odd_iff.mp hp.2.1
      omega
    have hp_lt := primeNeOneWitness_lt_of_odd_nonsquare_of_three_lt hn hns hn3 hw
    have hp5 : 5 ≤ primeNeOneWitness n hw := by
      have hp2 := hp.1.two_le
      have hpmod := Nat.odd_iff.mp hp.2.1
      omega
    have hndvd : ¬n ∣ primeNeOneWitness n hw := by
      intro hdiv
      have hnle : n ≤ primeNeOneWitness n hw := Nat.le_of_dvd hp.1.pos hdiv
      exact (Nat.not_le_of_lt hp_lt) hnle
    exact (firstStopNeOne_le_primeNeOneWitness hn hw hs ⟨hp5, hp.2.1⟩ hndvd).trans_lt hp_lt

end PseudoPrime.PrimeTest
