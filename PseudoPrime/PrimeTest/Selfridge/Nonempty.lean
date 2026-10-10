/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.JacobiWitness.Existence
public import PseudoPrime.PrimeTest.Selfridge.Coincidence
public import PseudoPrime.PrimeTest.Selfridge.Witness
public import PseudoPrime.PrimeTest.Selfridge.Wheel30
public import PseudoPrime.PrimeTest.Selfridge.Composite

/-!
# Nonemptiness of concrete PrimeTest Selfridge stopping sets

This module turns the neutral odd-prime witness theorem into nonemptiness of the
classical stopping sets.  It contains no `PseudoSquare` or GRH dependency.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

namespace Internal

/-- The exceptional Jacobi value used when the least witness is `3`. -/
theorem jacobiSym_three_five_eq_neg_one : jacobiSym 3 5 = -1 := by
  have hfive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym 5 3]
  have hthree : ((3 : ℤ) : ZMod 5) ≠ 0 := by
    intro hzero
    have hval := congrArg ZMod.val hzero
    change 3 = 0 at hval
    norm_num only at hval
  rcases legendreSym.eq_one_or_neg_one 5 hthree with hone | hneg
  · have hpow := legendreSym.eq_pow 5 3
    rw [hone] at hpow
    have hne : (1 : ZMod 5) ≠ 3 ^ ((5 - 1) / 2) := by
      intro hmod
      have hval := congrArg ZMod.val hmod
      rw [@ZMod.val_one 5 ⟨by norm_num only⟩] at hval
      norm_num only [ZMod.val_ofNat] at hval
    exact (hne hpow).elim
  · exact hneg

end Internal

/-- Every odd nonsquare has an odd-prime denominator with Jacobi value `-1`. -/
theorem primeNegOneWitnessSet_nonempty_of_odd_nonsquare {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n) :
    (PrimeNegOneWitnessSet n).Nonempty := by
  have hn1 : n ≠ 1 := by
    intro hnone
    subst n
    exact hns ⟨1, by norm_num only⟩
  have hn3 : n = 3 ∨ 3 < n := by
    obtain ⟨k, hk⟩ := hn
    by_cases hk1 : k = 1
    · left
      rw [hk, hk1]
      norm_num only
    · right
      have hk0 : k ≠ 0 := by
        intro h
        apply hn1
        rw [hk, h]
        norm_num only
      have hkge1 : 1 ≤ k := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hk0)
      have hkge2 : 2 ≤ k := Nat.succ_le_iff.mpr (lt_of_le_of_ne hkge1 (Ne.symm hk1))
      rw [hk]
      calc
        3 < 2 * 2 + 1 := by decide
        _ ≤ 2 * k + 1 := Nat.add_le_add_right (Nat.mul_le_mul_left 2 hkge2) 1
  rcases hn3 with rfl | hn3
  · exact ⟨5, Nat.prime_five, by decide, Internal.jacobiSym_three_five_eq_neg_one⟩
  · obtain ⟨q, hqprime, hqodd, _, hqvalue⟩ :=
      NumberTheory.oddNonsquareHasSmallerNegOneWitness hn hn3 hns
    exact ⟨q, hqprime, hqodd, hqvalue⟩

/-- A candidate containing `27` and every odd prime at least `5` admits a pure `-1` stop. -/
theorem firstStopNegOneSet_nonempty_of_primeWitness {C : ℕ → Prop} {n : ℕ} (hn : Odd n) (h27 : C 27)
    (hprime : ∀ {p : ℕ}, p.Prime → Odd p → 5 ≤ p → C p) (hw : (PrimeNegOneWitnessSet n).Nonempty) :
    (FirstStopNegOneSet C n).Nonempty := by
  obtain ⟨p, hpprime, hpodd, hpvalue⟩ := hw
  by_cases hp3 : p = 3
  · subst p
    refine ⟨27, h27, ?_⟩
    rw [jacobi_selfridgeD (by decide) hn, show 27 = 3 ^ 3 by norm_num only, jacobiSym.pow_right,
      hpvalue]
    norm_num only
  · have hp5 : 5 ≤ p := by exact Internal.oddPrime_ge_five_of_ne_three hpprime hpodd hp3
    exact
      ⟨p,
        mem_firstStopNegOneSet_of_mem_primeNegOneWitnessSet hn (hprime hpprime hpodd hp5)
          ⟨hpprime, hpodd, hpvalue⟩⟩

/-- The classical pure `-1` stopping set is nonempty for every odd nonsquare. -/
theorem classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) : (FirstStopNegOneSet isClassicalCandidate n).Nonempty := by
  apply firstStopNegOneSet_nonempty_of_primeWitness hn ⟨by norm_num only, by decide⟩
  · intro p hp hpodd hp5
    exact ⟨hp5, hpodd⟩
  · exact primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns

/--
Assumptions: `n` is odd, nonsquare, and `27 < n`; `hs` is nonemptiness of the classical
pure `-1` stopping set.
Conclusion: the classical pure `-1` first stop is strictly below `n`.
Proof: use the smaller Jacobi witness construction, then apply first-stop minimality.
Role: supplies the finite Selfridge search with a bound independent of the analytic `Q` bound.
-/
theorem classicalFirstStopNegOne_lt_of_odd_nonsquare_of_twenty_seven_lt {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hn27 : 27 < n)
    (hs : (FirstStopNegOneSet isClassicalCandidate n).Nonempty) :
    firstStopNegOne isClassicalCandidate n hs < n := by
  obtain ⟨p, hp, hpodd, hplt, hpvalue⟩ :=
    NumberTheory.oddNonsquareHasSmallerNegOneWitness hn (lt_trans (by decide : 3 < 27) hn27) hns
  by_cases hp3 : p = 3
  · subst p
    have hmem : 27 ∈ FirstStopNegOneSet isClassicalCandidate n := by
      refine ⟨⟨by norm_num only, by decide⟩, ?_⟩
      rw [jacobi_selfridgeD (by decide) hn, show (27 : ℕ) = 3 ^ 3 by norm_num only,
        jacobiSym.pow_right, hpvalue]
      norm_num only
    exact (firstStopNegOne_le isClassicalCandidate n hs hmem).trans_lt hn27
  · have hp5 : 5 ≤ p := by exact Internal.oddPrime_ge_five_of_ne_three hp hpodd hp3
    have hmem : p ∈ FirstStopNegOneSet isClassicalCandidate n :=
      mem_firstStopNegOneSet_of_mem_primeNegOneWitnessSet (C := isClassicalCandidate) (p := p) hn
        ⟨hp5, hpodd⟩ ⟨hp, hpodd, hpvalue⟩
    exact (firstStopNegOne_le isClassicalCandidate n hs hmem).trans_lt hplt

/-- The Wheel30 pure `-1` stopping set is nonempty for every odd nonsquare. -/
theorem wheel30FirstStopNegOneSet_nonempty_of_odd_nonsquare {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) : (FirstStopNegOneSet isWheel30NegOneCandidate n).Nonempty := by
  apply firstStopNegOneSet_nonempty_of_primeWitness hn
  · norm_num only [isWheel30NegOneCandidate, isWheel30NegOneInitial, isWheel30TailResidue, false_or,
      true_or, false_and, or_false]
  · intro p hp hpodd hp5
    exact prime_mem_wheel30NegOneCandidate hp hpodd hp5
  · exact primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns

/-- The standard factor-detecting Wheel30 stopping set is nonempty for every odd nonsquare. -/
theorem wheel30FirstStopNeOneSet_nonempty_of_odd_nonsquare {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) : (FirstStopNeOneSet isWheel30NeOneCandidate n).Nonempty := by
  have hnpos := Odd.pos hn
  have hclass : (FirstStopNeOneSet isClassicalCandidate n).Nonempty := by
    apply firstStopNeOneSet_nonempty_of_negOne
    · have hn1 : n ≠ 1 := by
        intro h
        subst n
        exact hns ⟨1, by norm_num only⟩
      exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ne_of_gt hnpos, hn1⟩
    · exact classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns
  have hstop := firstStopNeOne_mem isClassicalCandidate n hclass
  have hcand : isWheel30NeOneCandidate (firstStopNeOne isClassicalCandidate n hclass) := by
    by_cases hp : (firstStopNeOne isClassicalCandidate n hclass).Prime
    · exact prime_mem_wheel30NeOneCandidate hp hstop.1.2 hstop.1.1
    · have hi : 0 < firstStopNeOne isClassicalCandidate n hclass := by
        have hi5 := hstop.1.1
        exact lt_of_lt_of_le (by decide : 0 < 5) hi5
      have hmin :
        ∀ j < firstStopNeOne isClassicalCandidate n hclass,
          j ∉ FirstStopNeOneSet isClassicalCandidate n := by
        intro j hj
        exact not_mem_firstStopNeOneSet_of_lt isClassicalCandidate n hclass hj
      rcases composite_minimal_classical_neOne_eq_nine_or_fifteen hnpos hn hns hi hp hstop hmin with
        h | h
      · rw [h]
        norm_num only [isWheel30NeOneCandidate, isWheel30NeOneInitial, isWheel30TailResidue,
          false_or, true_or, false_and, or_false]
      · rw [h]
        norm_num only [isWheel30NeOneCandidate, isWheel30NeOneInitial, isWheel30TailResidue,
          false_or, true_or, false_and, or_false]
  exact ⟨firstStopNeOne isClassicalCandidate n hclass, hcand, hstop.2.1, hstop.2.2⟩

/-- The classical factor-detecting stopping set is nonempty for every odd nonsquare. -/
theorem classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) : (FirstStopNeOneSet isClassicalCandidate n).Nonempty := by
  apply firstStopNeOneSet_nonempty_of_negOne
  · have hn1 : n ≠ 1 := by
      intro h
      subst n
      exact hns ⟨1, by norm_num only⟩
    have hnpos := Odd.pos hn
    exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ne_of_gt hnpos, hn1⟩
  · exact classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns

end PseudoPrime.PrimeTest
