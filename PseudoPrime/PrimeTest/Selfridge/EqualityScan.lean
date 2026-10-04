/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.Selfridge.Scan

/-! # Reference equality-exclusion Selfridge scan and certified consumers -/

namespace PseudoPrime.PrimeTest

/-- Stop using the reference programs' equality exclusion instead of divisibility.
The domain below 2*n supplies equivalence; arbitrary magnitudes need not agree. -/
def selfridgeNeOneStopEq (n i : ℕ) : Bool :=
  wheel30NeOneCandidate i &&
    (decide (i ≠ n) && decide (ReferenceArithmetic.jacobiExecutable (selfridgeD i) n ≠ 1))

/-- Positive magnitudes below 2*n are divisible by n exactly when they equal n.
Thus the reference stopping predicate agrees with the original predicate on that interval. -/
theorem selfridgeNeOneStopEq_eq (n i : ℕ) (hi : 0 < i) (hb : i < 2 * n) :
    selfridgeNeOneStopEq n i = selfridgeNeOneStop n i := by
  have hd : n ∣ i ↔ i = n :=
    ⟨fun h ↦ Nat.eq_of_dvd_of_lt_two_mul (Nat.ne_of_gt hi) h hb, fun h ↦ h.symm ▸ dvd_refl n⟩
  simp only [selfridgeNeOneStopEq, selfridgeNeOneStop, hd]

/-- Scan increasing magnitudes with equality exclusion and the Wheel30 filter.
Fuel counts magnitudes; this comparison model preserves the reference first-stop semantics. -/
def selfridgeNeOneScanEq (n start : ℕ) : ℕ → Option ℕ
  | 0 => none
  | fuel + 1 =>
    if selfridgeNeOneStopEq n start then some start else selfridgeNeOneScanEq n (start + 1) fuel

/-- The two finite scans agree before a known first stop below 2*n, for every budget.
Induction never compares their predicates beyond that stop, including exhausted budgets. -/
theorem selfridgeNeOneScanEq_prefix {n start i : ℕ} (hstart : 0 < start) (hsi : start ≤ i)
    (hb : i < 2 * n) (hs : selfridgeNeOneStop n i = true)
    (hm : ∀ j, start ≤ j → j < i → selfridgeNeOneStop n j = false) (fuel : ℕ) :
    selfridgeNeOneScanEq n start fuel = selfridgeNeOneScan n start fuel := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
    have he := selfridgeNeOneStopEq_eq n start hstart (hsi.trans_lt hb)
    by_cases hi : start = i
    · subst start
      simp only [selfridgeNeOneScanEq, selfridgeNeOneScan, he, hs, ↓reduceIte]
    · have hlt : start < i := Nat.lt_of_le_of_ne hsi hi
      have hf := hm start le_rfl hlt
      simp only [selfridgeNeOneScanEq, selfridgeNeOneScan, he, hf, Bool.false_eq_true, ↓reduceIte]
      exact
        ih (Nat.zero_lt_succ start) (Nat.succ_le_of_lt hlt)
          (fun j hj hji ↦ hm j (Nat.le_trans (Nat.le_succ start) hj) hji)

/-- The mathematical first stop of every odd nonsquare input is below 2*n.
Above fifteen use the classical bound; small inputs use kernel-checked witnesses. -/
theorem wheel30FirstStopNeOne_lt_two_mul {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hw : (FirstStopNeOneSet isWheel30NeOneCandidate n).Nonempty) :
    firstStopNeOne isWheel30NeOneCandidate n hw < 2 * n := by
  by_cases hl : 15 < n
  · have hc := classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns
    have hp :=
      primeNeOneWitnessSet_nonempty_of_negOne
        (primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)
    rw [firstStopNeOne_wheel30_eq_classical hn.pos hn hns hc hw]
    exact
      (classicalFirstStopNeOne_lt_of_odd_nonsquare_of_fifteen_lt hn hns hl hp hc).trans_le
        (Nat.le_mul_of_pos_left n (by decide : 0 < 2))
  · have hle : n ≤ 15 := Nat.le_of_not_gt hl
    interval_cases n <;> norm_num only [Nat.odd_iff, Nat.reduceMod] at hn
    all_goals
      first
      | exact False.elim (hns ⟨1, rfl⟩)
      | exact False.elim (hns ⟨3, rfl⟩)
      |
        exact
          (firstStopNeOne_le _ _ hw ((selfridgeNeOneStop_iff _ 5).mp (by decide +kernel))).trans_lt
            (by decide)
      |
        exact
          (firstStopNeOne_le _ _ hw ((selfridgeNeOneStop_iff _ 7).mp (by decide +kernel))).trans_lt
            (by decide)
      |
        exact
          (firstStopNeOne_le _ _ hw ((selfridgeNeOneStop_iff _ 13).mp (by decide +kernel))).trans_lt
            (by decide)

end PseudoPrime.PrimeTest

namespace PseudoPrime.PrimeTest

/-- Every budget gives the same result with equality or divisibility exclusion on odd nonsquares.
The unconditional first-stop bound supplies the common-prefix induction invariant. -/
theorem selfridgeNeOneScanEq_eq {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n) (fuel : ℕ) :
    selfridgeNeOneScanEq n 5 fuel = selfridgeNeOneScan n 5 fuel := by
  have hw := wheel30FirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns
  have hm := firstStopNeOne_mem isWheel30NeOneCandidate n hw
  apply
    selfridgeNeOneScanEq_prefix (by decide) (wheel30NeOneCandidate_classical hm.1).1
      (wheel30FirstStopNeOne_lt_two_mul hn hns hw) ((selfridgeNeOneStop_iff n _).mpr hm)
  intro j _ hj
  exact
    Bool.eq_false_iff.mpr
      (fun h ↦ not_mem_firstStopNeOneSet_of_lt _ n hw hj ((selfridgeNeOneStop_iff n j).mp h))

end PseudoPrime.PrimeTest

namespace PseudoPrime.PrimeTest

/-- Classify the equality-exclusion scan for an odd nonsquare input.
Transport soundness from the original scan, keeping parameters, factors, and exhaustion distinct. -/
def selfridgeNeOneResultEq (n : ℕ) (hn : Odd n) (hns : ¬IsSquare n) (fuel : ℕ) :
    SelfridgeScanResult n :=
  selfridgeNeOneClassify n (selfridgeNeOneScanEq n 5 fuel)
    (fun _ h ↦ selfridgeNeOneScan_sound ((selfridgeNeOneScanEq_eq hn hns fuel).symm.trans h))

/-- The equality-exclusion scan preserves the complete certified search outcome for every budget.
The shared classifier identifies parameter and divisor evidence by proof irrelevance. -/
theorem selfridgeNeOneResultEq_eq (n : ℕ) (hn : Odd n) (hns : ¬IsSquare n) (fuel : ℕ) :
    selfridgeNeOneResultEq n hn hns fuel = selfridgeNeOneResult n fuel := by
  unfold selfridgeNeOneResultEq selfridgeNeOneResult
  exact
    selfridgeNeOneClassify_congr n _ _ _ _
      ((selfridgeNeOneScanEq_eq hn hns fuel).trans (selfridgeNeOneJump_eq n 5 fuel).symm)

/-- Ordinary finite-search decisions agree, including certified factors and unknown exhaustion. -/
theorem selfridgeNeOneResultEq_decide (n : ℕ) (hn : Odd n) (hns : ¬IsSquare n) (fuel : ℕ) :
    (selfridgeNeOneResultEq n hn hns fuel).decide = (selfridgeNeOneResult n fuel).decide := by
  rw [selfridgeNeOneResultEq_eq]

/-- Strengthened finite-search decisions agree for every odd nonsquare and caller budget. -/
theorem selfridgeNeOneResultEq_decideStrengthened (n : ℕ) (hn : Odd n) (hns : ¬IsSquare n)
    (fuel : ℕ) :
    (selfridgeNeOneResultEq n hn hns fuel).decideStrengthened =
      (selfridgeNeOneResult n fuel).decideStrengthened := by
  rw [selfridgeNeOneResultEq_eq]

end PseudoPrime.PrimeTest
