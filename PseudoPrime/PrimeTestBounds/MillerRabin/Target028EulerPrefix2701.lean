/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028FiniteRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ExtraBlock0
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ExtraBlock1
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ExtraBlock2
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ExtraBlock3
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ExtraBlock4
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ExtraBlock5
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ExtraBlock6
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ExtraBlock7
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ExtraBlock8
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ExtraBlock9
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ExtraBlock10
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ExtraBlock11

/-! # Extended prime-power prefix for finite analytic cells -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Proposed extra rows, selected by their ordered index ranges. -/
def target028ExtraEulerData (n : ℕ) : RefinedEulerAtom :=
  if n ≤ 1117 then target028ExtraData0 n
  else
    if n ≤ 1279 then target028ExtraData1 n
    else
      if n ≤ 1427 then target028ExtraData2 n
      else
        if n ≤ 1553 then target028ExtraData3 n
        else
          if n ≤ 1693 then target028ExtraData4 n
          else
            if n ≤ 1849 then target028ExtraData5 n
            else
              if n ≤ 1999 then target028ExtraData6 n
              else
                if n ≤ 2137 then target028ExtraData7 n
                else
                  if n ≤ 2281 then target028ExtraData8 n
                  else
                    if n ≤ 2411 then target028ExtraData9 n
                    else if n ≤ 2593 then target028ExtraData10 n else target028ExtraData11 n

/-- Union of the additional prime-power blocks through 2701. -/
def target028ExtraEulerSet : Finset ℕ :=
  target028ExtraSet0 ∪ target028ExtraSet1 ∪ target028ExtraSet2 ∪ target028ExtraSet3 ∪
    target028ExtraSet4 ∪
    target028ExtraSet5 ∪
    target028ExtraSet6 ∪
    target028ExtraSet7 ∪
    target028ExtraSet8 ∪
    target028ExtraSet9 ∪
    target028ExtraSet10 ∪
    target028ExtraSet11

/-- On block 0, the combined data use the corresponding checked row. -/
theorem target028_extra_sound0 {n : ℕ} (hn : n ∈ target028ExtraSet0) :
    refinedEulerAtomCheck 24 n (target028ExtraEulerData n) = true := by
  have hr := target028_extra_range0 n hn
  have hc := target028_extra_check0 n hn
  unfold target028ExtraEulerData
  rw [ite_eq_left hr.2]
  exact hc

/-- On block 1, the combined data use the corresponding checked row. -/
theorem target028_extra_sound1 {n : ℕ} (hn : n ∈ target028ExtraSet1) :
    refinedEulerAtomCheck 24 n (target028ExtraEulerData n) = true := by
  have hr := target028_extra_range1 n hn
  have hc := target028_extra_check1 n hn
  unfold target028ExtraEulerData
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1117 ≤ 1117) hr.1))]
  rw [ite_eq_left hr.2]
  exact hc

/-- On block 2, the combined data use the corresponding checked row. -/
theorem target028_extra_sound2 {n : ℕ} (hn : n ∈ target028ExtraSet2) :
    refinedEulerAtomCheck 24 n (target028ExtraEulerData n) = true := by
  have hr := target028_extra_range2 n hn
  have hc := target028_extra_check2 n hn
  unfold target028ExtraEulerData
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1117 ≤ 1279) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1279 ≤ 1279) hr.1))]
  rw [ite_eq_left hr.2]
  exact hc

/-- On block 3, the combined data use the corresponding checked row. -/
theorem target028_extra_sound3 {n : ℕ} (hn : n ∈ target028ExtraSet3) :
    refinedEulerAtomCheck 24 n (target028ExtraEulerData n) = true := by
  have hr := target028_extra_range3 n hn
  have hc := target028_extra_check3 n hn
  unfold target028ExtraEulerData
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1117 ≤ 1427) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1279 ≤ 1427) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1427 ≤ 1427) hr.1))]
  rw [ite_eq_left hr.2]
  exact hc

/-- On block 4, the combined data use the corresponding checked row. -/
theorem target028_extra_sound4 {n : ℕ} (hn : n ∈ target028ExtraSet4) :
    refinedEulerAtomCheck 24 n (target028ExtraEulerData n) = true := by
  have hr := target028_extra_range4 n hn
  have hc := target028_extra_check4 n hn
  unfold target028ExtraEulerData
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1117 ≤ 1553) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1279 ≤ 1553) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1427 ≤ 1553) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1553 ≤ 1553) hr.1))]
  rw [ite_eq_left hr.2]
  exact hc

/-- On block 5, the combined data use the corresponding checked row. -/
theorem target028_extra_sound5 {n : ℕ} (hn : n ∈ target028ExtraSet5) :
    refinedEulerAtomCheck 24 n (target028ExtraEulerData n) = true := by
  have hr := target028_extra_range5 n hn
  have hc := target028_extra_check5 n hn
  unfold target028ExtraEulerData
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1117 ≤ 1693) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1279 ≤ 1693) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1427 ≤ 1693) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1553 ≤ 1693) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1693 ≤ 1693) hr.1))]
  rw [ite_eq_left hr.2]
  exact hc

/-- On block 6, the combined data use the corresponding checked row. -/
theorem target028_extra_sound6 {n : ℕ} (hn : n ∈ target028ExtraSet6) :
    refinedEulerAtomCheck 24 n (target028ExtraEulerData n) = true := by
  have hr := target028_extra_range6 n hn
  have hc := target028_extra_check6 n hn
  unfold target028ExtraEulerData
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1117 ≤ 1849) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1279 ≤ 1849) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1427 ≤ 1849) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1553 ≤ 1849) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1693 ≤ 1849) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1849 ≤ 1849) hr.1))]
  rw [ite_eq_left hr.2]
  exact hc

/-- On block 7, the combined data use the corresponding checked row. -/
theorem target028_extra_sound7 {n : ℕ} (hn : n ∈ target028ExtraSet7) :
    refinedEulerAtomCheck 24 n (target028ExtraEulerData n) = true := by
  have hr := target028_extra_range7 n hn
  have hc := target028_extra_check7 n hn
  unfold target028ExtraEulerData
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1117 ≤ 1999) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1279 ≤ 1999) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1427 ≤ 1999) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1553 ≤ 1999) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1693 ≤ 1999) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1849 ≤ 1999) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1999 ≤ 1999) hr.1))]
  rw [ite_eq_left hr.2]
  exact hc

/-- On block 8, the combined data use the corresponding checked row. -/
theorem target028_extra_sound8 {n : ℕ} (hn : n ∈ target028ExtraSet8) :
    refinedEulerAtomCheck 24 n (target028ExtraEulerData n) = true := by
  have hr := target028_extra_range8 n hn
  have hc := target028_extra_check8 n hn
  unfold target028ExtraEulerData
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1117 ≤ 2137) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1279 ≤ 2137) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1427 ≤ 2137) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1553 ≤ 2137) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1693 ≤ 2137) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1849 ≤ 2137) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1999 ≤ 2137) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 2137 ≤ 2137) hr.1))]
  rw [ite_eq_left hr.2]
  exact hc

/-- On block 9, the combined data use the corresponding checked row. -/
theorem target028_extra_sound9 {n : ℕ} (hn : n ∈ target028ExtraSet9) :
    refinedEulerAtomCheck 24 n (target028ExtraEulerData n) = true := by
  have hr := target028_extra_range9 n hn
  have hc := target028_extra_check9 n hn
  unfold target028ExtraEulerData
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1117 ≤ 2281) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1279 ≤ 2281) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1427 ≤ 2281) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1553 ≤ 2281) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1693 ≤ 2281) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1849 ≤ 2281) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1999 ≤ 2281) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 2137 ≤ 2281) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 2281 ≤ 2281) hr.1))]
  rw [ite_eq_left hr.2]
  exact hc

/-- On block 10, the combined data use the corresponding checked row. -/
theorem target028_extra_sound10 {n : ℕ} (hn : n ∈ target028ExtraSet10) :
    refinedEulerAtomCheck 24 n (target028ExtraEulerData n) = true := by
  have hr := target028_extra_range10 n hn
  have hc := target028_extra_check10 n hn
  unfold target028ExtraEulerData
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1117 ≤ 2411) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1279 ≤ 2411) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1427 ≤ 2411) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1553 ≤ 2411) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1693 ≤ 2411) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1849 ≤ 2411) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1999 ≤ 2411) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 2137 ≤ 2411) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 2281 ≤ 2411) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 2411 ≤ 2411) hr.1))]
  rw [ite_eq_left hr.2]
  exact hc

/-- On block 11, the combined data use the corresponding checked row. -/
theorem target028_extra_sound11 {n : ℕ} (hn : n ∈ target028ExtraSet11) :
    refinedEulerAtomCheck 24 n (target028ExtraEulerData n) = true := by
  have hr := target028_extra_range11 n hn
  have hc := target028_extra_check11 n hn
  unfold target028ExtraEulerData
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1117 ≤ 2593) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1279 ≤ 2593) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1427 ≤ 2593) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1553 ≤ 2593) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1693 ≤ 2593) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1849 ≤ 2593) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 1999 ≤ 2593) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 2137 ≤ 2593) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 2281 ≤ 2593) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 2411 ≤ 2593) hr.1))]
  rw [ite_eq_right (Nat.not_le_of_gt (lt_of_le_of_lt (by decide : 2593 ≤ 2593) hr.1))]
  exact hc

/-- The extended Euler data retain the original certified rows through 1000. -/
def target028EulerData2701 (n : ℕ) : RefinedEulerAtom :=
  if n ≤ 1000 then refinedEulerData n else target028ExtraEulerData n

/-- Union of existing and extra certified prime-power indices. -/
def target028EulerSet2701 : Finset ℕ :=
  refinedEulerPrefixSet ∪ target028ExtraEulerSet

-- The original prefix and the disjoint checked blocks are finite.
set_option maxRecDepth 1000000 in
/-- Every selected prime-power row through 2701 passes the Euler checker.
The original prefix and the extra blocks use their own kernel certificates. -/
theorem target028_euler2701_check :
    ∀ n ∈ target028EulerSet2701,
      IsPrimePow n → refinedEulerAtomCheck 24 n (target028EulerData2701 n) = true := by
  intro n hn hprime
  rcases Finset.mem_union.mp hn with hold | hnew
  · have hle := refinedEulerPrefixSet_le n hold
    rw [target028EulerData2701, ite_eq_left hle]
    exact refined_euler_prefix_check n hold hprime
  · simp only [target028ExtraEulerSet, Finset.mem_union, or_assoc] at hnew
    rcases hnew with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
    · have hgt : 1000 < n :=
        lt_of_le_of_lt (by decide : 1000 ≤ 1000) (target028_extra_range0 n h0).1
      rw [target028EulerData2701, ite_eq_right (Nat.not_le_of_gt hgt)]
      exact target028_extra_sound0 h0
    · have hgt : 1000 < n :=
        lt_of_le_of_lt (by decide : 1000 ≤ 1117) (target028_extra_range1 n h1).1
      rw [target028EulerData2701, ite_eq_right (Nat.not_le_of_gt hgt)]
      exact target028_extra_sound1 h1
    · have hgt : 1000 < n :=
        lt_of_le_of_lt (by decide : 1000 ≤ 1279) (target028_extra_range2 n h2).1
      rw [target028EulerData2701, ite_eq_right (Nat.not_le_of_gt hgt)]
      exact target028_extra_sound2 h2
    · have hgt : 1000 < n :=
        lt_of_le_of_lt (by decide : 1000 ≤ 1427) (target028_extra_range3 n h3).1
      rw [target028EulerData2701, ite_eq_right (Nat.not_le_of_gt hgt)]
      exact target028_extra_sound3 h3
    · have hgt : 1000 < n :=
        lt_of_le_of_lt (by decide : 1000 ≤ 1553) (target028_extra_range4 n h4).1
      rw [target028EulerData2701, ite_eq_right (Nat.not_le_of_gt hgt)]
      exact target028_extra_sound4 h4
    · have hgt : 1000 < n :=
        lt_of_le_of_lt (by decide : 1000 ≤ 1693) (target028_extra_range5 n h5).1
      rw [target028EulerData2701, ite_eq_right (Nat.not_le_of_gt hgt)]
      exact target028_extra_sound5 h5
    · have hgt : 1000 < n :=
        lt_of_le_of_lt (by decide : 1000 ≤ 1849) (target028_extra_range6 n h6).1
      rw [target028EulerData2701, ite_eq_right (Nat.not_le_of_gt hgt)]
      exact target028_extra_sound6 h6
    · have hgt : 1000 < n :=
        lt_of_le_of_lt (by decide : 1000 ≤ 1999) (target028_extra_range7 n h7).1
      rw [target028EulerData2701, ite_eq_right (Nat.not_le_of_gt hgt)]
      exact target028_extra_sound7 h7
    · have hgt : 1000 < n :=
        lt_of_le_of_lt (by decide : 1000 ≤ 2137) (target028_extra_range8 n h8).1
      rw [target028EulerData2701, ite_eq_right (Nat.not_le_of_gt hgt)]
      exact target028_extra_sound8 h8
    · have hgt : 1000 < n :=
        lt_of_le_of_lt (by decide : 1000 ≤ 2281) (target028_extra_range9 n h9).1
      rw [target028EulerData2701, ite_eq_right (Nat.not_le_of_gt hgt)]
      exact target028_extra_sound9 h9
    · have hgt : 1000 < n :=
        lt_of_le_of_lt (by decide : 1000 ≤ 2411) (target028_extra_range10 n h10).1
      rw [target028EulerData2701, ite_eq_right (Nat.not_le_of_gt hgt)]
      exact target028_extra_sound10 h10
    · have hgt : 1000 < n :=
        lt_of_le_of_lt (by decide : 1000 ≤ 2593) (target028_extra_range11 n h11).1
      rw [target028EulerData2701, ite_eq_right (Nat.not_le_of_gt hgt)]
      exact target028_extra_sound11 h11

end PseudoPrime.PrimeTestBounds.MillerRabin
