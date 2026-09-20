/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import PseudoPrime.PrimeTest.Selfridge.FirstStop
import PseudoPrime.PrimeTest.Selfridge.WitnessBounds
import PseudoPrime.PrimeTest.Selfridge.Nonempty
import PseudoPrime.PrimeTest.Selfridge.Candidates
import PseudoPrime.PrimeTest.Selfridge.MethodAStar
import PseudoPrime.PrimeTest.Selfridge.Params
import PseudoPrime.PrimeTest.StrongLucas.Spec

/-!
# Ascending classical Selfridge search

This module provides the canonical ascending traversal and records the
current candidate index explicitly.
-/

namespace PseudoPrime.PrimeTest

/- The definition records the odd candidate magnitude `5 + 2 * k`. -/
def classicalCandidateMagnitude (k : ℕ) : ℕ :=
  5 + 2 * k

/- Every generated magnitude is a classical Selfridge candidate. -/
theorem classicalCandidateMagnitude_isCandidate (k : ℕ) :
    isClassicalCandidate (classicalCandidateMagnitude k) := by
  refine ⟨?_, ?_⟩
  · dsimp [classicalCandidateMagnitude]
    omega
  · refine ⟨k + 2, ?_⟩
    dsimp [classicalCandidateMagnitude]
    omega

/-- Ascending search from candidate index `k` over a half-open fuel range. -/
def selfridgeClassicalSearchAscendingFrom (n k fuel : ℕ) : Option ℤ :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      let i := classicalCandidateMagnitude k
      if jacobiSym (selfridgeD i) n = -1 then some (selfridgeD i)
    else selfridgeClassicalSearchAscendingFrom n (k + 1) fuel

/-- Ascending search beginning with the least classical candidate. -/
def selfridgeClassicalSearchAscending (n fuel : ℕ) : Option ℤ :=
  selfridgeClassicalSearchAscendingFrom n 0 fuel

/-- Ascending search over the Wheel30-filtered classical candidates. -/
def selfridgeWheel30SearchAscendingFrom (n k fuel : ℕ) : Option ℤ :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      let i := classicalCandidateMagnitude k
      if wheel30NegOneCandidate i then
      if jacobiSym (selfridgeD i) n = -1 then some (selfridgeD i)
      else selfridgeWheel30SearchAscendingFrom n (k + 1) fuel
    else selfridgeWheel30SearchAscendingFrom n (k + 1) fuel

/-- Ascending Wheel30-filtered search beginning with the least classical candidate. -/
def selfridgeWheel30SearchAscending (n fuel : ℕ) : Option ℤ :=
  selfridgeWheel30SearchAscendingFrom n 0 fuel

/-- Ascending search over the prime classical candidates. -/
def selfridgePrimeSearchAscendingFrom (n k fuel : ℕ) : Option ℤ :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      let i := classicalCandidateMagnitude k
      if i.Prime then
      if jacobiSym (selfridgeD i) n = -1 then some (selfridgeD i)
      else selfridgePrimeSearchAscendingFrom n (k + 1) fuel
    else selfridgePrimeSearchAscendingFrom n (k + 1) fuel

/-- Ascending prime-filtered search beginning with the least classical candidate. -/
def selfridgePrimeSearchAscending (n fuel : ℕ) : Option ℤ :=
  selfridgePrimeSearchAscendingFrom n 0 fuel

/-- The least candidate gives the concrete stopping value for the first odd prime. -/
theorem selfridgeClassicalSearchAscending_three :
    selfridgeClassicalSearchAscending 3 (3 - 2) = some 5 := by
  change (if jacobiSym (selfridgeD 5) 3 = -1 then some (selfridgeD 5) else none) = some 5
  rw [jacobi_selfridgeD (by decide) (by decide)]
  rw [show (↑(3 : ℕ) : ℤ) = 3 by norm_num only]
  rw [Internal.jacobiSym_three_five_eq_neg_one]
  rw [selfridgeD_of_mod_four_eq_one (by decide)]
  change some (5 : ℤ) = some 5
  rfl

/-- The second odd prime stops at the next negative Selfridge candidate. -/
theorem selfridgeClassicalSearchAscending_five :
    selfridgeClassicalSearchAscending 5 (5 - 2) = some (-7) := by
  have hzero : jacobiSym (↑(5 : ℕ) : ℤ) 5 = 0 := by
    rw [jacobiSym.eq_zero_iff_not_coprime]
    norm_num
  have h55 : jacobiSym (selfridgeD 5) 5 ≠ -1 := by
    rw [selfridgeD_of_mod_four_eq_one (by decide), hzero]
    norm_num
  have h75 : jacobiSym (selfridgeD 7) 5 = -1 := by
    rw [show selfridgeD 7 = -7 by norm_num [selfridgeD]]
    apply (jacobiSym.eq_one_or_neg_one (by norm_num)).resolve_left
    exact Internal.jacobiSym_neg_seven_five_ne_one
  change
    (if jacobiSym (selfridgeD 5) 5 = -1 then some (selfridgeD 5)
      else
        if jacobiSym (selfridgeD 7) 5 = -1 then some (selfridgeD 7)
        else if jacobiSym (selfridgeD 9) 5 = -1 then some (selfridgeD 9) else none) =
      some (-7)
  rw [ite_eq_right h55, h75]
  rw [show selfridgeD 7 = -7 by norm_num [selfridgeD]]
  change some (-7 : ℤ) = some (-7)
  rfl

/-- The third odd prime stops at the initial positive Selfridge candidate. -/
theorem selfridgeClassicalSearchAscending_seven :
    selfridgeClassicalSearchAscending 7 (7 - 2) = some 5 := by
  have h5 : jacobiSym (selfridgeD 5) 7 = -1 := by
    rw [selfridgeD_of_mod_four_eq_one (i := 5) (by decide)]
    norm_num [jacobiSym, legendreSym, quadraticCharFun]
  change
    (if jacobiSym (selfridgeD 5) 7 = -1 then some (selfridgeD 5)
      else
        if jacobiSym (selfridgeD 7) 7 = -1 then some (selfridgeD 7)
        else
          if jacobiSym (selfridgeD 9) 7 = -1 then some (selfridgeD 9)
          else
            if jacobiSym (selfridgeD 11) 7 = -1 then some (selfridgeD 11)
            else if jacobiSym (selfridgeD 13) 7 = -1 then some (selfridgeD 13) else none) =
      some 5
  rw [h5]
  rw [selfridgeD_of_mod_four_eq_one (i := 5) (by decide)]
  change some (5 : ℤ) = some 5
  rfl

/-- The fourth odd prime reaches the positive candidate `D = 13`. -/
theorem selfridgeClassicalSearchAscending_eleven :
    selfridgeClassicalSearchAscending 11 (11 - 2) = some 13 := by
  have h5 : jacobiSym (selfridgeD 5) 11 = 1 := by
    rw [selfridgeD_of_mod_four_eq_one (i := 5) (by decide)]
    norm_num [jacobiSym, legendreSym, quadraticCharFun]
  have h7 : jacobiSym (selfridgeD 7) 11 = 1 := by
    rw [show selfridgeD 7 = -7 by norm_num [selfridgeD]]
    norm_num [jacobiSym, legendreSym, quadraticCharFun]
  have h9 : jacobiSym (selfridgeD 9) 11 = 1 := by
    rw [selfridgeD_of_mod_four_eq_one (i := 9) (by decide)]
    norm_num [jacobiSym, legendreSym, quadraticCharFun]
  have h11 : jacobiSym (selfridgeD 11) 11 = 0 := by
    rw [show selfridgeD 11 = -11 by norm_num [selfridgeD]]
    norm_num [jacobiSym, legendreSym, quadraticCharFun]
  have h13 : jacobiSym (selfridgeD 13) 11 = -1 := by
    rw [selfridgeD_of_mod_four_eq_one (i := 13) (by decide)]
    norm_num [jacobiSym, legendreSym, quadraticCharFun]
  change
    (if jacobiSym (selfridgeD 5) 11 = -1 then some (selfridgeD 5)
      else
        if jacobiSym (selfridgeD 7) 11 = -1 then some (selfridgeD 7)
        else
          if jacobiSym (selfridgeD 9) 11 = -1 then some (selfridgeD 9)
          else
            if jacobiSym (selfridgeD 11) 11 = -1 then some (selfridgeD 11)
            else
              if jacobiSym (selfridgeD 13) 11 = -1 then some (selfridgeD 13)
              else
                if jacobiSym (selfridgeD 15) 11 = -1 then some (selfridgeD 15)
                else
                  if jacobiSym (selfridgeD 17) 11 = -1 then some (selfridgeD 17)
                  else
                    if jacobiSym (selfridgeD 19) 11 = -1 then some (selfridgeD 19)
                    else if jacobiSym (selfridgeD 21) 11 = -1 then some (selfridgeD 21) else none) =
      some 13
  rw [h5, h7, h9, h11, h13]
  rw [selfridgeD_of_mod_four_eq_one (i := 13) (by decide)]
  change some (13 : ℤ) = some 13
  rfl

/-- The fifth odd prime stops at the initial positive Selfridge candidate. -/
theorem selfridgeClassicalSearchAscending_thirteen :
    selfridgeClassicalSearchAscending 13 (13 - 2) = some 5 := by
  have h5 : jacobiSym (selfridgeD 5) 13 = -1 := by
    rw [selfridgeD_of_mod_four_eq_one (i := 5) (by decide)]
    norm_num [jacobiSym, legendreSym, quadraticCharFun]
  change
    (if jacobiSym (selfridgeD 5) 13 = -1 then some (selfridgeD 5)
      else
        if jacobiSym (selfridgeD 7) 13 = -1 then some (selfridgeD 7)
        else
          if jacobiSym (selfridgeD 9) 13 = -1 then some (selfridgeD 9)
          else
            if jacobiSym (selfridgeD 11) 13 = -1 then some (selfridgeD 11)
            else
              if jacobiSym (selfridgeD 13) 13 = -1 then some (selfridgeD 13)
              else
                if jacobiSym (selfridgeD 15) 13 = -1 then some (selfridgeD 15)
                else
                  if jacobiSym (selfridgeD 17) 13 = -1 then some (selfridgeD 17)
                  else
                    if jacobiSym (selfridgeD 19) 13 = -1 then some (selfridgeD 19)
                    else
                      if jacobiSym (selfridgeD 21) 13 = -1 then some (selfridgeD 21)
                      else
                        if jacobiSym (selfridgeD 23) 13 = -1 then some (selfridgeD 23)
                        else
                          if jacobiSym (selfridgeD 25) 13 = -1 then some (selfridgeD 25)
                          else none) =
      some 5
  rw [h5]
  rw [selfridgeD_of_mod_four_eq_one (i := 5) (by decide)]
  change some (5 : ℤ) = some 5
  rfl

/-- Every classical candidate occurs at a unique affine scan index. -/
theorem exists_classicalCandidateMagnitude_eq {i : ℕ} (hi : isClassicalCandidate i) :
    ∃ k, classicalCandidateMagnitude k = i := by
  rcases hi with ⟨hi5, hodd⟩
  refine ⟨(i - 5) / 2, ?_⟩
  have hi2 : i % 2 = 1 := Nat.odd_iff.mp hodd
  have hparity : (i - 5) % 2 = 0 := by omega
  dsimp [classicalCandidateMagnitude]
  calc
    5 + 2 * ((i - 5) / 2) = 5 + ((i - 5) / 2) * 2 := by rw [Nat.mul_comm]
    _ = 5 + ((i - 5) / 2) * 2 + (i - 5) % 2 := by rw [hparity, Nat.add_zero]
    _ = 5 + (((i - 5) / 2) * 2 + (i - 5) % 2) := by rw [Nat.add_assoc]
    _ = 5 + (i - 5) := by rw [Nat.div_add_mod']
    _ = i := by omega

/-- Method A* parameters produced by the ascending search. -/
def selfridgeClassicalMethodAStarParamsAscending (n fuel : ℕ) : Option LucasParams :=
  match selfridgeClassicalSearchAscending n fuel with
  | none => none
  | some D => if hmod : (1 - D) % 4 = 0 then some (LucasParams.methodAStar D hmod) else none

/-- Method A* parameters produced by the ascending Wheel30-filtered search. -/
def selfridgeWheel30MethodAStarParamsAscending (n fuel : ℕ) : Option LucasParams :=
  match selfridgeWheel30SearchAscending n fuel with
  | none => none
  | some D => if hmod : (1 - D) % 4 = 0 then some (LucasParams.methodAStar D hmod) else none

/-- Method A* parameters produced by the ascending prime-filtered search. -/
def selfridgePrimeMethodAStarParamsAscending (n fuel : ℕ) : Option LucasParams :=
  match selfridgePrimeSearchAscending n fuel with
  | none => none
  | some D => if hmod : (1 - D) % 4 = 0 then some (LucasParams.methodAStar D hmod) else none

/-- A successful ascending search returns a Jacobi `-1` discriminant. -/
theorem selfridgeClassicalSearchAscending_some_spec {n k fuel : ℕ} {D : ℤ}
    (hsearch : selfridgeClassicalSearchAscendingFrom n k fuel = some D) : jacobiSym D n = -1 := by
  induction fuel generalizing k with
  | zero =>
    simp only [selfridgeClassicalSearchAscendingFrom] at hsearch
    cases hsearch
  | succ fuel ih =>
    simp only [selfridgeClassicalSearchAscendingFrom] at hsearch
    split at hsearch <;> rename_i hj
    · have hD : selfridgeD (classicalCandidateMagnitude k) = D := Option.some.inj hsearch
      rw [← hD]
      exact hj
    · exact ih hsearch

/-- A successful ascending Wheel30 search returns a Jacobi `-1` discriminant. -/
theorem selfridgeWheel30SearchAscending_some_spec {n k fuel : ℕ} {D : ℤ}
    (hsearch : selfridgeWheel30SearchAscendingFrom n k fuel = some D) : jacobiSym D n = -1 := by
  induction fuel generalizing k with
  | zero =>
    simp only [selfridgeWheel30SearchAscendingFrom] at hsearch
    cases hsearch
  | succ fuel ih =>
    simp only [selfridgeWheel30SearchAscendingFrom] at hsearch
    split at hsearch <;> rename_i hwheel
    · split at hsearch <;> rename_i hjacobi
      · have hD : selfridgeD (classicalCandidateMagnitude k) = D := Option.some.inj hsearch
        rw [← hD]
        exact hjacobi
      · exact ih hsearch
    · exact ih hsearch

/-- A successful ascending Wheel30 search returns an admissible Method A discriminant. -/
theorem selfridgeWheel30SearchAscending_some_methodA_mod {n k fuel : ℕ} {D : ℤ}
    (hsearch : selfridgeWheel30SearchAscendingFrom n k fuel = some D) : (1 - D) % 4 = 0 := by
  induction fuel generalizing k with
  | zero =>
    simp only [selfridgeWheel30SearchAscendingFrom] at hsearch
    cases hsearch
  | succ fuel ih =>
    simp only [selfridgeWheel30SearchAscendingFrom] at hsearch
    split at hsearch <;> rename_i hwheel
    · split at hsearch <;> rename_i hjacobi
      · have hD : selfridgeD (classicalCandidateMagnitude k) = D := Option.some.inj hsearch
        rw [← hD]
        exact selfridgeD_methodA_mod_four (classicalCandidateMagnitude_isCandidate k).2
      · exact ih hsearch
    · exact ih hsearch

/-- A successful ascending prime search returns a Jacobi `-1` discriminant. -/
theorem selfridgePrimeSearchAscending_some_spec {n k fuel : ℕ} {D : ℤ}
    (hsearch : selfridgePrimeSearchAscendingFrom n k fuel = some D) : jacobiSym D n = -1 := by
  induction fuel generalizing k with
  | zero =>
    simp only [selfridgePrimeSearchAscendingFrom] at hsearch
    cases hsearch
  | succ fuel ih =>
    simp only [selfridgePrimeSearchAscendingFrom] at hsearch
    split at hsearch <;> rename_i hprime
    · split at hsearch <;> rename_i hjacobi
      · have hD : selfridgeD (classicalCandidateMagnitude k) = D := Option.some.inj hsearch
        rw [← hD]
        exact hjacobi
      · exact ih hsearch
    · exact ih hsearch

/-- A successful ascending prime search returns an admissible Method A discriminant. -/
theorem selfridgePrimeSearchAscending_some_methodA_mod {n k fuel : ℕ} {D : ℤ}
    (hsearch : selfridgePrimeSearchAscendingFrom n k fuel = some D) : (1 - D) % 4 = 0 := by
  induction fuel generalizing k with
  | zero =>
    simp only [selfridgePrimeSearchAscendingFrom] at hsearch
    cases hsearch
  | succ fuel ih =>
    simp only [selfridgePrimeSearchAscendingFrom] at hsearch
    split at hsearch <;> rename_i hprime
    · split at hsearch <;> rename_i hjacobi
      · have hD : selfridgeD (classicalCandidateMagnitude k) = D := Option.some.inj hsearch
        rw [← hD]
        exact selfridgeD_methodA_mod_four (classicalCandidateMagnitude_isCandidate k).2
      · exact ih hsearch
    · exact ih hsearch

/-- A successful ascending search returns a candidate in its scanned range. -/
theorem selfridgeClassicalSearchAscending_some_index {n k fuel : ℕ} {D : ℤ}
    (hsearch : selfridgeClassicalSearchAscendingFrom n k fuel = some D) :
    ∃ j < k + fuel, k ≤ j ∧ selfridgeD (classicalCandidateMagnitude j) = D := by
  induction fuel generalizing k with
  | zero =>
    simp only [selfridgeClassicalSearchAscendingFrom] at hsearch
    cases hsearch
  | succ fuel ih =>
    simp only [selfridgeClassicalSearchAscendingFrom] at hsearch
    split at hsearch <;> rename_i hj
    · exact ⟨k, by omega, le_rfl, Option.some.inj hsearch⟩
    · obtain ⟨j, hjlt, hkj, hD⟩ := ih hsearch
      exact ⟨j, by omega, by omega, hD⟩

/-- A failed ascending search has no Jacobi `-1` value in its scanned range. -/
theorem selfridgeClassicalSearchAscending_none_spec {n k fuel : ℕ}
    (hsearch : selfridgeClassicalSearchAscendingFrom n k fuel = none) :
    ∀ j, k ≤ j → j < k + fuel → jacobiSym (selfridgeD (classicalCandidateMagnitude j)) n ≠ -1 := by
  induction fuel generalizing k with
  | zero =>
    simp only [selfridgeClassicalSearchAscendingFrom] at hsearch
    intro j hkj hjlt
    omega
  | succ fuel ih =>
    simp only [selfridgeClassicalSearchAscendingFrom] at hsearch
    split at hsearch <;> rename_i hj
    · cases hsearch
    · intro j hkj hjlt
      by_cases hEq : j = k
      · subst j
        exact hj
      · apply ih hsearch j
        · omega
        · omega

/-- An ascending search returns the first successful candidate in a finite range. -/
theorem selfridgeClassicalSearchAscendingFrom_some_of_prior_failures {n s k : ℕ} {i : ℕ}
    (hi : classicalCandidateMagnitude (s + k) = i) (hjacobi : jacobiSym (selfridgeD i) n = -1)
    (hfail :
      ∀ j, s ≤ j → j < s + k → jacobiSym (selfridgeD (classicalCandidateMagnitude j)) n ≠ -1) :
    selfridgeClassicalSearchAscendingFrom n s (k + 1) = some (selfridgeD i) := by
  induction k generalizing s with
  | zero =>
    rw [selfridgeClassicalSearchAscendingFrom]
    simp only [Nat.add_zero] at hi hjacobi
    rw [← hi] at hjacobi
    split <;> rename_i hcondition
    · simp only [hi]
    · exact False.elim (hcondition hjacobi)
  | succ k ih =>
    rw [selfridgeClassicalSearchAscendingFrom]
    have hcurrent : jacobiSym (selfridgeD (classicalCandidateMagnitude s)) n ≠ -1 := by
      exact hfail s le_rfl (by omega)
    rw [ite_eq_right hcurrent]
    apply ih (s := s + 1)
    · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi
    · intro j hsj hjs
      apply hfail j
      · omega
      · omega

/-- The mathematical `-1` first-stop is realized by the ascending search. -/
theorem selfridgeClassicalSearchAscending_some_of_firstStopNegOne {n : ℕ}
    (hs : (FirstStopNegOneSet isClassicalCandidate n).Nonempty) :
    ∃ k,
      classicalCandidateMagnitude k = firstStopNegOne isClassicalCandidate n hs ∧
        selfridgeClassicalSearchAscending n (k + 1) =
          some (selfridgeD (firstStopNegOne isClassicalCandidate n hs)) := by
  let i := firstStopNegOne isClassicalCandidate n hs
  have hstop := firstStopNegOne_mem isClassicalCandidate n hs
  obtain ⟨k, hk⟩ := exists_classicalCandidateMagnitude_eq hstop.1
  have hjacobi : jacobiSym (selfridgeD i) n = -1 := by exact hstop.2
  have hk' : classicalCandidateMagnitude (0 + k) = i := by simpa only [Nat.zero_add, i] using hk
  refine ⟨k, hk, ?_⟩
  change selfridgeClassicalSearchAscendingFrom n 0 (k + 1) = some (selfridgeD i)
  apply
    selfridgeClassicalSearchAscendingFrom_some_of_prior_failures (s := 0) (k := k) (i := i) hk'
      hjacobi
  intro j h0 hjk hsuccess
  have hji : classicalCandidateMagnitude j < i := by
    dsimp [classicalCandidateMagnitude] at hk ⊢
    omega
  exact
    (not_mem_firstStopNegOneSet_of_lt isClassicalCandidate n hs hji)
      ⟨classicalCandidateMagnitude_isCandidate j, hsuccess⟩

/-- Increasing the fuel preserves a successful ascending-search result. -/
theorem selfridgeClassicalSearchAscendingFrom_some_of_le_fuel {n s fuel extra : ℕ} {D : ℤ}
    (hsearch : selfridgeClassicalSearchAscendingFrom n s fuel = some D) :
    selfridgeClassicalSearchAscendingFrom n s (fuel + extra) = some D := by
  induction fuel generalizing s extra with
  | zero =>
    simp only [selfridgeClassicalSearchAscendingFrom] at hsearch
    cases hsearch
  | succ fuel ih =>
    rw [Nat.succ_add]
    rw [selfridgeClassicalSearchAscendingFrom] at hsearch ⊢
    split at hsearch <;> rename_i hj
    · rw [ite_eq_left hj]
      exact hsearch
    · rw [ite_eq_right hj]
      exact ih hsearch

/-- The remaining prime below `27` with initial candidate `D = 5`. -/
theorem selfridgeClassicalSearchAscending_seventeen :
    selfridgeClassicalSearchAscending 17 (17 - 2) = some 5 := by
  have h5 : jacobiSym (selfridgeD 5) 17 = -1 := by
    rw [selfridgeD_of_mod_four_eq_one (i := 5) (by decide)]
    norm_num [jacobiSym, legendreSym, quadraticCharFun]
  have hsearch : selfridgeClassicalSearchAscending 17 1 = some 5 := by
    change (if jacobiSym (selfridgeD 5) 17 = -1 then some (selfridgeD 5) else none) = some 5
    rw [h5, selfridgeD_of_mod_four_eq_one (i := 5) (by decide)]
    change some (5 : ℤ) = some 5
    rfl
  simpa [selfridgeClassicalSearchAscending] using
    (selfridgeClassicalSearchAscendingFrom_some_of_le_fuel (extra := 14)
      (by simpa [selfridgeClassicalSearchAscending] using hsearch))

/-- The remaining prime below `27` with second candidate `D = -7`. -/
theorem selfridgeClassicalSearchAscending_nineteen :
    selfridgeClassicalSearchAscending 19 (19 - 2) = some (-7) := by
  have h5 : jacobiSym (selfridgeD 5) 19 ≠ -1 := by
    rw [selfridgeD_of_mod_four_eq_one (i := 5) (by decide)]
    norm_num [jacobiSym, legendreSym, quadraticCharFun]
  have h7 : jacobiSym (selfridgeD 7) 19 = -1 := by
    rw [show selfridgeD 7 = -7 by norm_num [selfridgeD]]
    norm_num [jacobiSym, legendreSym, quadraticCharFun]
  have hsearch : selfridgeClassicalSearchAscending 19 2 = some (-7) := by
    change
      (if jacobiSym (selfridgeD 5) 19 = -1 then some (selfridgeD 5)
        else if jacobiSym (selfridgeD 7) 19 = -1 then some (selfridgeD 7) else none) =
        some (-7)
    rw [ite_eq_right h5, h7, show selfridgeD 7 = -7 by norm_num [selfridgeD]]
    change some (-7 : ℤ) = some (-7)
    rfl
  simpa [selfridgeClassicalSearchAscending] using
    (selfridgeClassicalSearchAscendingFrom_some_of_le_fuel (extra := 15)
      (by simpa [selfridgeClassicalSearchAscending] using hsearch))

/-- The last prime below `27` again stops at the initial positive candidate. -/
theorem selfridgeClassicalSearchAscending_twenty_three :
    selfridgeClassicalSearchAscending 23 (23 - 2) = some 5 := by
  have h5 : jacobiSym (selfridgeD 5) 23 = -1 := by
    rw [selfridgeD_of_mod_four_eq_one (i := 5) (by decide)]
    norm_num [jacobiSym, legendreSym, quadraticCharFun]
  have hsearch : selfridgeClassicalSearchAscending 23 1 = some 5 := by
    change (if jacobiSym (selfridgeD 5) 23 = -1 then some (selfridgeD 5) else none) = some 5
    rw [h5, selfridgeD_of_mod_four_eq_one (i := 5) (by decide)]
    change some (5 : ℤ) = some 5
    rfl
  simpa [selfridgeClassicalSearchAscending] using
    (selfridgeClassicalSearchAscendingFrom_some_of_le_fuel (extra := 20)
      (by simpa [selfridgeClassicalSearchAscending] using hsearch))

/-- A first-stop below `n` is found by the elementary `n - 2` fuel budget. -/
theorem selfridgeClassicalSearchAscendingWithinTwoMul_some_of_firstStop_lt {n : ℕ} (hn : 3 ≤ n)
    (hs : (FirstStopNegOneSet isClassicalCandidate n).Nonempty)
    (hstop : firstStopNegOne isClassicalCandidate n hs < n) :
    ∃ D, selfridgeClassicalSearchAscending n (n - 2) = some D := by
  obtain ⟨k, hk, hsearch⟩ := selfridgeClassicalSearchAscending_some_of_firstStopNegOne hs
  have hkfuel : k + 1 ≤ n - 2 := by
    dsimp [classicalCandidateMagnitude] at hk
    omega
  refine ⟨selfridgeD (firstStopNegOne isClassicalCandidate n hs), ?_⟩
  have hextra : (k + 1) + (n - 2 - (k + 1)) = n - 2 := by omega
  rw [← hextra]
  exact selfridgeClassicalSearchAscendingFrom_some_of_le_fuel hsearch

/-- A least prime witness below `n` and the exceptional bound `27` imply bounded success. -/
theorem selfridgeClassicalSearchAscendingWithinTwoMul_some_of_primeWitness_lt {n : ℕ} (hn : 3 ≤ n)
    (hnodd : Odd n) (hn27 : 27 < n) (hw : (PrimeNegOneWitnessSet n).Nonempty)
    (hs : (FirstStopNegOneSet isClassicalCandidate n).Nonempty)
    (hqw : primeNegOneWitness n hw < n) :
    ∃ D, selfridgeClassicalSearchAscending n (n - 2) = some D := by
  apply selfridgeClassicalSearchAscendingWithinTwoMul_some_of_firstStop_lt hn hs
  have hbound := classicalFirstStopNegOne_le_max_twenty_seven_primeWitness hnodd hw hs
  exact hbound.trans_lt ((Nat.max_lt).2 ⟨hn27, hqw⟩)

/-- Every prime above `27` supplies the witness bound needed by the ascending search. -/
theorem selfridgeClassicalSearchAscendingWithinTwoMul_some_of_prime {n : ℕ} (hn : n.Prime)
    (hn27 : 27 < n) (hw : (PrimeNegOneWitnessSet n).Nonempty)
    (hs : (FirstStopNegOneSet isClassicalCandidate n).Nonempty) :
    ∃ D, selfridgeClassicalSearchAscending n (n - 2) = some D := by
  have hodd : Odd n := hn.odd_iff.mpr (by omega)
  obtain ⟨p, hp, hpodd, hplt, hvalue⟩ := NumberTheory.primeHasSmallerNegOneWitness hn (by omega)
  apply
    selfridgeClassicalSearchAscendingWithinTwoMul_some_of_primeWitness_lt (by omega) hodd hn27 hw hs
  exact (primeNegOneWitness_le n hw ⟨hp, hpodd, hvalue⟩).trans_lt hplt

/-- Every prime at least `3` has a successful elementary ascending search. -/
theorem selfridgeClassicalSearchAscendingWithinTwoMul_some_of_prime_of_three_le {n : ℕ}
    (hn : n.Prime) (hn3 : 3 ≤ n) : ∃ D, selfridgeClassicalSearchAscending n (n - 2) = some D := by
  by_cases hn27 : 27 < n
  · exact
      selfridgeClassicalSearchAscendingWithinTwoMul_some_of_prime hn hn27
        (primeNegOneWitnessSet_nonempty_of_odd_nonsquare (hn.odd_of_ne_two (by omega))
          hn.not_isSquare)
        (classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare (hn.odd_of_ne_two (by omega))
          hn.not_isSquare)
  · have hnle : n ≤ 27 := by omega
    interval_cases n <;>
      first
      | exact ⟨5, selfridgeClassicalSearchAscending_three⟩
      | exact ⟨-7, selfridgeClassicalSearchAscending_five⟩
      | exact ⟨5, selfridgeClassicalSearchAscending_seven⟩
      | exact ⟨13, selfridgeClassicalSearchAscending_eleven⟩
      | exact ⟨5, selfridgeClassicalSearchAscending_thirteen⟩
      | exact ⟨5, selfridgeClassicalSearchAscending_seventeen⟩
      | exact ⟨-7, selfridgeClassicalSearchAscending_nineteen⟩
      | exact ⟨5, selfridgeClassicalSearchAscending_twenty_three⟩
      | norm_num at hn

/-- A successful ascending search converts to the corresponding Method A* parameters. -/
theorem selfridgeClassicalMethodAStarParamsAscending_of_search {n fuel : ℕ} {D : ℤ}
    (hsearch : selfridgeClassicalSearchAscending n fuel = some D) :
    selfridgeClassicalMethodAStarParamsAscending n fuel =
      some
        (LucasParams.methodAStar D
          (by
            obtain ⟨k, _, _, hD⟩ := selfridgeClassicalSearchAscending_some_index hsearch
            rw [← hD]
            exact selfridgeD_methodA_mod_four (classicalCandidateMagnitude_isCandidate k).2)) := by
  simp only [selfridgeClassicalMethodAStarParamsAscending, hsearch]
  split
  · rfl
  · rename_i hnot
    exact
      False.elim
        (hnot
          (by
            obtain ⟨k, _, _, hD⟩ := selfridgeClassicalSearchAscending_some_index hsearch
            rw [← hD]
            exact selfridgeD_methodA_mod_four (classicalCandidateMagnitude_isCandidate k).2))

/-- A successful ascending Wheel30 search determines its Method A* parameters. -/
theorem selfridgeWheel30MethodAStarParamsAscending_of_search {n fuel : ℕ} {D : ℤ}
    (hsearch : selfridgeWheel30SearchAscending n fuel = some D) :
    selfridgeWheel30MethodAStarParamsAscending n fuel =
      some
        (LucasParams.methodAStar D
          (selfridgeWheel30SearchAscending_some_methodA_mod
            (by simpa only [selfridgeWheel30SearchAscending] using hsearch))) := by
  simp only [selfridgeWheel30MethodAStarParamsAscending, hsearch]
  split
  · rfl
  · rename_i hnot
    exact
      False.elim
        (hnot
          (selfridgeWheel30SearchAscending_some_methodA_mod
            (by simpa only [selfridgeWheel30SearchAscending] using hsearch)))

/-- A successful ascending prime search determines its Method A* parameters. -/
theorem selfridgePrimeMethodAStarParamsAscending_of_search {n fuel : ℕ} {D : ℤ}
    (hsearch : selfridgePrimeSearchAscending n fuel = some D) :
    selfridgePrimeMethodAStarParamsAscending n fuel =
      some
        (LucasParams.methodAStar D
          (selfridgePrimeSearchAscending_some_methodA_mod
            (by simpa only [selfridgePrimeSearchAscending] using hsearch))) := by
  simp only [selfridgePrimeMethodAStarParamsAscending, hsearch]
  split
  · rfl
  · rename_i hnot
    exact
      False.elim
        (hnot
          (selfridgePrimeSearchAscending_some_methodA_mod
            (by simpa only [selfridgePrimeSearchAscending] using hsearch)))

end PseudoPrime.PrimeTest
