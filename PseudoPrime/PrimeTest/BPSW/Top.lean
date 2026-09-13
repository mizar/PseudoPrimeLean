/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import PseudoPrime.PrimeTest.BPSW.Selfridge

/-!
# Top-level elementary-range Baillie–PSW interfaces

These definitions use the common precheck and the explicit elementary
Selfridge range.  Search failure is represented by `false`; no existence
theorem is built into the executable definition.  The search is the ascending
pure-Jacobi-`-1` variant; it does not perform Jacobi-`0` factor detection.
-/

namespace PseudoPrime.PrimeTest

/-- Baillie–PSW with the elementary `|D| < 2*n` Selfridge A* search. -/
def bailliePSW (n : ℕ) : Bool :=
  match primalityPrecheck n with
  | some result => result
  | none =>
    match selfridgeClassicalMethodAStarParamsWithinTwoMul n with
    | none => false
    | some param => bailliePSWWithParams n param.D param.P param.Q

/-- Strengthened Baillie–PSW with the elementary `|D| < 2*n` Selfridge A* search. -/
def strengthenedBPSW (n : ℕ) : Bool :=
  match primalityPrecheck n with
  | some result => result
  | none =>
    match selfridgeClassicalMethodAStarParamsWithinTwoMul n with
    | none => false
    | some param => strengthenedBPSWWithParams n param.D param.P param.Q

/-- Top-level BPSW rejects zero through the common precheck. -/
theorem bailliePSW_zero : bailliePSW 0 = false := by simp only [bailliePSW, primalityPrecheck_zero]

/-- Top-level BPSW rejects one through the common precheck. -/
theorem bailliePSW_one : bailliePSW 1 = false := by simp only [bailliePSW, primalityPrecheck_one]

/-- Top-level BPSW accepts two through the common precheck. -/
theorem bailliePSW_two : bailliePSW 2 = true := by simp only [bailliePSW, primalityPrecheck_two]

/-- Top-level BPSW rejects every even input other than two. -/
theorem bailliePSW_even_false {n : ℕ} (hn2 : n ≠ 2) (heven : Even n) : bailliePSW n = false := by
  rw [bailliePSW, primalityPrecheck_even_false hn2 heven]

/-- Top-level strengthened BPSW rejects zero through the common precheck. -/
theorem strengthenedBPSW_zero : strengthenedBPSW 0 = false := by
  simp only [strengthenedBPSW, primalityPrecheck_zero]

/-- Top-level strengthened BPSW rejects one through the common precheck. -/
theorem strengthenedBPSW_one : strengthenedBPSW 1 = false := by
  simp only [strengthenedBPSW, primalityPrecheck_one]

/-- Top-level strengthened BPSW accepts two through the common precheck. -/
theorem strengthenedBPSW_two : strengthenedBPSW 2 = true := by
  simp only [strengthenedBPSW, primalityPrecheck_two]

/-- Top-level strengthened BPSW rejects every even input other than two. -/
theorem strengthenedBPSW_even_false {n : ℕ} (hn2 : n ≠ 2) (heven : Even n) :
    strengthenedBPSW n = false := by rw [strengthenedBPSW, primalityPrecheck_even_false hn2 heven]

/-- A prime modulus passes top-level BPSW when the elementary search succeeds. -/
theorem bailliePSW_of_prime_of_search {n : ℕ} (hn : n.Prime) {D : ℤ}
    (hsearch : selfridgeClassicalSearchWithinTwoMul n = some D) : bailliePSW n = true := by
  rcases hn.eq_two_or_odd' with rfl | hodd
  · simp only [bailliePSW, primalityPrecheck_two]
  · have hn3 : 3 ≤ n := hn.odd_iff.mp hodd
    rw [bailliePSW, primalityPrecheck_none_of_odd hn3 hodd hn.not_isSquare]
    change selfridgeClassicalSearchAscending n (n - 2) = some D at hsearch
    simp only [selfridgeClassicalMethodAStarParamsWithinTwoMul]
    rw [selfridgeClassicalMethodAStarParamsAscending_of_search hsearch]
    let hmod := selfridgeClassicalSearchWithinTwoMul_some_methodA_mod hsearch
    let param := LucasParams.methodAStar D hmod
    have hD : param.D = D := by
      dsimp [param, LucasParams.methodAStar]
      split <;> rfl
    have hjacobi : jacobiSym param.D n = -1 := by
      simpa only [hD] using selfridgeClassicalSearchAscending_some_spec hsearch
    simpa only [param] using
      bailliePSWWithParams_of_prime hn param.D param.P param.Q param.discr hjacobi

/-- A prime modulus passes top-level strengthened BPSW when the elementary search succeeds. -/
theorem strengthenedBPSW_of_prime_of_search {n : ℕ} (hn : n.Prime) {D : ℤ}
    (hsearch : selfridgeClassicalSearchWithinTwoMul n = some D) : strengthenedBPSW n = true := by
  rcases hn.eq_two_or_odd' with rfl | hodd
  · simp only [strengthenedBPSW, primalityPrecheck_two]
  · have hn3 : 3 ≤ n := hn.odd_iff.mp hodd
    rw [strengthenedBPSW, primalityPrecheck_none_of_odd hn3 hodd hn.not_isSquare]
    change selfridgeClassicalSearchAscending n (n - 2) = some D at hsearch
    simp only [selfridgeClassicalMethodAStarParamsWithinTwoMul]
    rw [selfridgeClassicalMethodAStarParamsAscending_of_search hsearch]
    let hmod := selfridgeClassicalSearchWithinTwoMul_some_methodA_mod hsearch
    let param := LucasParams.methodAStar D hmod
    have hD : param.D = D := by
      dsimp [param, LucasParams.methodAStar]
      split <;> rfl
    have hjacobi : jacobiSym param.D n = -1 := by
      simpa only [hD] using selfridgeClassicalSearchAscending_some_spec hsearch
    simpa only [param] using
      strengthenedBPSWWithParams_of_prime hn param.D param.P param.Q param.discr hjacobi

/--
Input: a proof that every odd prime has a successful elementary Selfridge search.
Claim: the top-level BPSW implementation satisfies the common primality-test
interface, including the explicit parity behavior.
Role: the executable-to-specification connection; an analytic module may later
provide the search-success premise without becoming a PrimeTest dependency.
-/
theorem bailliePSW_spec
    (hsearch :
      ∀ {n : ℕ}, n.Prime → 3 ≤ n → ∃ D : ℤ, selfridgeClassicalSearchWithinTwoMul n = some D) :
    PrimalityTestSpec bailliePSW := by
  constructor
  · exact bailliePSW_zero
  · exact bailliePSW_one
  · exact bailliePSW_two
  · intro n hn2 heven
    exact bailliePSW_even_false hn2 heven
  · intro n hn
    rcases hn.eq_two_or_odd' with rfl | hodd
    · exact bailliePSW_two
    · rcases hsearch hn (hn.odd_iff.mp hodd) with ⟨D, hD⟩
      exact bailliePSW_of_prime_of_search hn hD

/--
Input: the same explicit odd-prime elementary-search success premise.
Claim: the strengthened top-level BPSW implementation satisfies the common
primality-test interface.
Role: packages the prime, small-input, and parity guarantees together.
-/
theorem strengthenedBPSW_spec
    (hsearch :
      ∀ {n : ℕ}, n.Prime → 3 ≤ n → ∃ D : ℤ, selfridgeClassicalSearchWithinTwoMul n = some D) :
    PrimalityTestSpec strengthenedBPSW := by
  constructor
  · exact strengthenedBPSW_zero
  · exact strengthenedBPSW_one
  · exact strengthenedBPSW_two
  · intro n hn2 heven
    exact strengthenedBPSW_even_false hn2 heven
  · intro n hn
    rcases hn.eq_two_or_odd' with rfl | hodd
    · exact strengthenedBPSW_two
    · rcases hsearch hn (hn.odd_iff.mp hodd) with ⟨D, hD⟩
      exact strengthenedBPSW_of_prime_of_search hn hD

/-- The unconditional BPSW specification obtained from the canonical ascending search. -/
theorem bailliePSW_spec_unconditional : PrimalityTestSpec bailliePSW := by
  apply bailliePSW_spec
  intro n hn hn3
  exact selfridgeClassicalSearchAscendingWithinTwoMul_some_of_prime_of_three_le hn hn3

/-- The unconditional strengthened-BPSW specification obtained from ascending search. -/
theorem strengthenedBPSW_spec_unconditional : PrimalityTestSpec strengthenedBPSW := by
  apply strengthenedBPSW_spec
  intro n hn hn3
  exact selfridgeClassicalSearchAscendingWithinTwoMul_some_of_prime_of_three_le hn hn3

end PseudoPrime.PrimeTest
