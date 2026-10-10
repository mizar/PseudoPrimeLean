/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.BPSW.Selfridge

/-!
# Top-level elementary-range Baillie–PSW interfaces

These definitions use the common precheck and the explicit elementary
Selfridge range.  Search failure is represented by `false`; no existence
theorem is built into the executable definition.  The search is the ascending
pure-Jacobi-`-1` variant; it does not perform Jacobi-`0` factor detection.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Ordinary BPSW using the common precheck and a bounded ascending pure-minus-one search.
For natural `n`, return the precheck's Boolean when available; otherwise search Method A*
parameters with fuel `n - 2`, return false on failure, and run parameterized BPSW on success.
The search tests Jacobi value `-1` without factor-detecting Jacobi-zero stops. Its successful
candidates have magnitude below `2 * n`; the separate specification proves prime acceptance.
-/
def bailliePSW (n : ℕ) : Bool :=
  match primalityPrecheck n with
  | some result => result
  | none =>
    match selfridgeClassicalMethodAStarParamsWithinTwoMul n with
    | none => false
    | some param => bailliePSWWithParams n param.D param.P param.Q

/--
The ordinary precheck-first BPSW entry rejects zero without performing its search.
No premises are required. Unfold the entry and apply the zero precheck equation.
This supplies the zero-input field of its primality-filter contract.
-/
theorem bailliePSW_zero : bailliePSW 0 = false := by simp only [bailliePSW, primalityPrecheck_zero]

/--
The ordinary precheck-first BPSW entry rejects one without performing its search.
Unfold the entry and use the one-input precheck equation; no hypotheses are required.
This supplies the unit-input rejection field of the top-level contract.
-/
theorem bailliePSW_one : bailliePSW 1 = false := by simp only [bailliePSW, primalityPrecheck_one]

/--
The ordinary precheck-first BPSW entry accepts the prime two without parameter search.
Unfolding the entry and applying the two-input precheck equation proves the result.
This separates the even-prime boundary from the odd-domain Selfridge completeness argument.
-/
theorem bailliePSW_two : bailliePSW 2 = true := by simp only [bailliePSW, primalityPrecheck_two]

/--
Every even input other than two is rejected by ordinary precheck-first BPSW.
The assumptions are `n ≠ 2` and `Even n`. Rewrite the common precheck's parity result;
the search and modular comparisons are never reached. This supplies the parity contract.
-/
theorem bailliePSW_even_false {n : ℕ} (hn2 : n ≠ 2) (heven : Even n) : bailliePSW n = false := by
  rw [bailliePSW, primalityPrecheck_even_false hn2 heven]

/--
A prime input passes ordinary BPSW when its bounded classical discriminant search succeeds.
Assume `n.Prime` and an explicit `some D` search result. The proof handles two by precheck;
for odd primes it obtains admissible Method A* parameters and the Jacobi-minus-one property
from the search specification, then applies parameterized BPSW prime completeness.
The following global contract discharges this search-success premise separately.
-/
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
      dsimp only [param, LucasParams.methodAStar]
      split <;> rfl
    have hjacobi : jacobiSym param.D n = -1 := by
      simpa only [hD] using selfridgeClassicalSearchAscending_some_spec hsearch
    simpa only [param] using
      bailliePSWWithParams_of_prime hn param.D param.P param.Q param.discr hjacobi

/--
One-sided correctness of ordinary BPSW conditional on bounded search success for odd primes.
The premise supplies some successful discriminant for each prime `n ≥ 3`; the conclusion
includes zero/one rejection, two acceptance, even-input rejection, and all-prime acceptance.
The proof assembles the boundary lemmas and applies prime completeness with the supplied
search result. `bailliePSW_spec_unconditional` provides the premise by elementary search bounds.
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
Unconditional one-sided correctness of the precheck-first classical ordinary BPSW entry.
There are no GRH or analytic hypotheses. Supply `bailliePSW_spec` with the canonical ascending
search's elementary prime-success theorem. The resulting contract justifies certified rejection
through `decideByTest`; it does not certify primality of arbitrary accepted inputs.
-/
theorem bailliePSW_spec_unconditional : PrimalityTestSpec bailliePSW := by
  apply bailliePSW_spec
  intro n hn hn3
  exact selfridgeClassicalSearchAscendingWithinTwoMul_some_of_prime_of_three_le hn hn3

end PseudoPrime.PrimeTest
