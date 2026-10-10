/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Selfridge.SearchAscending

/-!
# Elementary bounded Selfridge search

This module fixes the classical scan fuel to `n - 2`.  The only bound used
here is the elementary inequality for the generated candidates; no GRH or
analytic estimate is involved.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Ascending classical pure-minus-one Selfridge search with fuel `n - 2`.
For natural `n`, return an optional signed discriminant using the canonical increasing candidate
order. `none` means that this finite scan found no Jacobi-minus-one candidate; it is not a factor
certificate. For `n ≥ 3`, every returned magnitude is strictly below `2 * n`.
This elementary range is the search used by the ordinary classical BPSW boundary interface.
-/
def selfridgeClassicalSearchWithinTwoMul (n : ℕ) : Option ℤ :=
  selfridgeClassicalSearchAscending n (n - 2)

/--
Method A* parameter selection from the ascending classical scan with fuel `n - 2`.
Return `none` on scan failure, or a proof-carrying `LucasParams` record for the selected
Jacobi-minus-one discriminant. The record applies the special `(5,5)` branch at `D = 5`.
Top-level classical BPSW uses this optional parameter result after the common precheck.
-/
def selfridgeClassicalMethodAStarParamsWithinTwoMul (n : ℕ) : Option LucasParams :=
  selfridgeClassicalMethodAStarParamsAscending n (n - 2)

/--
Every scanned classical index `k < n - 2` has signed discriminant magnitude below `2 * n`.
The statement retains `3 ≤ n`; the proof rewrites signed magnitude to its natural candidate
formula and uses the index inequality arithmetically. This turns the scan fuel into the
elementary discriminant bound used by the successful-search theorem.
-/
theorem selfridgeD_natAbs_lt_two_mul_of_candidate_index {n k : ℕ} (_hn : 3 ≤ n) (hk : k < n - 2) :
    (selfridgeD (classicalCandidateMagnitude k)).natAbs < 2 * n := by
  rw [selfridgeD_natAbs]
  dsimp only [classicalCandidateMagnitude]
  linarith only [Nat.add_lt_of_lt_sub hk]

/--
A successful bounded classical search at input `n ≥ 3` returns `|D| < 2 * n`.
Extract the scanned index and its range from the ascending search specification, identify its
signed discriminant, and apply the candidate-index bound. This estimates returned parameters
without using GRH, logarithmic bounds, or a search-success assumption for arbitrary inputs.
-/
theorem selfridgeClassicalSearchWithinTwoMul_some_bound {n : ℕ} (hn : 3 ≤ n) {D : ℤ}
    (hsearch : selfridgeClassicalSearchWithinTwoMul n = some D) : D.natAbs < 2 * n := by
  obtain ⟨k, hk, _, hD⟩ := selfridgeClassicalSearchAscending_some_index hsearch
  rw [← hD]
  exact selfridgeD_natAbs_lt_two_mul_of_candidate_index hn (by simpa only [zero_add] using hk)

/--
Every signed discriminant returned by the bounded classical search is Method A admissible.
The premise is an explicit successful result `some D`; conclude `(1 - D) % 4 = 0`.
The search specification identifies a classical candidate, whose sign rule gives the congruence.
This constructs the proof field required by Method A and Method A* parameter selection.
-/
theorem selfridgeClassicalSearchWithinTwoMul_some_methodA_mod {n : ℕ} {D : ℤ}
    (hsearch : selfridgeClassicalSearchWithinTwoMul n = some D) : (1 - D) % 4 = 0 := by
  obtain ⟨k, _, _, hD⟩ := selfridgeClassicalSearchAscending_some_index hsearch
  rw [← hD]
  exact selfridgeD_methodA_mod_four (classicalCandidateMagnitude_isCandidate k).2

/--
A successful bounded classical result has the congruence needed for Method A* parameters.
From `some D`, conclude `(1 - D) % 4 = 0` by the Method A admissibility theorem.
The congruence is shared by both parameter rules; only their `D = 5` recurrence pair differs.
This alias exposes the search-to-Method-A* contract without an extra mathematical hypothesis.
-/
theorem selfridgeClassicalSearchWithinTwoMul_some_methodAStar_mod {n : ℕ} {D : ℤ}
    (hsearch : selfridgeClassicalSearchWithinTwoMul n = some D) : (1 - D) % 4 = 0 := by
  exact selfridgeClassicalSearchWithinTwoMul_some_methodA_mod hsearch

/--
A successful bounded discriminant search determines the exact Method A* parameter record.
Given `selfridgeClassicalSearchWithinTwoMul n = some D`, the parameter search returns
`some (LucasParams.methodAStar D ...)`, using the proved admissibility congruence.
Apply the general ascending-search parameter bridge at the fixed fuel. This lets prime-pass
proofs recover the full parameter invariant from the simpler discriminant search result.
-/
theorem selfridgeClassicalMethodAStarParamsWithinTwoMul_of_search {n : ℕ} {D : ℤ}
    (hsearch : selfridgeClassicalSearchWithinTwoMul n = some D) :
    selfridgeClassicalMethodAStarParamsWithinTwoMul n =
      some
        (LucasParams.methodAStar D
          (selfridgeClassicalSearchWithinTwoMul_some_methodA_mod hsearch)) := by
  exact selfridgeClassicalMethodAStarParamsAscending_of_search hsearch

/--
The Method A* record formed from a successful bounded search retains `|D| < 2 * n`.
Assume `n ≥ 3`, search success, and any admissibility proof for the returned `D`.
Both constructor branches preserve the discriminant, so rewrite that projection and apply
the successful-search bound. This carries elementary magnitude estimates through parameterization.
-/
theorem selfridgeClassicalMethodAStarParamsWithinTwoMul_some_bound {n : ℕ} (hn : 3 ≤ n) {D : ℤ}
    (hsearch : selfridgeClassicalSearchWithinTwoMul n = some D) (hmod : (1 - D) % 4 = 0) :
    (LucasParams.methodAStar D hmod).D.natAbs < 2 * n := by
  have hparamD : (LucasParams.methodAStar D hmod).D = D := by
    dsimp only [LucasParams.methodAStar]
    split <;> rfl
  rw [hparamD]
  exact selfridgeClassicalSearchWithinTwoMul_some_bound hn hsearch

end PseudoPrime.PrimeTest
