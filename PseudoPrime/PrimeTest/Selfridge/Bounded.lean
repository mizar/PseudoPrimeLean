/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import PseudoPrime.PrimeTest.Selfridge.SearchAscending

/-!
# Elementary bounded Selfridge search

This module fixes the classical scan fuel to `n - 2`.  The only bound used
here is the elementary inequality for the generated candidates; no GRH or
analytic estimate is involved.
-/

namespace PseudoPrime.PrimeTest

/-- Classical Selfridge search through the elementary range `|D| < 2*n`.

The canonical traversal is ascending, so the first admissible candidate is
returned when the fuel is sufficient.
-/
def selfridgeClassicalSearchWithinTwoMul (n : ℕ) : Option ℤ :=
  selfridgeClassicalSearchAscending n (n - 2)

/-- Method A* parameters obtained from the elementary classical search range. -/
def selfridgeClassicalMethodAStarParamsWithinTwoMul (n : ℕ) : Option LucasParams :=
  selfridgeClassicalMethodAStarParamsAscending n (n - 2)

/-- A classical candidate scanned below `n - 2` has signed magnitude less than `2*n`. -/
theorem selfridgeD_natAbs_lt_two_mul_of_candidate_index {n k : ℕ} (hn : 3 ≤ n) (hk : k < n - 2) :
    (selfridgeD (classicalCandidateMagnitude k)).natAbs < 2 * n := by
  rw [selfridgeD_natAbs]
  dsimp [classicalCandidateMagnitude]
  omega

/-- A successful elementary classical search returns a discriminant with `|D| < 2*n`. -/
theorem selfridgeClassicalSearchWithinTwoMul_some_bound {n : ℕ} (hn : 3 ≤ n) {D : ℤ}
    (hsearch : selfridgeClassicalSearchWithinTwoMul n = some D) : D.natAbs < 2 * n := by
  obtain ⟨k, hk, _, hD⟩ := selfridgeClassicalSearchAscending_some_index hsearch
  rw [← hD]
  exact selfridgeD_natAbs_lt_two_mul_of_candidate_index hn (by simpa using hk)

/-- A successful elementary search is admissible for Method A. -/
theorem selfridgeClassicalSearchWithinTwoMul_some_methodA_mod {n : ℕ} {D : ℤ}
    (hsearch : selfridgeClassicalSearchWithinTwoMul n = some D) : (1 - D) % 4 = 0 := by
  obtain ⟨k, _, _, hD⟩ := selfridgeClassicalSearchAscending_some_index hsearch
  rw [← hD]
  exact selfridgeD_methodA_mod_four (classicalCandidateMagnitude_isCandidate k).2

/-- A successful elementary search is admissible for Method A*. -/
theorem selfridgeClassicalSearchWithinTwoMul_some_methodAStar_mod {n : ℕ} {D : ℤ}
    (hsearch : selfridgeClassicalSearchWithinTwoMul n = some D) : (1 - D) % 4 = 0 := by
  exact selfridgeClassicalSearchWithinTwoMul_some_methodA_mod hsearch

/-- The ascending bounded search determines its Method A* parameters. -/
theorem selfridgeClassicalMethodAStarParamsWithinTwoMul_of_search {n : ℕ} {D : ℤ}
    (hsearch : selfridgeClassicalSearchWithinTwoMul n = some D) :
    selfridgeClassicalMethodAStarParamsWithinTwoMul n =
      some
        (LucasParams.methodAStar D
          (selfridgeClassicalSearchWithinTwoMul_some_methodA_mod hsearch)) := by
  exact selfridgeClassicalMethodAStarParamsAscending_of_search hsearch

/-- The Method A* parameter selected by the elementary search retains the D bound. -/
theorem selfridgeClassicalMethodAStarParamsWithinTwoMul_some_bound {n : ℕ} (hn : 3 ≤ n) {D : ℤ}
    (hsearch : selfridgeClassicalSearchWithinTwoMul n = some D) (hmod : (1 - D) % 4 = 0) :
    (LucasParams.methodAStar D hmod).D.natAbs < 2 * n := by
  have hparamD : (LucasParams.methodAStar D hmod).D = D := by
    dsimp [LucasParams.methodAStar]
    split <;> rfl
  rw [hparamD]
  exact selfridgeClassicalSearchWithinTwoMul_some_bound hn hsearch

end PseudoPrime.PrimeTest
