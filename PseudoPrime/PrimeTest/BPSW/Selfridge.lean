/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.BPSW.Strengthened
public import PseudoPrime.PrimeTest.MillerRabin.Prime
public import PseudoPrime.PrimeTest.Selfridge.Bounded
public import PseudoPrime.PrimeTest.StrongLucas.Prime
public import PseudoPrime.PrimeTest.Selfridge.MethodAStarEquivalence

/-!
# Selfridge parameter selection for Baillie–PSW

The search fuel is explicit so that executable totality stays separate from
any analytic bound on the number of candidates.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Run the ascending pure Jacobi -1 Method A* search with the elementary n-2 fuel,
then evaluate fixed-parameter ordinary BPSW. Return none when parameters are unavailable
and some b for the probable-prime Boolean result. The bounded search ranges over
classical magnitudes below 2*n; no factor-detecting stopping rule is used here.
-/
def bailliePSWClassicalWithinTwoMul (n : ℕ) : Option Bool :=
  (selfridgeClassicalMethodAStarParamsWithinTwoMul n).map
    (fun param => bailliePSWWithParams n param.D param.P param.Q)

/--
Run the elementary ascending pure Jacobi -1 Method A* search, then evaluate
fixed-parameter strengthened BPSW. None records unavailable parameters, not a rejection.
The returned Boolean combines base-two MR, Strong Lucas, Lucas-V and raw Euler-Jacobi;
prime inputs at least three have the separate some-true guarantee.
-/
def strengthenedBPSWClassicalWithinTwoMul (n : ℕ) : Option Bool :=
  (selfridgeClassicalMethodAStarParamsWithinTwoMul n).map
    (fun param => strengthenedBPSWWithParams n param.D param.P param.Q)

/-- A successful elementary search supplies the bounded BPSW result. -/
theorem bailliePSWClassicalWithinTwoMul_of_search {n : ℕ} {D : ℤ}
    (hsearch : selfridgeClassicalSearchWithinTwoMul n = some D) :
    bailliePSWClassicalWithinTwoMul n =
      some
        (bailliePSWWithParams n
          (LucasParams.methodAStar D
              (selfridgeClassicalSearchWithinTwoMul_some_methodA_mod hsearch)).D
          (LucasParams.methodAStar D
              (selfridgeClassicalSearchWithinTwoMul_some_methodA_mod hsearch)).P
          (LucasParams.methodAStar D
              (selfridgeClassicalSearchWithinTwoMul_some_methodA_mod hsearch)).Q) := by
  simp only [bailliePSWClassicalWithinTwoMul,
    selfridgeClassicalMethodAStarParamsWithinTwoMul_of_search hsearch, Option.map_some]

/-- A successful elementary search supplies the bounded strengthened-BPSW result. -/
theorem strengthenedBPSWClassicalWithinTwoMul_of_search {n : ℕ} {D : ℤ}
    (hsearch : selfridgeClassicalSearchWithinTwoMul n = some D) :
    strengthenedBPSWClassicalWithinTwoMul n =
      some
        (strengthenedBPSWWithParams n
          (LucasParams.methodAStar D
              (selfridgeClassicalSearchWithinTwoMul_some_methodA_mod hsearch)).D
          (LucasParams.methodAStar D
              (selfridgeClassicalSearchWithinTwoMul_some_methodA_mod hsearch)).P
          (LucasParams.methodAStar D
              (selfridgeClassicalSearchWithinTwoMul_some_methodA_mod hsearch)).Q) := by
  simp only [strengthenedBPSWClassicalWithinTwoMul,
    selfridgeClassicalMethodAStarParamsWithinTwoMul_of_search hsearch, Option.map_some]

/--
For odd `n`, a successful bounded classical search gives the same ordinary BPSW result
with Method A parameters as with Method A*. The proof treats `D = 5` separately and
uses equality of the parameters otherwise. This does not replace the Method A*
parameters used by the strengthened BPSW execution API.
-/
theorem bailliePSWClassicalWithinTwoMul_of_search_methodA {n : ℕ} (hn : Odd n) {D : ℤ}
    (hsearch : selfridgeClassicalSearchWithinTwoMul n = some D) :
    bailliePSWClassicalWithinTwoMul n = some (bailliePSWWithParams n D 1 ((1 - D) / 4)) := by
  rw [bailliePSWClassicalWithinTwoMul_of_search hsearch]
  let hmod := selfridgeClassicalSearchWithinTwoMul_some_methodA_mod hsearch
  by_cases hD : D = 5
  · subst D
    have hjacobi : jacobiSym 5 n = -1 := by
      simpa only using selfridgeClassicalSearchAscending_some_spec hsearch
    have hfive := bailliePSWWithParams_methodAStar_eq_methodA_of_five hn hjacobi
    simpa only [LucasParams.methodAStar, ↓reduceDIte,
      show ((1 - (5 : ℤ)) / 4) = -1 by norm_num only] using congrArg some hfive
  · rw [LucasParams.methodAStar_eq_methodA_of_ne_five hmod hD]
    simp only [LucasParams.methodA_D, LucasParams.methodA_P, LucasParams.methodA_Q]

/--
For every prime n >= 3, the elementary classical BPSW search returns some true.
Use unconditional bounded search success, preserve its D in the Method A* record and
apply fixed-parameter prime completeness. This supplies the bounded ordinary wrapper contract.
-/
theorem bailliePSWClassicalWithinTwoMul_of_prime {n : ℕ} (hn : Nat.Prime n) (hn3 : 3 ≤ n) :
    bailliePSWClassicalWithinTwoMul n = some true := by
  obtain ⟨D, hsearch⟩ :=
    selfridgeClassicalSearchAscendingWithinTwoMul_some_of_prime_of_three_le hn hn3
  rw [bailliePSWClassicalWithinTwoMul_of_search hsearch, Option.some.injEq]
  let hmod := selfridgeClassicalSearchWithinTwoMul_some_methodA_mod hsearch
  let param := LucasParams.methodAStar D hmod
  have hD : param.D = D := by
    dsimp only [param, LucasParams.methodAStar]
    split <;> rfl
  have hjacobi : jacobiSym param.D n = -1 := by
    simpa only [hD] using selfridgeClassicalSearchAscending_some_spec hsearch
  exact bailliePSWWithParams_of_prime hn param.D param.P param.Q param.discr hjacobi

/--
For every prime n >= 3, the elementary strengthened BPSW search returns some true.
The unconditional search supplies valid Method A* parameters with Jacobi -1; fixed-parameter
Strong, V and Euler completeness prove the pass. This supplies the bounded strengthened contract.
-/
theorem strengthenedBPSWClassicalWithinTwoMul_of_prime {n : ℕ} (hn : Nat.Prime n) (hn3 : 3 ≤ n) :
    strengthenedBPSWClassicalWithinTwoMul n = some true := by
  obtain ⟨D, hsearch⟩ :=
    selfridgeClassicalSearchAscendingWithinTwoMul_some_of_prime_of_three_le hn hn3
  rw [strengthenedBPSWClassicalWithinTwoMul_of_search hsearch, Option.some.injEq]
  let hmod := selfridgeClassicalSearchWithinTwoMul_some_methodA_mod hsearch
  let param := LucasParams.methodAStar D hmod
  have hD : param.D = D := by
    dsimp only [param, LucasParams.methodAStar]
    split <;> rfl
  have hjacobi : jacobiSym param.D n = -1 := by
    simpa only [hD] using selfridgeClassicalSearchAscending_some_spec hsearch
  exact strengthenedBPSWWithParams_of_prime hn param.D param.P param.Q param.discr hjacobi

/--
Search the Wheel30-filtered pure Jacobi -1 affine sequence with caller fuel, build
Method A* parameters and evaluate ordinary fixed-parameter BPSW. Fuel counts inspected
affine indices, including filtered-out ones. Return none on parameter-search failure
and some b for a test result; this is distinct from the factor-detecting Wheel30 entry.
-/
def bailliePSWWheel30Ascending (n fuel : ℕ) : Option Bool :=
  (selfridgeWheel30MethodAStarParamsAscending n fuel).map
    (fun param => bailliePSWWithParams n param.D param.P param.Q)

/-- A successful Wheel30 search supplies the corresponding BPSW result. -/
theorem bailliePSWWheel30Ascending_of_search {n fuel : ℕ} {D : ℤ}
    (hsearch : selfridgeWheel30SearchAscending n fuel = some D) :
    bailliePSWWheel30Ascending n fuel =
      some
        (bailliePSWWithParams n
          (LucasParams.methodAStar D
              (selfridgeWheel30SearchAscending_some_methodA_mod (n := n) (k := 0) (fuel := fuel)
                (by simpa only [selfridgeWheel30SearchAscending] using hsearch))).D
          (LucasParams.methodAStar D
              (selfridgeWheel30SearchAscending_some_methodA_mod (n := n) (k := 0) (fuel := fuel)
                (by simpa only [selfridgeWheel30SearchAscending] using hsearch))).P
          (LucasParams.methodAStar D
              (selfridgeWheel30SearchAscending_some_methodA_mod (n := n) (k := 0) (fuel := fuel)
                (by simpa only [selfridgeWheel30SearchAscending] using hsearch))).Q) := by
  simp only [bailliePSWWheel30Ascending,
    selfridgeWheel30MethodAStarParamsAscending_of_search hsearch, Option.map_some]

/-- A prime modulus passes Wheel30 BPSW whenever its bounded search succeeds. -/
theorem bailliePSWWheel30Ascending_of_prime_of_search {n fuel : ℕ} (hn : n.Prime) {D : ℤ}
    (hsearch : selfridgeWheel30SearchAscending n fuel = some D) :
    bailliePSWWheel30Ascending n fuel = some true := by
  rw [bailliePSWWheel30Ascending_of_search hsearch, Option.some.injEq]
  let hmod :=
    selfridgeWheel30SearchAscending_some_methodA_mod
      (by simpa only [selfridgeWheel30SearchAscending] using hsearch)
  let param := LucasParams.methodAStar D hmod
  have hD : param.D = D := by
    dsimp only [param, LucasParams.methodAStar]
    split <;> rfl
  have hjacobi : jacobiSym param.D n = -1 := by
    simpa only [hD] using
      selfridgeWheel30SearchAscending_some_spec
        (by simpa only [selfridgeWheel30SearchAscending] using hsearch)
  exact bailliePSWWithParams_of_prime hn param.D param.P param.Q param.discr hjacobi

/--
Search only prime magnitudes in the affine pure Jacobi -1 sequence with caller fuel,
build Method A* parameters and evaluate ordinary fixed-parameter BPSW. Skipped composite
indices consume fuel. None records search failure; some true remains only a probable-prime pass.
-/
def bailliePSWPrimeAscending (n fuel : ℕ) : Option Bool :=
  (selfridgePrimeMethodAStarParamsAscending n fuel).map
    (fun param => bailliePSWWithParams n param.D param.P param.Q)

/-- A successful prime-only search supplies the corresponding BPSW result. -/
theorem bailliePSWPrimeAscending_of_search {n fuel : ℕ} {D : ℤ}
    (hsearch : selfridgePrimeSearchAscending n fuel = some D) :
    bailliePSWPrimeAscending n fuel =
      some
        (bailliePSWWithParams n
          (LucasParams.methodAStar D
              (selfridgePrimeSearchAscending_some_methodA_mod (n := n) (k := 0) (fuel := fuel)
                (by simpa only [selfridgePrimeSearchAscending] using hsearch))).D
          (LucasParams.methodAStar D
              (selfridgePrimeSearchAscending_some_methodA_mod (n := n) (k := 0) (fuel := fuel)
                (by simpa only [selfridgePrimeSearchAscending] using hsearch))).P
          (LucasParams.methodAStar D
              (selfridgePrimeSearchAscending_some_methodA_mod (n := n) (k := 0) (fuel := fuel)
                (by simpa only [selfridgePrimeSearchAscending] using hsearch))).Q) := by
  simp only [bailliePSWPrimeAscending, selfridgePrimeMethodAStarParamsAscending_of_search hsearch,
    Option.map_some]

/-- A prime modulus passes prime-only BPSW whenever its bounded search succeeds. -/
theorem bailliePSWPrimeAscending_of_prime_of_search {n fuel : ℕ} (hn : n.Prime) {D : ℤ}
    (hsearch : selfridgePrimeSearchAscending n fuel = some D) :
    bailliePSWPrimeAscending n fuel = some true := by
  rw [bailliePSWPrimeAscending_of_search hsearch, Option.some.injEq]
  let hmod :=
    selfridgePrimeSearchAscending_some_methodA_mod
      (by simpa only [selfridgePrimeSearchAscending] using hsearch)
  let param := LucasParams.methodAStar D hmod
  have hD : param.D = D := by
    dsimp only [param, LucasParams.methodAStar]
    split <;> rfl
  have hjacobi : jacobiSym param.D n = -1 := by
    simpa only [hD] using
      selfridgePrimeSearchAscending_some_spec
        (by simpa only [selfridgePrimeSearchAscending] using hsearch)
  exact bailliePSWWithParams_of_prime hn param.D param.P param.Q param.discr hjacobi

end PseudoPrime.PrimeTest
