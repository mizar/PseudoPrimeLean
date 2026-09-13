/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import PseudoPrime.PrimeTest.BPSW.Strengthened
import PseudoPrime.PrimeTest.MillerRabin.Prime
import PseudoPrime.PrimeTest.Selfridge.Bounded
import PseudoPrime.PrimeTest.StrongLucas.Prime
import PseudoPrime.PrimeTest.Selfridge.MethodAStarEquivalence

/-!
# Selfridge parameter selection for Baillie–PSW

The search fuel is explicit so that executable totality stays separate from
any analytic bound on the number of candidates.
-/

namespace PseudoPrime.PrimeTest

/-- Baillie–PSW using only the elementary `|D| < 2*n` Selfridge range. -/
def bailliePSWClassicalWithinTwoMul (n : ℕ) : Option Bool :=
  (selfridgeClassicalMethodAStarParamsWithinTwoMul n).map
    (fun param => bailliePSWWithParams n param.D param.P param.Q)

/-- Strengthened BPSW using only the elementary `|D| < 2*n` Selfridge range. -/
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
    convert congrArg some hfive using 1 <;> norm_num [LucasParams.methodAStar]
  · rw [LucasParams.methodAStar_eq_methodA_of_ne_five hmod hD]
    simp only [LucasParams.methodA_D, LucasParams.methodA_P, LucasParams.methodA_Q]

/-- A prime modulus passes the bounded classical BPSW search. -/
theorem bailliePSWClassicalWithinTwoMul_of_prime {n : ℕ} (hn : Nat.Prime n) (hn3 : 3 ≤ n) :
    bailliePSWClassicalWithinTwoMul n = some true := by
  obtain ⟨D, hsearch⟩ :=
    selfridgeClassicalSearchAscendingWithinTwoMul_some_of_prime_of_three_le hn hn3
  rw [bailliePSWClassicalWithinTwoMul_of_search hsearch, Option.some.injEq]
  let hmod := selfridgeClassicalSearchWithinTwoMul_some_methodA_mod hsearch
  let param := LucasParams.methodAStar D hmod
  have hD : param.D = D := by
    dsimp [param, LucasParams.methodAStar]
    split <;> rfl
  have hjacobi : jacobiSym param.D n = -1 := by
    simpa only [hD] using selfridgeClassicalSearchAscending_some_spec hsearch
  exact bailliePSWWithParams_of_prime hn param.D param.P param.Q param.discr hjacobi

/-- A prime modulus passes the bounded classical strengthened-BPSW search. -/
theorem strengthenedBPSWClassicalWithinTwoMul_of_prime {n : ℕ} (hn : Nat.Prime n) (hn3 : 3 ≤ n) :
    strengthenedBPSWClassicalWithinTwoMul n = some true := by
  obtain ⟨D, hsearch⟩ :=
    selfridgeClassicalSearchAscendingWithinTwoMul_some_of_prime_of_three_le hn hn3
  rw [strengthenedBPSWClassicalWithinTwoMul_of_search hsearch, Option.some.injEq]
  let hmod := selfridgeClassicalSearchWithinTwoMul_some_methodA_mod hsearch
  let param := LucasParams.methodAStar D hmod
  have hD : param.D = D := by
    dsimp [param, LucasParams.methodAStar]
    split <;> rfl
  have hjacobi : jacobiSym param.D n = -1 := by
    simpa only [hD] using selfridgeClassicalSearchAscending_some_spec hsearch
  exact strengthenedBPSWWithParams_of_prime hn param.D param.P param.Q param.discr hjacobi

/-- Baillie–PSW using the ascending Wheel30 Selfridge Method A* search. -/
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
              (selfridgeWheel30SearchAscending_some_methodA_mod
                (by simpa only [selfridgeWheel30SearchAscending] using hsearch))).D
          (LucasParams.methodAStar D
              (selfridgeWheel30SearchAscending_some_methodA_mod
                (by simpa only [selfridgeWheel30SearchAscending] using hsearch))).P
          (LucasParams.methodAStar D
              (selfridgeWheel30SearchAscending_some_methodA_mod
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
    dsimp [param, LucasParams.methodAStar]
    split <;> rfl
  have hjacobi : jacobiSym param.D n = -1 := by
    simpa only [hD] using
      selfridgeWheel30SearchAscending_some_spec
        (by simpa only [selfridgeWheel30SearchAscending] using hsearch)
  exact bailliePSWWithParams_of_prime hn param.D param.P param.Q param.discr hjacobi

/-- Baillie–PSW using the ascending prime-only Selfridge Method A* search. -/
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
              (selfridgePrimeSearchAscending_some_methodA_mod
                (by simpa only [selfridgePrimeSearchAscending] using hsearch))).D
          (LucasParams.methodAStar D
              (selfridgePrimeSearchAscending_some_methodA_mod
                (by simpa only [selfridgePrimeSearchAscending] using hsearch))).P
          (LucasParams.methodAStar D
              (selfridgePrimeSearchAscending_some_methodA_mod
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
    dsimp [param, LucasParams.methodAStar]
    split <;> rfl
  have hjacobi : jacobiSym param.D n = -1 := by
    simpa only [hD] using
      selfridgePrimeSearchAscending_some_spec
        (by simpa only [selfridgePrimeSearchAscending] using hsearch)
  exact bailliePSWWithParams_of_prime hn param.D param.P param.Q param.discr hjacobi

end PseudoPrime.PrimeTest
