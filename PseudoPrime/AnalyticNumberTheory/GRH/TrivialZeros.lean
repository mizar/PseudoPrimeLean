/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Trivial zeros for Dirichlet characters

This definition is independent of the generalized Riemann hypothesis predicate and downstream
constructions. The modulus-one branch excludes negative even integers; other branches follow the
parity of the character.
-/

namespace PseudoPrime.AnalyticNumberTheory.GRH

/--
Input: a Dirichlet character.
Output: its prescribed trivial-zero set as integers.
For modulus one exclude negative even integers; otherwise use negative odd integers for odd
characters and nonpositive even integers for even characters. Used to state primitive GRH.
-/
noncomputable def dirichletTrivialZeros {q : ℕ} (χ : DirichletCharacter ℂ q) : Set ℤ := by
  classical
    exact
    if q = 1 then {z | ∃ n : ℕ, z = -2 * ((n : ℤ) + 1)}
    else if χ.Odd then {z | ∃ n : ℕ, z = -2 * (n : ℤ) - 1} else {z | ∃ n : ℕ, z = -2 * (n : ℤ)}

end PseudoPrime.AnalyticNumberTheory.GRH
