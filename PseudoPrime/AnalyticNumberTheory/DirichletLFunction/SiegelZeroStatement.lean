/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-! # A uniform real-zero gap statement -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- The uniform real-zero gap statement asserts the existence of an absolute
positive constant `c` such that every real zero `β ∈ (0, 1)` of a primitive,
nonprincipal real Dirichlet character modulo `q ≥ 3` satisfies
`c ≤ (1 - β) * log q`. This definition records a proposition; it does not
assert that such a constant exists. -/
def SiegelZeroUniformBound : Prop :=
  ∃ c : ℝ,
    0 < c ∧
      ∀ (q : ℕ) [NeZero q],
        3 ≤ q →
          ∀ χ : DirichletCharacter ℂ q,
            χ.IsPrimitive →
              χ ≠ 1 →
              (∀ a : ZMod q, (χ a).im = 0) →
              ∀ β : ℝ, 0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 → c ≤ (1 - β) * Real.log (q : ℝ)

/-- The curried real-zero gap statement is equivalent to the formulation
that groups the three zero conditions in a conjunction. The equivalence
only reorganizes hypotheses and does not establish either statement. -/
theorem siegelZeroUniformBound_iff :
    SiegelZeroUniformBound ↔
      ∃ c : ℝ,
        0 < c ∧
          ∀ (q : ℕ) [NeZero q],
            3 ≤ q →
              ∀ χ : DirichletCharacter ℂ q,
                χ.IsPrimitive →
                  χ ≠ 1 →
                  (∀ a : ZMod q, (χ a).im = 0) →
                  ∀ β : ℝ,
                    (0 < β ∧ β < 1 ∧ χ.LFunction (β : ℂ) = 0) → c ≤ (1 - β) * Real.log (q : ℝ) := by
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, ?_⟩
    intro q _ hq χ hχ hp hr β hβ
    exact h q hq χ hχ hp hr β hβ.1 hβ.2.1 hβ.2.2
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, ?_⟩
    intro q _ hq χ hχ hp hr β hβ0 hβ1 hz
    exact h q hq χ hχ hp hr β ⟨hβ0, hβ1, hz⟩

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
