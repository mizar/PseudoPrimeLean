/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! # Quasi-Riemann hypotheses for zeta and Dirichlet L-functions -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.GRH

/-- The quasi-Riemann hypothesis for the Riemann zeta function asserts that
`riemannZeta s` is nonzero at every complex `s` with `7/8 < s.re`. This is
the proposition stated by the QuasiRiemannHypothesis comparator challenge. -/
def QuasiRiemannHypothesis : Prop :=
  ∀ s : ℂ, (7 / 8 : ℝ) < s.re → riemannZeta s ≠ 0

/-- The Dirichlet quasi-Riemann hypothesis asserts that, for every nonzero
modulus `q` and every Dirichlet character modulo `q`, the associated L-function
is nonzero when `7/8 < s.re`, except at the principal-character pole `s = 1`.
This is the proposition stated by the DirichletSevenEighths comparator challenge. -/
def DirichletQuasiRiemannHypothesis : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    (7 / 8 : ℝ) < s.re → ¬(χ = 1 ∧ s = 1) → χ.LFunction s ≠ 0

end PseudoPrime.AnalyticNumberTheory.GRH
