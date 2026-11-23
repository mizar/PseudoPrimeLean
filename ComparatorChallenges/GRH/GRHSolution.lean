/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import PseudoPrime.AnalyticNumberTheory.GRH.EquivalentForms
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-! # Four equivalent formulations of RH and GRH -/

@[expose] public section

namespace ComparatorChallenges.GRH

/-- Integer arguments excluded as trivial zeros for a complex Dirichlet character. The
modulus-one case uses negative even integers; otherwise parity selects the nonpositive even
or negative odd integers. This set specifies the zero exclusions used in GRH. -/
noncomputable def dirichletTrivialZeros {q : ℕ} (χ : DirichletCharacter ℂ q) : Set ℤ := by
  classical
    exact
    if q = 1 then {z | ∃ n : ℕ, z = -2 * ((n : ℤ) + 1)}
    else if χ.Odd then {z | ∃ n : ℕ, z = -2 * (n : ℤ) - 1} else {z | ∃ n : ℕ, z = -2 * (n : ℤ)}

/-- For a character of nonzero modulus, zeros outside the excluded integer set have real part
one half. This character-level condition is used to formulate GRH. -/
def DirichletRiemannHypothesis {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ s : ℂ,
    χ.LFunction s = 0 → s ∉ (Int.cast : ℤ → ℂ) '' dirichletTrivialZeros χ → s.re = (1 : ℝ) / 2

/-- Every primitive complex Dirichlet character of nonzero modulus satisfies the character-level
Riemann hypothesis. This is the explicit assumption in both witness propositions. -/
def GeneralizedRiemannHypothesis : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → DirichletRiemannHypothesis χ

/-- The Dirichlet Riemann hypothesis for the trivial character modulo one is equivalent to
the Riemann hypothesis for the Riemann zeta function. Identify the character's L-function and
trivial zeros with those of zeta, and use the nonvanishing convention at one. This equivalence
connects the challenge's GRH formulation to the ordinary Riemann hypothesis. -/
theorem dirichletRiemannHypothesis_one_iff :
    DirichletRiemannHypothesis (1 : DirichletCharacter ℂ 1) ↔ RiemannHypothesis := by
  classical
  have htriv (s : ℂ) :
    s ∈ (Int.cast : ℤ → ℂ) '' dirichletTrivialZeros (1 : DirichletCharacter ℂ 1) ↔
      ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    simp only [Set.mem_image]
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      refine ⟨n, ?_⟩
      push_cast
      ring
    · rintro ⟨n, rfl⟩
      refine ⟨-2 * ((n : ℤ) + 1), ⟨n, rfl⟩, ?_⟩
      push_cast
      ring
  simp only [DirichletRiemannHypothesis, DirichletCharacter.LFunction_modOne_eq, htriv]
  constructor
  · intro h s hs ht _
    exact h s hs ht
  · intro h s hs ht
    exact h s hs ht (fun he => riemannZeta_one_ne_zero (he ▸ hs))

/-- The challenge's generalized Riemann hypothesis implies the Riemann hypothesis. Apply GRH
to the primitive trivial character modulo one and use the modulus-one equivalence. This provides
the ordinary hypothesis to results that need only the Riemann zeta function. -/
theorem GeneralizedRiemannHypothesis.riemann (h : GeneralizedRiemannHypothesis) :
    RiemannHypothesis := by
  have hDirichlet : DirichletRiemannHypothesis 1 :=
    h 1 1 DirichletCharacter.isPrimitive_one_level_one
  exact dirichletRiemannHypothesis_one_iff.mp hDirichlet

/-- The Riemann zeta function's zeros outside the negative even integers lie on the critical
line. The point `1` is explicitly excluded, matching mathlib's Riemann hypothesis. -/
def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

/-- For every complex Dirichlet character of nonzero modulus, its L-function is nonzero to
the right of the critical line, excluding the principal character at `1`. -/
def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- Every zero in the open critical strip of any complex Dirichlet L-function of nonzero
modulus lies on the critical line. -/
def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- Every zero in the open critical strip of a primitive complex Dirichlet L-function of
nonzero modulus lies on the critical line. -/
def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    χ.IsPrimitive →
      ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- The zeta formulation is exactly mathlib's Riemann hypothesis: the definitions agree. -/
theorem riemannZetaZerosOnLine_iff : RiemannZetaZerosOnLine ↔ RiemannHypothesis := by
  exact PseudoPrime.AnalyticNumberTheory.GRH.riemannZetaZerosOnLine_iff

/-- The right-half-plane nonvanishing formulation is equivalent to GRH. Reflection supplies
the primitive zero statement, and GRH supplies nonvanishing for all characters. -/
theorem nonvanishing_right_iff_grh :
    DirichletLNonvanishingRightOfHalf ↔ GeneralizedRiemannHypothesis := by
  exact PseudoPrime.AnalyticNumberTheory.GRH.nonvanishing_right_iff_grh

/-- The open-strip formulation for all Dirichlet characters is equivalent to GRH. Restriction
to primitive characters gives one direction; zero transfer and the principal Euler product give
the other. -/
theorem zeros_on_line_iff_grh : DirichletLZerosOnLine ↔ GeneralizedRiemannHypothesis := by
  exact PseudoPrime.AnalyticNumberTheory.GRH.zeros_on_line_iff_grh

/-- The primitive open-strip formulation is equivalent to GRH. The forward implication first
recovers RH from the modulus-one character, then separates principal and nonprincipal characters. -/
theorem primitive_zeros_on_line_iff_grh :
    PrimitiveDirichletLZerosOnLine ↔ GeneralizedRiemannHypothesis := by
  exact PseudoPrime.AnalyticNumberTheory.GRH.primitive_zeros_on_line_iff_grh

end ComparatorChallenges.GRH
