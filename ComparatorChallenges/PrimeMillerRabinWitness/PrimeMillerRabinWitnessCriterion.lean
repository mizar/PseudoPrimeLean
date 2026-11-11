/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Base-nine logarithm Miller–Rabin criterion challenge

This file states the GRH-conditional primality criterion independently of the library proof.
Its theorem is a placeholder for comparison with a solution using Lake's built-in comparator.
The definitions fix the meaning of GRH and the criterion for that comparison.
-/

@[expose] public section

namespace ComparatorChallenges.PrimeMillerRabinWitness

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

/-- The strong Miller–Rabin probable-prime condition for a natural input `n` and base `a`.
With `(s, d) = Nat.maxPowDvdDiv 2 (n - 1)`, it asserts that `a^d = 1` in `ZMod n`, or that
`a^(2^j * d) = -1` for some `j < s`. The proposition is defined for all natural inputs and
expresses the base test used by the prime-base criteria below. -/
def IsStrongMillerRabinProbablePrime (n a : ℕ) : Prop :=
  let (s, d) := Nat.maxPowDvdDiv 2 (n - 1)
  (a : ZMod n) ^ d = 1 ∨ ∃ j : ℕ, j < s ∧ (a : ZMod n) ^ (2 ^ j * d) = -1

/-- Under GRH, an odd natural number `n > 1` is prime if and only if it passes
the strong Miller–Rabin test for every prime base at most
`max 2 ((3 / 11) * (log n)^2)`. The composite direction uses the least
rejecting-prime bound, and the prime direction uses base-two acceptance and
the log-square bound. -/
theorem prime_millerRabin_027_criterion (hGRH : GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) :
    (∀ p : ℕ,
        Nat.Prime p →
          (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) → IsStrongMillerRabinProbablePrime n p) ↔
      Nat.Prime n := by
  sorry

/-- Under GRH, an odd natural number `n > 1` is prime if and only if it passes the strong
Miller–Rabin test for every prime base at most `2 * (logb 9 n)^2`. This states the challenge
for the base-nine logarithmic cutoff; its proof is supplied by the comparator solution. -/
theorem prime_millerRabin_log_nine_criterion (hGRH : GeneralizedRiemannHypothesis) {n : ℕ}
    (hn : 1 < n) (ho : Odd n) :
    (∀ p : ℕ,
        Nat.Prime p → (p : ℝ) ≤ 2 * (Real.logb 9 n) ^ 2 → IsStrongMillerRabinProbablePrime n p) ↔
      Nat.Prime n := by
  sorry

end ComparatorChallenges.PrimeMillerRabinWitness
