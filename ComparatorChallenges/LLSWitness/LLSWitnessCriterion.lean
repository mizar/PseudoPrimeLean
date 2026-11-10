/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-! # LLS subgroup and character witness challenges

These statements fix GRH and the original LLS correction independently of the library proofs.
The theorem placeholders are compared with a separate solution module.
-/

@[expose] public section

namespace ComparatorChallenges.LLSWitness

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

/-- The logarithmic weight of the distinct prime factors of a natural number. This finite sum
appears in the original LLS auxiliary term and is fixed as part of the challenge statement. -/
noncomputable def primeFactorLogSum (q : ℕ) : ℝ :=
  ∑ p ∈ q.primeFactors, Real.log p / (p - 1)

/-- The nonnegative auxiliary term in the original LLS bound, defined from the logarithm and
the prime-factor weight of the modulus. It determines the correction term below. -/
noncomputable def llsAuxiliaryTerm (q : ℕ) : ℝ :=
  max 0 (2 * Real.log (Real.log q) - 8 / 5 - primeFactorLogSum q)

/-- The original LLS nonnegative correction term for a natural modulus. Its squared sum with
the logarithm gives the subgroup witness cutoff in the first proposition. -/
noncomputable def llsCorrectionTerm (q : ℕ) : ℝ :=
  max 0
    (2 * Real.log (Real.log q) + 3 +
        2 * q.primeFactors.card * (Real.log (Real.log q)) ^ 2 / Real.log q -
      2 * llsAuxiliaryTerm q)

/-- Under GRH, for each modulus at least three and each proper subgroup of its unit group,
there is a prime not dividing the modulus whose unit residue is outside the subgroup and is at
most the original LLS cutoff. This is the extended S1 challenge. -/
def LLSSubgroupWitnessBound : Prop :=
  GeneralizedRiemannHypothesis →
    ∀ (q : ℕ) [NeZero q],
      3 ≤ q →
        ∀ H : Subgroup (ZMod q)ˣ,
          H ≠ ⊤ →
            ∃ p : ℕ,
              p.Prime ∧
                ¬p ∣ q ∧
                ∃ u : (ZMod q)ˣ,
                  u ∉ H ∧
                    (u : ZMod q) = (p : ZMod q) ∧ (p : ℝ) ≤ (Real.log q + llsCorrectionTerm q) ^ 2

/-- Under GRH, a nonprincipal complex character at any modulus at least five has a prime with
value different from one at most the squared logarithm of the modulus. The value zero is allowed;
this proposition does not assert that the prime is coprime to the modulus. -/
def LLSCharacterWitnessBound : Prop :=
  GeneralizedRiemannHypothesis →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → 5 ≤ q → ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (Real.log q) ^ 2 ∧ χ p ≠ 1

/-- The extended LLS subgroup witness bound, to be proved by a comparator solution. -/
theorem lls_subgroup_witness_bound : LLSSubgroupWitnessBound := by sorry

/-- The LLS nonprincipal-character witness bound, to be proved by a comparator solution. -/
theorem lls_character_witness_bound : LLSCharacterWitnessBound := by sorry

end ComparatorChallenges.LLSWitness
