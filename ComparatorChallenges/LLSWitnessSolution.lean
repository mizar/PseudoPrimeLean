/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Part1FromThree
public import PseudoPrime.LLS.CharacterPart2FromFive
public import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-! # LLS subgroup and character witness challenges

These statements reproduce GRH and the original LLS correction for comparison.
The theorems below apply the library proofs without importing the challenge module.
-/

@[expose] public section

namespace ComparatorChallenges

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

/-- The extended subgroup witness bound follows from the library S1 theorem. -/
theorem lls_subgroup_witness_bound : LLSSubgroupWitnessBound := fun hGRH q _ hq H hH ↦
  PseudoPrime.LLS.llsTheorem11S1_from_three_of_grh hGRH q hq H hH

/-- The nonprincipal-character witness bound follows from the library S2 theorem. -/
theorem lls_character_witness_bound : LLSCharacterWitnessBound := fun hGRH q _ χ hne hq ↦
  PseudoPrime.LLS.exists_prime_not_one_le_log_sq_from_five (q := q) χ hne hq hGRH

end ComparatorChallenges
