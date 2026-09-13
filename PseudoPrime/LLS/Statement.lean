/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactors
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.JacobiCharacterInducedZeros

/-!
# Statement of the Lamzouri--Li--Soundararajan bound

This file specifies both proper-subgroup conclusions of Theorem 1.1 of Lamzouri, Li, and
Soundararajan and the character-kernel specialization of Part 1. These are propositions, not
proofs from GRH. Later algebraic and finite arguments may take `llsTheorem11S1Character` as a
hypothesis.
-/

namespace PseudoPrime.LLS

/-- The nonnegative auxiliary term `A(q)` from LLS Theorem 1.1. -/
noncomputable def llsAuxiliaryTerm (q : ℕ) : ℝ :=
  max 0
    (2 * Real.log (Real.log q) - 8 / 5 -
      AnalyticNumberTheory.Arithmetic.primeFactorLogSum q)

/-- The LLS auxiliary term is nonnegative by construction. -/
theorem llsAuxiliaryTerm_nonneg (q : ℕ) : 0 ≤ llsAuxiliaryTerm q :=
  le_max_left 0 _

/-- The correction term `B(q)` from LLS Theorem 1.1. -/
noncomputable def llsCorrectionTerm (q : ℕ) : ℝ :=
  max 0
    (2 * Real.log (Real.log q) + 3 +
        2 * q.primeFactors.card * (Real.log (Real.log q)) ^ 2 / Real.log q -
      2 * llsAuxiliaryTerm q)

/-- The LLS correction term is nonnegative by construction. -/
theorem llsCorrectionTerm_nonneg (q : ℕ) : 0 ≤ llsCorrectionTerm q :=
  le_max_left 0 _

/--
The part of Lamzouri--Li--Soundararajan Theorem 1.1 used in this module.

For every nontrivial complex Dirichlet character of level `q ≥ 3000`, there is a prime `ℓ` not
dividing `q`, with character value different from `1`, at or below the explicit LLS bound. This
is the character-kernel specialization of the theorem's proper-subgroup formulation.
-/
def llsTheorem11S1Character : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    3000 ≤ q →
      χ ≠ 1 → ∃ ℓ : ℕ, ℓ.Prime ∧ ¬ℓ ∣ q ∧ χ ℓ ≠ 1 ∧ (ℓ : ℝ) ≤ (Real.log q + llsCorrectionTerm q) ^ 2

/-!
The following two propositions record the original proper-subgroup shape of LLS Theorem 1.1.
They are specifications, not proofs. GRH is not a premise inside these propositions: a theorem
establishing either specification must supply its analytic assumptions separately. The
character-valued statement `llsTheorem11S1Character` is distinct from these proper-subgroup
specifications.
-/

/-- A prime residue outside a proper subgroup of `(ZMod q)ˣ`, with the LLS Theorem 1.1 bound. -/
def llsTheorem11S1 : Prop :=
  ∀ (q : ℕ) [NeZero q],
    3000 ≤ q →
      ∀ H : Subgroup (ZMod q)ˣ,
        H ≠ ⊤ →
          ∃ ℓ : ℕ,
            ℓ.Prime ∧
              ¬ℓ ∣ q ∧
              ∃ u : (ZMod q)ˣ,
                u ∉ H ∧
                  (u : ZMod q) = (ℓ : ZMod q) ∧ (ℓ : ℝ) ≤ (Real.log q + llsCorrectionTerm q) ^ 2

/--
The small-prime-exclusion branch of the original proper-subgroup statement.  The premise records
that every prime strictly below `(log q)²` does not divide `q`. The conclusion supplies a prime
at or below that cutoff whose residue is outside the image of the given subgroup in `ZMod q`.
It does not require the residue to be a unit: a prime divisor at the equality endpoint is allowed.
-/
def llsTheorem11S2 : Prop :=
  ∀ (q : ℕ) [NeZero q],
    3000 ≤ q →
      (∀ p : ℕ, p.Prime → (p : ℝ) < (Real.log q) ^ 2 → ¬p ∣ q) →
      ∀ H : Subgroup (ZMod q)ˣ,
        H ≠ ⊤ →
          ∃ ℓ : ℕ,
            ℓ.Prime ∧
              (ℓ : ℝ) ≤ (Real.log q) ^ 2 ∧ ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (ℓ : ZMod q)

end PseudoPrime.LLS
