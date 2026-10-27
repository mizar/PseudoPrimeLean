/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.FiniteSignedPrefixTriviality
public import PseudoPrime.NumberTheory.DirichletCharacterParity

/-! # Character-independent signed prefix budgets -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Input: rational node-coefficient pairs and a complex Gamma-factor function.
Output: the signed finite log-derivative sum at the shifted nodes.
Role: retain coefficient cancellation before choosing the parity bound. -/
noncomputable def finiteSignedGammaCost (l : List (ℚ × ℚ)) (F : ℂ → ℂ) : ℝ :=
  (l.map (fun ab ↦ (ab.2 : ℝ) * (logDeriv F (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum

/-- Input: rational node-coefficient pairs.
Output: the maximum of the exact even and odd Gamma-factor costs.
Role: give a character-independent bound without taking absolute coefficient values. -/
noncomputable def finiteSignedParityUpper (l : List (ℚ × ℚ)) : ℝ :=
  max (finiteSignedGammaCost l Complex.Gammaℝ)
    (finiteSignedGammaCost l (fun z : ℂ ↦ Complex.Gammaℝ (z + 1)))

/-- Input: any complex Dirichlet character and rational node-coefficient pairs.
Claim: its exact Gamma cost is bounded by the parity maximum.
Proof: its Gamma factor is exactly the even or odd factor.
Role: remove character dependence from the archimedean budget. -/
theorem finiteSignedGammaCost_le_parity_upper {m : ℕ} (χ : DirichletCharacter ℂ m)
    (l : List (ℚ × ℚ)) : finiteSignedGammaCost l χ.gammaFactor ≤ finiteSignedParityUpper l := by
  rcases χ.even_or_odd with he | ho
  · have hf : χ.gammaFactor = Complex.Gammaℝ := funext he.gammaFactor_def
    rw [hf]
    exact le_max_left _ _
  · have hf : χ.gammaFactor = (fun z : ℂ ↦ Complex.Gammaℝ (z + 1)) := funext ho.gammaFactor_def
    rw [hf]
    exact le_max_right _ _

/-- Input: a modulus, rational coefficients, and a finite prime-power prefix.
Output: the conductor term, parity maximum and Euler total minus twice the prefix.
Role: package the character-independent budget when all small primes have value one. -/
noncomputable def finiteSignedTrivialPrefixBudget (m : ℕ) (l : List (ℚ × ℚ)) (B : Finset ℕ) : ℝ :=
  (l.map (fun ab ↦ (ab.2 : ℝ))).sum * (Real.log m / 2) + finiteSignedParityUpper l +
      (∑' k : ℕ, Analysis.finiteSignedMangoldtWeight l k) -
    2 * (∑ k ∈ B, Analysis.finiteSignedMangoldtWeight l k)

/-- Input: a finite prefix below a bound where the character is one on every prime.
Claim: the actual signed prefix budget is at most the character-independent budget.
Proof: cancel the finite defect and bound the signed Gamma cost by its parity maximum.
Role: expose explicit scalar costs to witness contradictions for arbitrary candidates. -/
theorem finiteSignedPrefixBudget_le_of_prime_one {m : ℕ} (χ : DirichletCharacter ℂ m)
    (l : List (ℚ × ℚ)) (B : Finset ℕ) {b : ℝ} (hB : ∀ k ∈ B, (k : ℝ) ≤ b)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → χ p = 1) :
    finiteSignedPrefixBudget χ l B ≤ finiteSignedTrivialPrefixBudget m l B := by
  have he := finiteSigned_prefix_defect_eq_zero_of_prime_one χ l B hB hsmall
  have hg := finiteSignedGammaCost_le_parity_upper χ l
  dsimp only [finiteSignedPrefixBudget, finiteSignedTrivialPrefixBudget,
    finiteSignedGammaCost] at hg ⊢
  rw [he, add_zero]
  linarith only [hg]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
