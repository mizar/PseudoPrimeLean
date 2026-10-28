/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleGammaCharacterBounds
public import PseudoPrime.LLS.QuadraticExcludedBudget
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LLSPairedEulerExcludedBounds

/-! # Paired Euler savings with a combined quadratic exclusion budget -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For primitive nonprincipal quadratic individual-RH data, prime triviality below
an ambient cutoff bounds the convergent Gamma zero mass by a principal finite sum
and its quadratic exclusion budget. Combine the signed two-pole profile with the
weighted defect identity. The exclusion modulus need not equal the conductor. -/
theorem gamma_zeroMass_le_twoPole_quadratic_budget {q N : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {b : ℝ} (S : Finset ℕ)
    (hS : ∀ n ∈ S, (n : ℝ) ≤ b) (ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p N → χ p = 1) :
    Summable
        (fun ρ : ℂ ↦
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖Complex.Gamma ρ‖) ∧
      (∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖Complex.Gamma ρ‖) ≤
        Real.log q / 2 + 419 / 50 -
            2 * (∑ n ∈ S, Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) n) +
          Arithmetic.quadraticExcludedBudget q N S
            (Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4)) := by
  have h := gamma_zeroMass_le_twoPole_rational_retained hq hRH hp hne hinv S S
  have he := Arithmetic.paired_euler_prefixes_eq_weight χ (5 / 4) (11 / 4) (3 / 4) S
  have hb :=
    Arithmetic.paired_weighted_sum_ge_quadratic_budget χ hquad S
      (Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4)) hS
      (fun n _ hn ↦ Arithmetic.pairedEulerPrefixWeight_eq_zero_of_mangoldt_eq_zero _ _ _ hn)
      (fun n _ ↦ Arithmetic.pairedEulerPrefixWeight_nonneg _ _ (by norm_num only) n) ht
  refine ⟨h.1, ?_⟩
  linarith only [h.2, he, hb]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
