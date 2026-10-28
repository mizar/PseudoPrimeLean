/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleGammaCharacterBounds
public import PseudoPrime.LLS.QuadraticExcludedBudget
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PairedEulerExcludedBounds

/-! # Paired Euler savings with a combined quadratic exclusion budget -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.DirichletLFunction AnalyticNumberTheory.Arithmetic in
/-- For primitive nonprincipal quadratic GRH data of modulus at least eight, prime
triviality gives a Gamma arithmetic upper bound with one combined exclusion cost.
Use the retained-prefix comparison and the same-modulus explicit remainder.
This supplies the upper side of a finite-scale witness contradiction. -/
theorem gamma_primitive_sum_re_le_twoPole_quadratic_budget {q N : ℕ} [NeZero q] (hq : 8 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x b : ℝ}
    (hx : 1 ≤ x) (S : Finset ℕ) (hS : ∀ n ∈ S, (n : ℝ) ≤ b)
    (ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p N → χ p = 1) :
    (∑' n : ℕ, gammaMellinKernel.summand χ x n).re ≤
      Real.log q / 2 + 419 / 50 -
          2 * (∑ n ∈ S, pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) n) +
        quadraticExcludedBudget q N S (pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4)) +
        64 / 9 +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        x ^ (-9 / 16 : ℝ) * ((3 / 2) * (Real.log q + 28) + 1) := by
  have h := gamma_primitive_sum_re_le_twoPole_from_eight hq hGRH hp hne hinv hx S S
  have he := paired_euler_prefixes_eq_weight χ (5 / 4) (11 / 4) (3 / 4) S
  have hb :=
    paired_weighted_sum_ge_quadratic_budget χ hquad S
      (pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4)) hS
      (fun n _ hn ↦ pairedEulerPrefixWeight_eq_zero_of_mangoldt_eq_zero _ _ _ hn)
      (fun n _ ↦ pairedEulerPrefixWeight_nonneg _ _ (by norm_num only) n) ht
  linarith only [h, he, hb]

end PseudoPrime.LLS.PaperStatements
