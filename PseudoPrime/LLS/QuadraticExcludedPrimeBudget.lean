/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.QuadraticExcludedEndpoint
public import PseudoPrime.Analysis.FiniteLinearBudget
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.QuadraticExcludedPrimeBudget

/-! # Prime-factor budgets for the combined quadratic endpoint weight -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For every real cutoff and a natural index which is not a prime power, the
combined endpoint weight vanishes. Both Mangoldt terms vanish. This checks the
support hypothesis needed to apply the prime-factor budget to the analytic kernel. -/
theorem excludedEndpointWeight_eq_zero_of_not_primePow (x : ℝ) {n : ℕ} (hn : ¬IsPrimePow n) :
    excludedEndpointWeight x n = 0 := by
  unfold excludedEndpointWeight
  rw [AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm_eq_zero_of_not_primePow hn,
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm_eq_zero_of_not_primePow hn, mul_zero,
    mul_zero, add_zero]

open AnalyticNumberTheory.Arithmetic in
/-- Under primitive nonprincipal quadratic GRH data, q dividing nonzero even N,
x>=64, and a nonnegative logarithmic tail rate, the prime-budget separation
condition gives an odd N-coprime negative prime at most x. Bound the structural
budget and apply the established endpoint witness theorem. The numerical tail
and excess conditions remain explicit certification obligations. -/
theorem exists_odd_prime_neg_one_of_quadratic_prime_budget {q N : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hN : N ≠ 0) (hqN : q ∣ N) (hN2 : 2 ∣ N) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ} (hx : 64 ≤ x) (T : Finset ℕ) {a : ℝ} (ha : 0 ≤ a)
    (htail :
      ∀ p ∈ N.primeFactors,
        p ∉ T → quadraticExcludedPrimeCost q x (excludedEndpointWeight x) p ≤ a * Real.log p)
    (hsep :
      oddEndpointTwoCostLimit q x x 0 0 + a * Real.log N +
          ∑ p ∈ T,
            max 0 (quadraticExcludedPrimeCost q x (excludedEndpointWeight x) p - a * Real.log p) <
        0) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p N ∧ χ p = -1 := by
  have hx0 : 0 ≤ x := le_trans (by norm_num only : (0 : ℝ) ≤ 64) hx
  have hb :=
    quadraticExcludedBudget_le_primeBudget hN q hx0 (excludedEndpointWeight x)
      (fun _ hn ↦ excludedEndpointWeight_eq_zero_of_not_primePow x hn) T ha htail
  apply exists_odd_prime_neg_one_of_quadratic_excluded_budget hq hqN hN2 hGRH hp hne hquad hx
  linarith only [hb, hsep]

end PseudoPrime.LLS.PaperStatements
