/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.QuadraticExcludedBudget
public import PseudoPrime.LLS.ExcludedEndpointWitness

/-! # A single quadratic exclusion budget for equal endpoint cutoffs -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.Arithmetic in
/-- At equal cutoffs, combine the reciprocal term with its positive endpoint
coefficient and the logarithmic term divided by sqrt x. The real weight is total;
its nonnegativity on the arithmetic support is proved for x>=1. This retains
cancellation before a single quadratic exclusion budget is applied. -/
noncomputable def excludedEndpointWeight (x : ℝ) (n : ℕ) : ℝ :=
  ((2 + (Real.log x + 2) / Real.sqrt x) / (1 - 1 / Real.sqrt x) ^ 2) *
      reciprocalWeightedMangoldtTerm x n +
    (1 / Real.sqrt x) * logWeightedMangoldtTerm x n

open AnalyticNumberTheory.Arithmetic in
/-- For arbitrary x and character, the endpoint limit with both exact local
defects equals its zero-cost value plus one excluded defect of the combined
weight. Use finite-sum linearity and ring algebra with totalized division. -/
theorem twoCostLimit_eq_zeroCost_add_excluded_weight {q N : ℕ} (χ : DirichletCharacter ℂ q)
    (x : ℝ) :
    oddEndpointTwoCostLimit q x x
        (excludedCharacterDefect χ N (Finset.Ioc 0 ⌊x⌋₊) (reciprocalWeightedMangoldtTerm x))
        (excludedCharacterDefect χ N (Finset.Ioc 0 ⌊x⌋₊) (logWeightedMangoldtTerm x)) =
      oddEndpointTwoCostLimit q x x 0 0 +
        excludedCharacterDefect χ N (Finset.Ioc 0 ⌊x⌋₊) (excludedEndpointWeight x) := by
  unfold excludedEndpointWeight
  rw [excludedCharacterDefect_linear_weight]
  unfold oddEndpointTwoCostLimit oddEndpointCostLimit
  simp only [div_eq_mul_inv]
  ring

open AnalyticNumberTheory.Arithmetic in
/-- For x>=1 and positive n<=floor x, the combined endpoint weight is
nonnegative. Both Mangoldt terms and the reciprocal multiplier are nonnegative.
This supplies the sign condition for the structural quadratic budget. -/
theorem excludedEndpointWeight_nonneg {x : ℝ} (hx : 1 ≤ x) {n : ℕ} (hn : n ∈ Finset.Ioc 0 ⌊x⌋₊) :
    0 ≤ excludedEndpointWeight x n := by
  have hx0 := zero_lt_one.trans_le hx
  have hk : 0 ≤ 2 + (Real.log x + 2) / Real.sqrt x :=
    add_nonneg (by norm_num only)
      (div_nonneg (by linarith only [Real.log_nonneg hx]) (Real.sqrt_nonneg x))
  exact
    add_nonneg
      (mul_nonneg (div_nonneg hk (sq_nonneg _))
        (reciprocalWeightedMangoldtTerm_nonneg hx0 (Finset.mem_Ioc.mp hn).1
          (Finset.mem_Ioc.mp hn).2))
      (mul_nonneg (div_nonneg zero_le_one (Real.sqrt_nonneg x))
        (logWeightedMangoldtTerm_nonneg hx0 (Finset.mem_Ioc.mp hn).1 (Finset.mem_Ioc.mp hn).2))

open AnalyticNumberTheory.Arithmetic in
/-- Under primitive nonprincipal quadratic GRH data, q dividing N, 2 dividing N
and x>=64, negativity of the zero-cost endpoint limit plus one structural budget
gives an odd N-coprime negative prime. Bound the exact combined defect and apply
the established two-cost witness theorem. No character values occur in the budget. -/
theorem exists_odd_prime_neg_one_of_quadratic_excluded_budget {q N : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hqN : q ∣ N) (hN2 : 2 ∣ N) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ} (hx : 64 ≤ x)
    (hsep :
      oddEndpointTwoCostLimit q x x 0 0 +
          quadraticExcludedBudget q N (Finset.Ioc 0 ⌊x⌋₊) (excludedEndpointWeight x) <
        0) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p N ∧ χ p = -1 := by
  have hx1 : 1 < x := by linarith only [hx]
  have hm :=
    excludedCharacterDefect_le_quadratic_budget χ hquad N (Finset.Ioc 0 ⌊x⌋₊)
      (excludedEndpointWeight x) (fun _ hn ↦ excludedEndpointWeight_nonneg hx1.le hn)
  have he := twoCostLimit_eq_zeroCost_add_excluded_weight (N := N) χ x
  have hlim :
    oddEndpointTwoCostLimit q x x
        (excludedCharacterDefect χ N (Finset.Ioc 0 ⌊x⌋₊) (reciprocalWeightedMangoldtTerm x))
        (excludedCharacterDefect χ N (Finset.Ioc 0 ⌊x⌋₊) (logWeightedMangoldtTerm x)) <
      0 := by
    linarith only [he, hm, hsep]
  exact
    exists_odd_prime_neg_one_of_excluded_two_cost_limit_neg hq hqN hN2 hGRH hp hne hquad hx1 hx
      (le_refl _) (le_refl _) (le_refl _) hlim

end PseudoPrime.LLS.PaperStatements
