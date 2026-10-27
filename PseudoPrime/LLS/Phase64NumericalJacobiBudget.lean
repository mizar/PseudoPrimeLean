/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Phase64TotalEulerJacobiBudget
public import PseudoPrime.LLS.Phase64EulerMass500

/-! # First-cell Jacobi criterion after full Euler-mass certification -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The first-cell Jacobi budget with the full Euler mass bounded by 31/10.
Inputs are the original odd integer, ambient pole modulus and scale. The constant
-129/200 is 31/10-749/200. Only the principal-ramp gap remains to be estimated. -/
noncomputable def phase64NumericalJacobiBudget (n q : ℕ) (x : ℝ) : ℝ :=
  (90992831 / 200000000 : ℝ) * Real.log (4 * (n : ℝ)) + (3 / 100 : ℝ) * Real.log n -
      (129 / 200 : ℝ) +
    ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
    43 * x ^ (-9 / 16 : ℝ)

/-- Under RH, the actual total-Euler budget is bounded by the explicit numerical
budget for any integer inputs and scale. Substitute the certified Euler mass upper bound. -/
theorem phase64_total_budget_le_numerical (hRH : RiemannHypothesis) (n q : ℕ) (x : ℝ) :
    phase64TotalEulerJacobiBudget n q x ≤ phase64NumericalJacobiBudget n q x := by
  have h := phase64_euler_mass_le hRH
  dsimp only [phase64TotalEulerJacobiBudget, phase64NumericalJacobiBudget]
  linarith only [h]

/-- Under GRH and the first-cell conductor hypotheses, absence of odd-prime
negative Jacobi witnesses forces the principal-ramp quantity below the numerical budget.
All Euler, prefix, Gamma and local numerical bounds are proved. -/
theorem phase64_jacobi_no_negative_numerical_comparison {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {L : ℝ} (hlo : 64 ≤ L)
    (hhi : L ≤ 64001 / 1000)
    (hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ L ^ 2 → jacobiSym n p ≠ -1) :
    2 *
          (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum (L ^ 2 / (99 / 40)) /
            Real.sqrt (L ^ 2 / (99 / 40))) -
        (∑' k : ℕ,
            PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1)
              (L ^ 2 / (99 / 40)) k).re ≤
      phase64NumericalJacobiBudget n q (L ^ 2 / (99 / 40)) := by
  exact
    (phase64_jacobi_no_negative_total_comparison bridge hGRH hq hmq hlo hhi hno).trans
      (phase64_total_budget_le_numerical hGRH.riemann n q _)

/-- Under GRH and the first-cell conductor hypotheses, a strict gap above the
explicit numerical budget gives an odd-prime negative Jacobi witness through L^2.
The remaining numerical premise concerns only the principal-ramp quantity. -/
theorem exists_odd_prime_negative_of_phase64_numerical_gap {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {L : ℝ} (hlo : 64 ≤ L)
    (hhi : L ≤ 64001 / 1000)
    (hgap :
      phase64NumericalJacobiBudget n q (L ^ 2 / (99 / 40)) <
        2 *
            (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum (L ^ 2 / (99 / 40)) /
              Real.sqrt (L ^ 2 / (99 / 40))) -
          (∑' k : ℕ,
              PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1)
                (L ^ 2 / (99 / 40)) k).re) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ L ^ 2 ∧ jacobiSym n p = -1 := by
  exact
    exists_odd_prime_negative_of_phase64_total_gap bridge hGRH hq hmq hlo hhi
      ((phase64_total_budget_le_numerical hGRH.riemann n q _).trans_lt hgap)

end PseudoPrime.LLS
