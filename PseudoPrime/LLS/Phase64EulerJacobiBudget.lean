/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Phase64ScalarJacobiBudget
public import PseudoPrime.AnalyticNumberTheory.Gamma.Phase64EvenGammaBounds

/-! # First-phase Jacobi budget with the Gamma correction certified -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: the original integer, ambient pole modulus, scale and prefix cutoff.
Output: the character-free Jacobi budget after the new signed Gamma correction
has been certified. The constant 391/200 equals 1727/500-1499/1000. The remaining
quantitative terms are the common Euler sum, prefix, pole and principal-ramp comparison. -/
noncomputable def phase64EulerJacobiBudget (n q : ℕ) (x b : ℝ) : ℝ :=
  (∑' k : ℕ, Analysis.finiteSignedMangoldtWeight Analysis.phaseResolvent64Coefficients k) -
      2 *
        (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊,
          Analysis.finiteSignedMangoldtWeight Analysis.phaseResolvent64Coefficients k) +
    (90992831 / 200000000 : ℝ) * Real.log (4 * (n : ℝ)) +
    (3 / 100 : ℝ) * Real.log n +
    (391 / 200 : ℝ) +
    ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
    43 * x ^ (-9 / 16 : ℝ)

/-- For every input and scale, the scalar budget is bounded by the Euler-only
budget. Substitute the new phase-specific Gamma certificate -1499/1000. This
comparison does not assume GRH, a witness condition or a scale entrance. -/
theorem phase64_scalar_budget_le_euler (n q : ℕ) (x b : ℝ) :
    phase64ScalarJacobiBudget n q x b ≤ phase64EulerJacobiBudget n q x b := by
  have h := AnalyticNumberTheory.Gamma.phase64_even_gamma_correction_le
  dsimp only [phase64ScalarJacobiBudget, phase64EulerJacobiBudget]
  linarith only [h]

/-- Under GRH and the certified first-cell conductor hypotheses, absence of
negative odd-prime Jacobi witnesses forces the ramp-minus-principal sum below
the Euler-only budget. All local costs and the Gamma-factor correction are certified. -/
theorem phase64_jacobi_no_negative_euler_comparison {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
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
      phase64EulerJacobiBudget n q (L ^ 2 / (99 / 40)) (L ^ 2) := by
  exact
    (phase64_jacobi_no_negative_scalar_comparison bridge hGRH hq hmq hlo hhi hno).trans
      (phase64_scalar_budget_le_euler n q (L ^ 2 / (99 / 40)) (L ^ 2))

/-- Under GRH and the first-cell conductor hypotheses, a strict Euler-budget
gap gives an odd-prime negative Jacobi witness through L^2. Only the remaining
global Euler-prefix and principal-ramp numerical comparison is assumed. -/
theorem exists_odd_prime_negative_of_phase64_euler_gap {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {L : ℝ} (hlo : 64 ≤ L)
    (hhi : L ≤ 64001 / 1000)
    (hgap :
      phase64EulerJacobiBudget n q (L ^ 2 / (99 / 40)) (L ^ 2) <
        2 *
            (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum (L ^ 2 / (99 / 40)) /
              Real.sqrt (L ^ 2 / (99 / 40))) -
          (∑' k : ℕ,
              PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1)
                (L ^ 2 / (99 / 40)) k).re) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ L ^ 2 ∧ jacobiSym n p = -1 := by
  exact
    exists_odd_prime_negative_of_phase64_scalar_gap bridge hGRH hq hmq hlo hhi
      ((phase64_scalar_budget_le_euler n q (L ^ 2 / (99 / 40)) (L ^ 2)).trans_lt hgap)

end PseudoPrime.LLS
