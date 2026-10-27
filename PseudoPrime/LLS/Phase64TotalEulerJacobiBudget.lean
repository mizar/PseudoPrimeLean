/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Phase64EulerJacobiBudget
public import PseudoPrime.Analysis.Phase64EulerPrefixSeed

/-! # First-phase Jacobi budget with the finite prefix certified -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: the original integer, ambient pole modulus and scale. Output: the
Jacobi budget after the signed prefix lower bound through 500 is certified.
The constant -749/200 is 391/200-2*(57/20). Only the full common Euler mass
and the principal-ramp comparison remain quantitatively unevaluated. -/
noncomputable def phase64TotalEulerJacobiBudget (n q : ℕ) (x : ℝ) : ℝ :=
  (∑' k : ℕ, Analysis.finiteSignedMangoldtWeight Analysis.phaseResolvent64Coefficients k) +
        (90992831 / 200000000 : ℝ) * Real.log (4 * (n : ℝ)) +
        (3 / 100 : ℝ) * Real.log n -
      (749 / 200 : ℝ) +
    ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
    43 * x ^ (-9 / 16 : ℝ)

/-- For every cutoff at least 500, the Euler-prefix budget is bounded by the
total-Euler budget. Substitute the proved nonnegative-prefix seed lower bound;
no GRH or scale restriction is needed for this algebraic comparison. -/
theorem phase64_euler_budget_le_total (n q : ℕ) (x : ℝ) {b : ℝ} (hb : 500 ≤ b) :
    phase64EulerJacobiBudget n q x b ≤ phase64TotalEulerJacobiBudget n q x := by
  have hp := Analysis.phase64_prefix_lower_of_cutoff_ge_500 hb
  dsimp only [phase64EulerJacobiBudget, phase64TotalEulerJacobiBudget]
  linarith only [hp]

/-- Under GRH and the first-cell conductor hypotheses, absence of negative
odd-prime Jacobi witnesses forces the ramp-minus-principal quantity below the
total-Euler budget. The finite prefix, Gamma and local costs are all certified. -/
theorem phase64_jacobi_no_negative_total_comparison {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
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
      phase64TotalEulerJacobiBudget n q (L ^ 2 / (99 / 40)) := by
  have hb : (500 : ℝ) ≤ L ^ 2 :=
    (by norm_num only : (500 : ℝ) ≤ 64 ^ 2).trans
      (pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 64) hlo 2)
  exact
    (phase64_jacobi_no_negative_euler_comparison bridge hGRH hq hmq hlo hhi hno).trans
      (phase64_euler_budget_le_total n q (L ^ 2 / (99 / 40)) hb)

/-- Under GRH and the first-cell conductor hypotheses, a strict total-Euler
budget gap gives an odd-prime negative Jacobi witness through L^2. The actual
prefix needs no numerical premise; only the full Euler mass and the principal-
ramp numerical comparison remain. -/
theorem exists_odd_prime_negative_of_phase64_total_gap {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {L : ℝ} (hlo : 64 ≤ L)
    (hhi : L ≤ 64001 / 1000)
    (hgap :
      phase64TotalEulerJacobiBudget n q (L ^ 2 / (99 / 40)) <
        2 *
            (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum (L ^ 2 / (99 / 40)) /
              Real.sqrt (L ^ 2 / (99 / 40))) -
          (∑' k : ℕ,
              PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1)
                (L ^ 2 / (99 / 40)) k).re) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ L ^ 2 ∧ jacobiSym n p = -1 := by
  have hb : (500 : ℝ) ≤ L ^ 2 :=
    (by norm_num only : (500 : ℝ) ≤ 64 ^ 2).trans
      (pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 64) hlo 2)
  exact
    exists_odd_prime_negative_of_phase64_euler_gap bridge hGRH hq hmq hlo hhi
      ((phase64_euler_budget_le_total n q (L ^ 2 / (99 / 40)) hb).trans_lt hgap)

end PseudoPrime.LLS
