/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Phase64FiniteJacobiBudget
public import PseudoPrime.Analysis.Phase64RamifiedExcessBounds

/-! # First-phase Jacobi witness criterion with all local costs certified -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: the original integer, ambient pole modulus, scale and prefix cutoff.
Output: the character-free signed Gamma and Euler budget after all local costs
have certified numerical allowances. The constant 1727/500 is 427/500+13/5.
Only the global scalar Gamma, Euler-prefix and principal-ramp comparison remains. -/
noncomputable def phase64ScalarJacobiBudget (n q : ℕ) (x b : ℝ) : ℝ :=
  (Analysis.phaseResolvent64Coefficients.map
            (fun ab ↦
              (ab.2 : ℝ) * (logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
        (∑' k : ℕ, Analysis.finiteSignedMangoldtWeight Analysis.phaseResolvent64Coefficients k) -
      2 *
        (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊,
          Analysis.finiteSignedMangoldtWeight Analysis.phaseResolvent64Coefficients k) +
    (90992831 / 200000000 : ℝ) * Real.log (4 * (n : ℝ)) +
    (3 / 100 : ℝ) * Real.log n +
    (1727 / 500 : ℝ) +
    ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
    43 * x ^ (-9 / 16 : ℝ)

/-- On the whole scale interval 1600 to 1660, the fixed-prime budget is bounded
by the scalar budget. Substitute the proved real excess cap 13/5; no local
numerical or factorization hypothesis is required. -/
theorem phase64_finite_budget_le_scalar (n q : ℕ) {x : ℝ} (hlo : 1600 ≤ x) (hhi : x ≤ 1660)
    (b : ℝ) : phase64FiniteJacobiBudget n q x b ≤ phase64ScalarJacobiBudget n q x b := by
  have he := Analysis.phase64_ramified_excess_le_thirteen_fifths hlo hhi
  dsimp only [phase64FiniteJacobiBudget, phase64ScalarJacobiBudget]
  linarith only [he]

/-- Under GRH and the first-cell conductor hypotheses, absence of negative
odd-prime Jacobi witnesses forces the actual ramp-minus-principal sum below
the scalar budget. All local numerical comparisons have been proved. -/
theorem phase64_jacobi_no_negative_scalar_comparison {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
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
      phase64ScalarJacobiBudget n q (L ^ 2 / (99 / 40)) (L ^ 2) := by
  have hx := Analysis.scale64_cell_of_level hlo hhi
  have hxlo := (by norm_num only : (1600 : ℝ) ≤ 163840 / 99).trans hx.1
  have hxhi := hx.2.trans (by norm_num only : (4096128001 / 2475000 : ℝ) ≤ 1660)
  exact
    (phase64_jacobi_no_negative_finite_comparison bridge hGRH hq hmq hlo hhi hno).trans
      (phase64_finite_budget_le_scalar n q hxlo hxhi (L ^ 2))

/-- Under GRH and the first-cell conductor hypotheses, a strict scalar-budget
gap gives an odd-prime negative Jacobi witness through L^2. No unproved local-cost
or spectral premise remains. The global scalar gap is still an explicit hypothesis. -/
theorem exists_odd_prime_negative_of_phase64_scalar_gap {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {L : ℝ} (hlo : 64 ≤ L)
    (hhi : L ≤ 64001 / 1000)
    (hgap :
      phase64ScalarJacobiBudget n q (L ^ 2 / (99 / 40)) (L ^ 2) <
        2 *
            (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum (L ^ 2 / (99 / 40)) /
              Real.sqrt (L ^ 2 / (99 / 40))) -
          (∑' k : ℕ,
              PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1)
                (L ^ 2 / (99 / 40)) k).re) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ L ^ 2 ∧ jacobiSym n p = -1 := by
  have hx := Analysis.scale64_cell_of_level hlo hhi
  have hxlo := (by norm_num only : (1600 : ℝ) ≤ 163840 / 99).trans hx.1
  have hxhi := hx.2.trans (by norm_num only : (4096128001 / 2475000 : ℝ) ≤ 1660)
  exact
    exists_odd_prime_negative_of_phase64_finite_gap bridge hGRH hq hmq hlo hhi
      ((phase64_finite_budget_le_scalar n q hxlo hxhi (L ^ 2)).trans_lt hgap)

end PseudoPrime.LLS
