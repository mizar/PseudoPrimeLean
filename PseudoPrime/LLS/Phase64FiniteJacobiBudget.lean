/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.Phase64RamifiedTailBounds
public import PseudoPrime.LLS.Phase64JacobiConductorBudget

/-! # First-phase Jacobi comparison with a fixed finite ramified budget -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: the original integer, ambient pole modulus, scale and prefix cutoff.
Output: the first-phase budget with the fixed 24-prime ramified excess and the
single (3/100) log n allowance. No character, conductor factorization or selected
local prime set occurs in this definition. The remaining scalar gap is not assumed here. -/
noncomputable def phase64FiniteJacobiBudget (n q : ℕ) (x b : ℝ) : ℝ :=
  (Analysis.phaseResolvent64Coefficients.map
            (fun ab ↦
              (ab.2 : ℝ) * (logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
        (∑' k : ℕ, Analysis.finiteSignedMangoldtWeight Analysis.phaseResolvent64Coefficients k) -
      2 *
        (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊,
          Analysis.finiteSignedMangoldtWeight Analysis.phaseResolvent64Coefficients k) +
    (90992831 / 200000000 : ℝ) * Real.log (4 * (n : ℝ)) +
    (427 / 500 : ℝ) +
    (3 / 100 : ℝ) * Real.log n +
    Analysis.phase64RamifiedExcess x +
    ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
    43 * x ^ (-9 / 16 : ℝ)

/-- For actual primitive Jacobi data and scales 1600 to 1700, the character-
dependent ramified budget is bounded by the factorization-independent finite budget.
Apply the exact signed dual cap and the even Gamma-factor identity; no GRH is needed. -/
theorem phase64_ramified_budget_le_finite {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (q : ℕ) {x : ℝ} (hlo : 1600 ≤ x)
    (hhi : x ≤ 1700) (b : ℝ) :
    phase64RamifiedJacobiBudget bridge q x b ≤ phase64FiniteJacobiBudget n q x b := by
  have hr :=
    Analysis.phase64_actual_ramified_cost_le_finite_dual hn
      (n.primeFactors.filter (fun p : ℕ ↦ bridge.character p = 0)) (Finset.filter_subset _ _)
      bridge.character (fun p hp ↦ (Finset.mem_filter.mp hp).2)
      (AnalyticNumberTheory.DirichletLFunction.gammaPrefixPowerIndices b) hlo hhi
  have he : bridge.character.gammaFactor = Complex.Gammaℝ :=
    funext (fun z ↦ bridge.character_even.gammaFactor_def z)
  dsimp only [phase64RamifiedJacobiBudget, phase64FiniteJacobiBudget]
  rw [he]
  linarith only [hr]

/-- Under GRH and the certified first level cell, absence of negative odd-prime
Jacobi witnesses forces the ramp-minus-principal quantity below the finite budget.
The proved conductor and signed ramified reductions remove all local numerical
hypotheses depending on the input factors. -/
theorem phase64_jacobi_no_negative_finite_comparison {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
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
      phase64FiniteJacobiBudget n q (L ^ 2 / (99 / 40)) (L ^ 2) := by
  have hx := Analysis.scale64_cell_of_level hlo hhi
  have hxlo := (by norm_num only : (1600 : ℝ) ≤ 163840 / 99).trans hx.1
  have hxhi := hx.2.trans (by norm_num only : (4096128001 / 2475000 : ℝ) ≤ 1700)
  exact
    (phase64_jacobi_no_negative_local_comparison bridge hGRH hq hmq hlo hhi hno).trans
      ((phase64_jacobi_local_budget_le_ramified bridge q hxlo (L ^ 2)).trans
        (phase64_ramified_budget_le_finite bridge q hxlo hxhi (L ^ 2)))

/-- Under GRH and the first-cell ambient-conductor hypotheses, a strict gap for
the factorization-independent finite budget yields an odd-prime negative Jacobi
witness through L^2. The fixed signed excess and the scalar gap remain explicit
numerical targets; no new whole-halfline entrance is asserted. -/
theorem exists_odd_prime_negative_of_phase64_finite_gap {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {L : ℝ} (hlo : 64 ≤ L)
    (hhi : L ≤ 64001 / 1000)
    (hgap :
      phase64FiniteJacobiBudget n q (L ^ 2 / (99 / 40)) (L ^ 2) <
        2 *
            (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum (L ^ 2 / (99 / 40)) /
              Real.sqrt (L ^ 2 / (99 / 40))) -
          (∑' k : ℕ,
              PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1)
                (L ^ 2 / (99 / 40)) k).re) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ L ^ 2 ∧ jacobiSym n p = -1 := by
  have hx := Analysis.scale64_cell_of_level hlo hhi
  have hxlo := (by norm_num only : (1600 : ℝ) ≤ 163840 / 99).trans hx.1
  have hxhi := hx.2.trans (by norm_num only : (4096128001 / 2475000 : ℝ) ≤ 1700)
  exact
    exists_odd_prime_negative_of_phase64_ramified_gap bridge hGRH hq hmq hlo hhi
      ((phase64_ramified_budget_le_finite bridge q hxlo hxhi (L ^ 2)).trans_lt hgap)

end PseudoPrime.LLS
