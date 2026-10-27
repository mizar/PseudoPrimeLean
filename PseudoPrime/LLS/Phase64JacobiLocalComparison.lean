/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaPhaseFirstCellBounds
public import PseudoPrime.LLS.GammaResolventCharacterComparison
public import PseudoPrime.LLS.GammaNoNegativeRampSupport
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.FiniteSignedPrimeIndexedPrefix
public import PseudoPrime.Analysis.Phase64FirstCellLocalBounds

/-! # Actual first-cell Jacobi comparison with signed local costs -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: actual Jacobi character data, an ambient pole modulus, scale and prefix cutoff.
Output: the first-phase signed prefix budget with its character defect replaced by
actual ambient prime local costs, plus the proved pole and left remainder allowances.
Role: retain all arithmetic local losses in the first-cell witness comparison. -/
noncomputable def phase64JacobiLocalBudget {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (q : ℕ) (x b : ℝ) : ℝ :=
  AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget bridge.character
        Analysis.phaseResolvent64Coefficients (Finset.Ioc 0 ⌊b⌋₊) -
      (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊,
        (1 - (bridge.character k).re) *
          Analysis.finiteSignedMangoldtWeight Analysis.phaseResolvent64Coefficients k) +
    (∑ p ∈ (4 * n).primeFactors,
      Analysis.finiteSignedActualPrimeLocalCost Analysis.phaseResolvent64Coefficients
        bridge.character p (AnalyticNumberTheory.DirichletLFunction.gammaPrefixPowerIndices b p)
        x) +
    ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
    43 * x ^ (-9 / 16 : ℝ)

open AnalyticNumberTheory.DirichletLFunction in
/-- Under GRH and the certified level cell, absence of negative odd-prime Jacobi
witnesses through `L^2` forces the actual ramp-minus-principal quantity below the
signed local budget. Combine the proved phase majorant, ambient ramp reduction,
and exact signed prime-prefix reindexing; no spectral comparison premise remains. -/
theorem phase64_jacobi_no_negative_local_comparison {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
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
      phase64JacobiLocalBudget bridge q (L ^ 2 / (99 / 40)) (L ^ 2) := by
  let : NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    ⟨(lt_of_lt_of_le (by norm_num only : (0 : ℕ) < 3) (gamma_jacobi_modulus_ge_three bridge)).ne'⟩
  have hx0 : 0 < L ^ 2 / (99 / 40 : ℝ) :=
    lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 163840 / 99)
      (Analysis.scale64_cell_of_level hlo hhi).1
  have hb : (1 : ℝ) ≤ L ^ 2 := by nlinarith only [hlo, sq_nonneg L]
  have he : (99 / 40 : ℝ) * (L ^ 2 / (99 / 40)) = L ^ 2 := by ring
  have hinv : bridge.character⁻¹ ≠ 1 := by
    rw [bridge.character_quadratic.inv]
    exact bridge.character_ne_one
  have hc :=
    PaperStatements.gamma_primitive_sum_re_le_phase64_first_cell hq
      (gamma_jacobi_modulus_ge_three bridge) hmq hGRH bridge.character_primitive
      bridge.character_ne_one hinv hlo hhi (Finset.Ioc 0 ⌊L ^ 2⌋₊)
  have ha :=
    gamma_jacobi_no_negative_ramp_comparison bridge hx0 (fun p hp ho hcut ↦ hno p hp ho (he ▸ hcut))
  have hl :=
    finiteSigned_character_prefix_add_ambient_ramp_eq_local_cost
      Analysis.phaseResolvent64Coefficients bridge.character
      (mul_pos (by norm_num only : (0 : ℕ) < 4) hn.pos) hb
      (gamma_jacobi_no_negative_prefix_prime_one bridge hno) (L ^ 2 / (99 / 40))
  dsimp only [phase64JacobiLocalBudget]
  linarith only [hc, ha, hl]

/-- Under GRH and the first-cell conductor hypotheses, a strict numerical gap for
the actual signed local budget yields an odd-prime negative Jacobi witness through
`L^2`. Negating witness existence contradicts the preceding arithmetic comparison.
The numerical gap is an explicit remaining hypothesis, not a proved scalar bound. -/
theorem exists_odd_prime_negative_of_phase64_local_gap {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {L : ℝ} (hlo : 64 ≤ L)
    (hhi : L ≤ 64001 / 1000)
    (hgap :
      phase64JacobiLocalBudget bridge q (L ^ 2 / (99 / 40)) (L ^ 2) <
        2 *
            (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum (L ^ 2 / (99 / 40)) /
              Real.sqrt (L ^ 2 / (99 / 40))) -
          (∑' k : ℕ,
              PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1)
                (L ^ 2 / (99 / 40)) k).re) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ L ^ 2 ∧ jacobiSym n p = -1 := by
  apply Classical.byContradiction
  intro h
  have hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ L ^ 2 → jacobiSym n p ≠ -1 := fun p hp ho hb hj ↦
    h ⟨p, hp, ho, hb, hj⟩
  exact
    (not_lt_of_ge (phase64_jacobi_no_negative_local_comparison bridge hGRH hq hmq hlo hhi hno)) hgap

end PseudoPrime.LLS
