/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.Phase64FirstCellMajorant
public import PseudoPrime.LLS.GammaPhase64CompactBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.FiniteSignedPrefixTriviality
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.FiniteSignedParityBudget

/-! # Certified Gamma arithmetic bound on the first continuous scale cell -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Input: GRH, a primitive nonprincipal character of conductor `3 ≤ m ≤ q`,
`q ≥ 20000`, and a level parameter `64 ≤ L ≤ 64.001`.
Claim: the actual Gamma sum at `x = L^2/(99/40)` obeys the certified prefix budget.
Proof: use the complete adaptive phase certificate and the compact arithmetic transfer.
Role: remove the spectral comparison premise on this cell; prefix costs remain explicit. -/
theorem gamma_primitive_sum_re_le_phase64_first_cell {q m : ℕ} [NeZero m] (hq : 20000 ≤ q)
    (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {L : ℝ} (hlo : (64 : ℝ) ≤ L) (hhi : L ≤ 64001 / 1000)
    (B : Finset ℕ) :
    (∑' k : ℕ, gammaMellinKernel.summand χ (L ^ 2 / (99 / 40)) k).re ≤
      AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget χ
          Analysis.phaseResolvent64Coefficients B +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt (L ^ 2 / (99 / 40)) +
        43 * (L ^ 2 / (99 / 40)) ^ (-9 / 16 : ℝ) := by
  have hx : (2 : ℝ) ≤ L ^ 2 / (99 / 40) :=
    le_trans (by norm_num only : (2 : ℝ) ≤ 163840 / 99) (Analysis.scale64_cell_of_level hlo hhi).1
  exact
    gamma_primitive_sum_re_le_phase64_of_compact hq hm hmq hGRH hp hne hinv hx B
      (fun t _ ↦ Analysis.phaseCell64_full_phase_of_level hlo hhi t)

/-- Input: the first-cell primitive-character hypotheses and prime triviality through `b`.
The finite set `B` contains only indices at most `b`.
Claim: the Gamma arithmetic bound retains twice the exact prime-power prefix savings,
with no character-defect term. Proof: cancel the generic finite defect in the certified bound.
Role: leave only explicit gamma-factor and Euler budgets for the witness contradiction. -/
theorem gamma_primitive_sum_re_le_phase64_first_cell_prime_prefix {q m : ℕ} [NeZero m]
    (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {L : ℝ} (hlo : (64 : ℝ) ≤ L) (hhi : L ≤ 64001 / 1000)
    (B : Finset ℕ) {b : ℝ} (hB : ∀ k ∈ B, (k : ℝ) ≤ b)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → χ p = 1) :
    (∑' k : ℕ, gammaMellinKernel.summand χ (L ^ 2 / (99 / 40)) k).re ≤
      (Analysis.phaseResolvent64Coefficients.map (fun ab ↦ (ab.2 : ℝ))).sum * (Real.log m / 2) +
            (Analysis.phaseResolvent64Coefficients.map
                (fun ab ↦
                  (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
            (∑' k : ℕ,
              Analysis.finiteSignedMangoldtWeight Analysis.phaseResolvent64Coefficients k) -
          2 *
            (∑ k ∈ B, Analysis.finiteSignedMangoldtWeight Analysis.phaseResolvent64Coefficients k) +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt (L ^ 2 / (99 / 40)) +
        43 * (L ^ 2 / (99 / 40)) ^ (-9 / 16 : ℝ) := by
  have h := gamma_primitive_sum_re_le_phase64_first_cell hq hm hmq hGRH hp hne hinv hlo hhi B
  have he :=
    AnalyticNumberTheory.DirichletLFunction.finiteSigned_prefix_defect_eq_zero_of_prime_one χ
      Analysis.phaseResolvent64Coefficients B hB hsmall
  simpa only [AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget, he, add_zero] using
    h

/-- Input: the first-cell primitive-character hypotheses and prime triviality through `b`.
Claim: the actual Gamma sum is bounded by a character-independent signed parity budget
and the proved remainder. Proof: combine the first-cell bound with exact defect cancellation.
Role: reduce the remaining witness comparison to explicit scalar Gamma and Euler costs. -/
theorem gamma_primitive_sum_re_le_phase64_first_cell_parity_prefix {q m : ℕ} [NeZero m]
    (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {L : ℝ} (hlo : (64 : ℝ) ≤ L) (hhi : L ≤ 64001 / 1000)
    (B : Finset ℕ) {b : ℝ} (hB : ∀ k ∈ B, (k : ℝ) ≤ b)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → χ p = 1) :
    (∑' k : ℕ, gammaMellinKernel.summand χ (L ^ 2 / (99 / 40)) k).re ≤
      AnalyticNumberTheory.DirichletLFunction.finiteSignedTrivialPrefixBudget m
          Analysis.phaseResolvent64Coefficients B +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt (L ^ 2 / (99 / 40)) +
        43 * (L ^ 2 / (99 / 40)) ^ (-9 / 16 : ℝ) := by
  have h := gamma_primitive_sum_re_le_phase64_first_cell hq hm hmq hGRH hp hne hinv hlo hhi B
  have hb :=
    AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget_le_of_prime_one χ
      Analysis.phaseResolvent64Coefficients B hB hsmall
  linarith only [h, hb]

end PseudoPrime.LLS.PaperStatements
