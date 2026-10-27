/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.Phase64Ramified1700Bounds
public import PseudoPrime.LLS.Phase64TransportedNumericalBudget

/-! # Existing Jacobi numerical budgets on scales through 1700 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: 1600 <= x <= 1700. Claim: the finite budget is below the same
scalar budget as before. Insert the certified 13/5 cap. Role: enlarge the scale
range without changing any global Euler or principal-sum certificate. -/
theorem phase64_finite_budget_le_scalar_1700 (n q : ℕ) {x : ℝ} (hlo : 1600 ≤ x) (hhi : x ≤ 1700)
    (b : ℝ) : phase64FiniteJacobiBudget n q x b ≤ phase64ScalarJacobiBudget n q x b := by
  have he := Analysis.phase64_ramified_excess_le_thirteen_fifths_1700 hlo hhi
  dsimp only [phase64FiniteJacobiBudget, phase64ScalarJacobiBudget]
  linarith only [he]

/-- Input: actual Jacobi data, RH, scale from 1600 to 1700 and prefix at least
500. Claim: the explicit numerical budget bounds the local budget. Compose the
conductor, ramified, Gamma and existing Euler bounds. Role: remove local numeric
hypotheses for the enlarged scale interval. -/
theorem phase64_local_budget_le_numerical_1700 {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (hRH : RiemannHypothesis) (q : ℕ)
    {x b : ℝ} (hlo : 1600 ≤ x) (hhi : x ≤ 1700) (hb : 500 ≤ b) :
    phase64JacobiLocalBudget bridge q x b ≤ phase64NumericalJacobiBudget n q x := by
  have h1 := phase64_jacobi_local_budget_le_ramified bridge q hlo b
  have h2 :=
    phase64_ramified_budget_le_finite bridge q hlo
      (hhi.trans (by norm_num only : (1700 : ℝ) ≤ 1700)) b
  have h3 := phase64_finite_budget_le_scalar_1700 n q hlo hhi b
  have h4 := phase64_scalar_budget_le_euler n q x b
  have h5 := phase64_euler_budget_le_total n q x hb
  have h6 := phase64_total_budget_le_numerical hRH n q x
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))

/-- For the same scale and prefix, nonnegative delta and conductor at most
q, the transported exact local budget is at most the explicit numerical budget.
Keep the old local budget and bound only the added conductor-logarithm cost. -/
theorem logarithmic_phase64_budget_le_numerical_1700 {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (hRH : RiemannHypothesis) {q : ℕ}
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {x b : ℝ} (hlo : 1600 ≤ x)
    (hhi : x ≤ 1700) (hb : 500 ≤ b) {δ : ℚ} (hd : 0 ≤ δ) :
    logarithmicPhaseJacobiLocalBudget bridge q x b Analysis.phaseResolvent64Coefficients δ ≤
      phase64TransportedNumericalBudget n q x δ := by
  have hc := phase64_local_budget_le_numerical_1700 bridge hRH q hlo hhi hb
  have hm0 : (0 : ℝ) < (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    Nat.cast_pos.mpr
      ((by norm_num only : (0 : ℕ) < 3).trans_le (gamma_jacobi_modulus_ge_three bridge))
  have hm := Real.log_le_log hm0 (Nat.cast_le.mpr hmq)
  have hmδ := mul_le_mul_of_nonneg_left hm ((Rat.cast_nonneg (K := ℝ)).mpr hd)
  have he :
    logarithmicPhaseJacobiLocalBudget bridge q x b Analysis.phaseResolvent64Coefficients δ =
      phase64JacobiLocalBudget bridge q x b +
        (δ : ℝ) * (Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor + 76 / 5) := by
    dsimp only [logarithmicPhaseJacobiLocalBudget, phase64JacobiLocalBudget]; ring
  rw [he]
  dsimp only [phase64TransportedNumericalBudget]
  nlinarith only [hc, hmδ]

/-- Under GRH and an anchor in the certified first level cell, a log-distance
cap and a strict transported numerical gap give an odd-prime negative Jacobi witness
through 99*x/40 at the new scale. All original local and Euler numerical caps are proved;
selecting a wider target interval still requires proving the displayed scalar gap. -/
theorem exists_odd_prime_negative_of_transported_phase64_numerical_gap_1700 {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {x b L : ℝ} (hlo : 1600 ≤ x)
    (hhi : x ≤ 1700) (hb : 500 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x) (hLlo : 64 ≤ L)
    (hLhi : L ≤ 64001 / 1000) (δ : ℚ) (hd : |Real.log x - Real.log (L ^ 2 / (99 / 40))| ≤ (δ : ℝ))
    (hgap :
      phase64TransportedNumericalBudget n q x δ <
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p = -1 := by
  have hd0 : 0 ≤ δ :=
    (Rat.cast_nonneg (K := ℝ)).mp
      ((abs_nonneg (Real.log x - Real.log (L ^ 2 / (99 / 40)))).trans hd)
  have hc := logarithmic_phase64_budget_le_numerical_1700 bridge hGRH.riemann hmq hlo hhi hb hd0
  exact
    exists_odd_prime_negative_of_transported_phase64_gap bridge hGRH hq hmq
      ((by norm_num only : (2 : ℝ) ≤ 1600).trans hlo) ((by norm_num only : (1 : ℝ) ≤ 500).trans hb)
      hbx hLlo hLhi δ hd (hc.trans_lt hgap)

end PseudoPrime.LLS
