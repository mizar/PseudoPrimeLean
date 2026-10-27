/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ParameterizedConductorPrefixBounds

/-! # Negative prime witnesses with conductor-cancelled Euler prefix costs -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For a character of nonzero level and Y at least one, the paired Euler exclusion budget
on the full prefix is at most its principal mass plus (3/10) times the conductor-quotient
logarithm and (1/5) log 2. Apply the prime-weight bound to the alternating budget. This is the
explicit cost needed to preserve a uniform saving in the negative-witness comparison. -/
theorem pairedEulerExcludedBudget_le_prefix_conductor {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {Y : ℝ} (hY : 1 ≤ Y) :
    AnalyticNumberTheory.Arithmetic.quadraticExcludedBudget χ.conductor q (Finset.Ioc 0 ⌊Y⌋₊)
        (AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4)) ≤
      twoPoleEulerPrefixMass (Finset.Ioc 0 ⌊Y⌋₊) + (3 / 10 : ℝ) * Real.log (q / χ.conductor : ℕ) +
        (1 / 5 : ℝ) * Real.log 2 := by
  exact
    quadraticExcludedBudget_le_prefix_add_conductor_budget χ hY _
      (AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight_nonneg _ _ (by norm_num only))
      (fun n hn ↦
        AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight_eq_zero_of_mangoldt_eq_zero _ _ _
          (ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn))
      (fun p hp ↦ AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight_prime_pow_antitone hp)
      (by norm_num only) (mul_nonneg (by norm_num only) (Real.log_natCast_nonneg 2))
      (fun p hp ↦
        AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight_prime_upper_three_tenths hp)

/-- For a nonprincipal quadratic character under GRH and x at least 25, unit-prime triviality
below 99x/40 gives the arithmetic upper bound minus the full principal prefix, with only
(1/5) log 2 and the level-prime ramp cost remaining. Allocate one fifth of the conductor saving
to the local correction and three tenths to the excluded prefix. Their quotient costs cancel
exactly. This retains a negative-witness saving without a separate exclusion-budget hypothesis. -/
theorem gamma_primitive_add_local_le_of_conductor_prefix {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C Y : ℝ} (hx : 25 ≤ x)
    (hY : 1 ≤ Y) (hYcut : ∀ n ∈ Finset.Ioc 0 ⌊Y⌋₊, (n : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (ht : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) :
    (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand χ.primitiveCharacter x n).re +
        gammaQuadraticLocalCorrection χ x ≤
      twoPoleConstantUpper A C x - twoPoleEulerPrefixMass (Finset.Ioc 0 ⌊Y⌋₊) +
        (1 / 5 : ℝ) * Real.log 2 +
        (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x := by
  have hx0 : 0 < x := by linarith only [hx]
  have hs : 5 ≤ Real.sqrt x := by nlinarith only [Real.sq_sqrt hx0.le, Real.sqrt_nonneg x, hx]
  exact
    gamma_primitive_add_local_le_of_parameterized_conductor_prefix χ hquad hne hqA hGRH
      (by linarith only [hx] : 2 ≤ x) hY (a := 3 / 10) (d := (1 / 5 : ℝ) * Real.log 2)
      (by norm_num only) (mul_nonneg (by norm_num only) (Real.log_natCast_nonneg 2))
      (by linarith only [hs])
      (fun p hp ↦
        AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight_prime_upper_three_tenths hp)
      hYcut hC ht

/-- For a nonprincipal quadratic character under GRH, x at least 25, and a full Euler prefix
below the cutoff, a saving g no larger than the prefix mass minus (1/5) log 2 yields a negative
unit-prime witness whenever the saved gap exceeds the level-prime ramp cost. Combine the
conductor-sensitive arithmetic upper bound with the principal ramp comparison, then use
quadraticity to turn a non-one unit value into minus one. This is the consumer-facing extraction
criterion; no input-dependent exclusion budget remains among its hypotheses. -/
theorem exists_prime_neg_one_of_conductor_prefix {q A : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C Y g : ℝ} (hx : 25 ≤ x)
    (hY : 1 ≤ Y) (hYcut : ∀ n ∈ Finset.Ioc 0 ⌊Y⌋₊, (n : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (hg : g ≤ twoPoleEulerPrefixMass (Finset.Ioc 0 ⌊Y⌋₊) - (1 / 5 : ℝ) * Real.log 2)
    (hgap :
      (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x <
        twoPoleConstantGap A (C - g) x) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p = -1 := by
  have hx0 : 0 < x := by linarith only [hx]
  have hs : 5 ≤ Real.sqrt x := by nlinarith only [Real.sq_sqrt hx0.le, Real.sqrt_nonneg x, hx]
  exact
    exists_prime_neg_one_of_parameterized_conductor_prefix χ hquad hne hqA hGRH
      (by linarith only [hx] : 2 ≤ x) hY (a := 3 / 10) (d := (1 / 5 : ℝ) * Real.log 2)
      (by norm_num only) (mul_nonneg (by norm_num only) (Real.log_natCast_nonneg 2))
      (by linarith only [hs])
      (fun p hp ↦
        AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight_prime_upper_three_tenths hp)
      hYcut hC hg hgap

end PseudoPrime.LLS
