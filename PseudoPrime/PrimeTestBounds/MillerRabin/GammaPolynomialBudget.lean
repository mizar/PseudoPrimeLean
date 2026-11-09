/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ExponentialRampSummation
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaSignedPrefixBounds
public import PseudoPrime.LLS.GammaRetainedCommonCostBounds
public import PseudoPrime.LLS.GammaSignedVariationPrincipalBounds
public import PseudoPrime.LLS.GammaPairedPolynomialSeparation

/-! # Gamma budget bounds for arbitrary scales and prefixes -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, the exact common Euler and even Gamma cost gives fixed allowance
541/50, retaining any finite prefix. Role: supply a sharper MR scalar budget
without changing the contour or subgroup comparison. -/
theorem gammaSignedPrefixMRBudget_lt_precise_common_cost (hRH : RiemannHypothesis) (n Q : ℕ)
    (x b : ℝ) :
    gammaSignedPrefixMRBudget n Q x b <
      (11783423 / 25000000 : ℝ) * Real.log n + 541 / 50 -
          2 * (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  have h :=
    LLS.gamma_even_common_cost_lt_precise hRH
      AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even
  have hf : (1 : DirichletCharacter ℂ 1).gammaFactor = Complex.Gammaℝ :=
    funext AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even.gammaFactor_def
  rw [hf] at h
  dsimp only [gammaSignedPrefixMRBudget]
  linarith only [h]

/-- Input: RH, log(n) <= L, scale x >= 1, any prefix lower bound C and
positive scalar polynomial data. Claim: the exact MR budget is below the
actual ramp-principal gap. Use the common Gamma cost and signed principal
upper bound. Role: connect arbitrary polynomial bounds to MR witnesses. -/
theorem gamma_budget_gap_of_polynomial (hRH : RiemannHypothesis) {n : ℕ} {L x b C R u : ℝ}
    (hlogn : Real.log n ≤ L) (hx : 1 ≤ x)
    (hprefix : C ≤ ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)
    (hroot : Real.sqrt x ≤ R) (hlog : Real.log ((101 / 40 : ℝ) * x) ≤ u)
    (hcoef : 0 ≤ (11783423 / 25000000 : ℝ) * L + 541 / 50 - 2 * C + 328051 / 197600)
    (hpoly :
      0 <
        ((83125234337 / 100000000000 : ℝ) - 231 / 24700) * x -
          ((11783423 / 25000000 : ℝ) * L + 541 / 50 - 2 * C + 328051 / 197600) * R -
          (38017647 / 988000 : ℝ) * u -
          (7 / 6 : ℝ) * L -
          14082763 / 197600) :
    gammaSignedPrefixMRBudget n n x b <
      2 * (LLS.exponentialRampMangoldtSum x / Real.sqrt x) -
        (∑' k : ℕ,
            LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re := by
  have hs := Real.sqrt_pos.mpr (zero_lt_one.trans_le hx)
  have hu := gammaSignedPrefixMRBudget_lt_precise_common_cost hRH n n x b
  have hpole :=
    div_le_div_of_nonneg_right
      (show (7 / 6 : ℝ) * Real.log n + 4 ≤ (7 / 6 : ℝ) * L + 4 by linarith only [hlogn]) hs.le
  have hcost := LLS.gamma_paired_scalar_lt_gap hx hroot hlog hcoef hpoly
  have hP := LLS.gamma_level_one_sum_upper_signed_variation hRH hx
  have hT := LLS.gamma_ramp_sum_lower_paired hRH hx
  dsimp only [LLS.gammaSignedVariationPrincipalCap] at hcost
  nlinarith only [hu, hprefix, hlogn, hpole, hcost, hP, hT]

/-- Input: RH, arbitrary levels, scale x and prefix endpoint b.
Claim: the signed MR prefix budget is below mu log n + 11 minus twice its prefix and contour costs.
Proof: combine the certified even Gamma gain and principal Euler mass below 25/2.
Role: preserve prefix gain with an explicit constant for future finite-scale comparisons. -/
theorem gammaSignedPrefixMRBudget_lt_principal_even (hRH : RiemannHypothesis) (n Q : ℕ) (x b : ℝ) :
    gammaSignedPrefixMRBudget n Q x b <
      (11783423 / 25000000 : ℝ) * Real.log n + 11 -
          2 * (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  have hg :=
    AnalyticNumberTheory.DirichletLFunction.gammaResolvent_gammaFactor_0_le
      AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even
  have hf : (1 : DirichletCharacter ℂ 1).gammaFactor = Complex.Gammaℝ :=
    funext AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even.gammaFactor_def
  rw [hf] at hg
  have he := AnalyticNumberTheory.DirichletLFunction.gammaResolvent_euler_lt_twelve_half hRH
  dsimp only [gammaSignedPrefixMRBudget, LLS.PaperStatements.gammaSignedGammaCost]
  linarith only [hg, he]

end PseudoPrime.PrimeTestBounds.MillerRabin
