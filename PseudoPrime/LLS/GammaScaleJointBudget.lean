/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaScaleConductorBudget
public import PseudoPrime.LLS.GammaIntegerPrefixConductorBounds
public import PseudoPrime.LLS.GammaJointPrefixComparison
public import PseudoPrime.LLS.GammaNonOneRefinedNumerics
public import PseudoPrime.LLS.GammaSmallScaleLocalBridge

/-! # Factor-independent joint Gamma budgets at arbitrary scales -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: actual Jacobi arithmetic data, any square-prime subset and prefixes, and x >= 20000.
Claim: conductor, square and dyadic costs fit mu log(4n)+3/4 at that scale.
Proof: transfer the bridge decomposition and conductor branch to scale-wise absorption.
Role: remove the old prescribed logarithmic profile from the arithmetic bridge. -/
theorem gamma_jacobi_square_dyadic_cost_le_of_scale {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (hχ : ∀ p ∈ S, bridge.character p = -1) (K : ℕ → Finset ℕ)
    (K2 : Finset ℕ) {x : ℝ} (hx : 20000 ≤ x) :
    (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        (∑ p ∈ S, Analysis.gammaActualPrimeLocalCost bridge.character p (K p) x) +
        Analysis.gammaActualPrimeLocalCost bridge.character 2 K2 x ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + 3 / 4 := by
  have hf : 0 < (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    (gamma_jacobi_modulus_eq_discriminant bridge).symm ▸ bridge.discriminant_pos
  have hd := gamma_jacobi_modulus_squarefree_data bridge
  exact
    Analysis.gamma_actual_square_dyadic_cost_le_of_scale
      (by simpa only [Nat.mul_comm] using bridge.squarefreePart_sq_mul.symm) hn
      bridge.squarefreePart_pos bridge.squareFactor_odd.pos hf hd.1 hd.2 bridge.character
      (gamma_jacobi_actual_dyadic_branch bridge) S hS hχ K K2 hx

/-- Input: a real logarithmic allowance L and scale x.
Definition: the variable dual price times L plus its finite signed odd-prime excess.
Output: a scalar local budget independent of the input prime factors.
Role: retain the actual signed ramp terms in arbitrary-scale numerical comparisons. -/
noncomputable def gammaScaleSignedDualBudget (L x : ℝ) : ℝ :=
  Analysis.gammaRamifiedDualParameter x * L +
    ∑ p ∈ Analysis.gammaRamifiedDualPrimeSet x,
      Real.log p *
        max (Analysis.gammaRamifiedSignedCombinedCost p x - Analysis.gammaRamifiedDualParameter x) 0

/-- Input: actual Jacobi arithmetic data, arbitrary positive-power prefixes and x >= 20000.
Claim: all ambient local costs fit the conductor allowance and finite scale dual budget.
Proof: classify the same input primes by values -1,0,1 and combine signed costs once.
Role: replace the old n >= 10^100 input gate by a gate on the actual analytic scale. -/
theorem gamma_jacobi_all_local_cost_le_scale_dual {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (K : ℕ → Finset ℕ)
    (K2 : Finset ℕ) {x : ℝ} (hx : 20000 ≤ x) :
    (11783423 / 25000000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor +
        (∑ p ∈ n.primeFactors, Analysis.gammaActualPrimeLocalCost bridge.character p (K p) x) +
        Analysis.gammaActualPrimeLocalCost bridge.character 2 K2 x ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + 3 / 4 +
        gammaScaleSignedDualBudget (Real.log n) x := by
  let S := n.primeFactors.filter (fun p : ℕ ↦ bridge.character p = -1)
  let R := n.primeFactors.filter (fun p : ℕ ↦ bridge.character p = 0)
  have hs :=
    gamma_jacobi_square_dyadic_cost_le_of_scale bridge S (Finset.filter_subset _ _)
      (fun p hp ↦ (Finset.mem_filter.mp hp).2) K K2 hx
  have hr :=
    Analysis.gamma_actual_odd_ramified_signed_cost_le_finite_dual hn R (Finset.filter_subset _ _)
      bridge.character (fun p hp ↦ (Finset.mem_filter.mp hp).2) K
      (show (1 : ℝ) ≤ x by linarith only [hx])
  have hc :=
    gamma_actual_quadratic_local_sum_le_classified hn bridge.character bridge.character_quadratic K
      (show (0 : ℝ) < x by linarith only [hx])
  change
    (∑ p ∈ n.primeFactors, Analysis.gammaActualPrimeLocalCost bridge.character p (K p) x) ≤
      (∑ p ∈ S, Analysis.gammaActualPrimeLocalCost bridge.character p (K p) x) +
        ∑ p ∈ R, Analysis.gammaActualPrimeLocalCost bridge.character p (K p) x at hc
  dsimp only [gammaScaleSignedDualBudget]
  linarith only [hs, hr, hc]

/-- Input: logarithmic allowance L, integer-prefix endpoint b and scale x.
Definition: the ambient conductor allowance, signed finite dual and negative twice-prefix gain.
Output: a joint upper budget with no input character or factorization argument.
Role: expose a purely scalar target for uniform negative-witness estimates. -/
noncomputable def gammaFactorFreeJointBudget (L b x : ℝ) : ℝ :=
  (11783423 / 25000000 : ℝ) * (L + 7 / 5) + 3 / 4 + gammaScaleSignedDualBudget L x -
    2 * (∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)

/-- Input: odd nonsquare n, log n <= L and x >= 20000; b is arbitrary.
Claim: the actual original-character joint budget is below the factor-independent budget.
Proof: use the canonical arithmetic bridge, split off two and enlarge logarithmic terms.
Role: remove conductor and factorization data from the sufficient scalar separation. -/
theorem gamma_joint_prefix_le_factor_free_budget {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    {L b x : ℝ} (hlog : Real.log n ≤ L) (hx : 20000 ≤ x) :
    gammaJointPrefixLocalBudget (NumberTheory.complexQuadraticCharacter n hn) b x ≤
      gammaFactorFreeJointBudget L b x := by
  obtain ⟨bridge⟩ := NumberTheory.exists_jacobiCharacterArithmeticData hn.pos hn hns
  let K := AnalyticNumberTheory.DirichletLFunction.gammaPrefixPowerIndices b
  have hl := gamma_jacobi_all_local_cost_le_scale_dual bridge K (K 2) hx
  have he : bridge.character = (NumberTheory.complexQuadraticCharacter n hn).primitiveCharacter :=
    bridge.character_eq
  have hm := mul_le_mul_of_nonneg_left hlog (Analysis.gamma_ramified_dual_parameter_nonneg x)
  have hlog4 : Real.log (4 * (n : ℝ)) ≤ L + 7 / 5 := by
    rw [Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) (Nat.cast_pos.mpr hn.pos).ne']
    linarith only [hlog, Analysis.log_four_le_seven_fifths]
  have hlead := mul_le_mul_of_nonneg_left hlog4 (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
  rw [gammaJointPrefixLocalBudget, ← he, gamma_ambient_four_factor_sum_eq hn]
  dsimp only [gammaFactorFreeJointBudget, gammaScaleSignedDualBudget] at ⊢ hl
  linarith only [hl, hm, hlead]

/-- Input: L, prefix b and scale x.
Definition: twice the paired ramp lower bound minus principal and factor-independent upper costs.
Output: a sufficient scalar margin containing only real parameters and finite prime sums.
Role: state a witness criterion independent of the unknown input factorization. -/
noncomputable def gammaFactorFreeSeparation (L b x : ℝ) : ℝ :=
  2 *
      ((∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) * Real.sqrt x -
        gammaRampPairedErrorNumerator x / Real.sqrt x) -
    (Real.sqrt x +
      (Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / Real.sqrt x) -
    (gammaFactorFreeJointBudget L b x + 11 + ((7 / 6 : ℝ) * (L + 7 / 5) + 4) / Real.sqrt x +
      43 * x ^ (-9 / 16 : ℝ))

/-- Input: odd nonsquare n, log n <= L, x >= 20000 and log Q <= L+7/5.
Claim: the factor-independent margin is at most the actual even-character joint margin.
Proof: compare the joint budget and the pole allowance before subtracting them.
Role: turn a scalar numerical certificate into the existing analytic separation. -/
theorem gamma_factor_free_separation_le_joint {n Q : ℕ} (hn : Odd n) (hns : ¬IsSquare n) {L b x : ℝ}
    (hlog : Real.log n ≤ L) (hx : 20000 ≤ x) (hlogQ : Real.log Q ≤ L + 7 / 5) :
    gammaFactorFreeSeparation L b x ≤
      gammaJointPrefixSeparation Q (NumberTheory.complexQuadraticCharacter n hn) b x (-3 / 2) := by
  have hJ := gamma_joint_prefix_le_factor_free_budget (b := b) hn hns hlog hx
  have hN :
    ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x ≤ ((7 / 6 : ℝ) * (L + 7 / 5) + 4) / Real.sqrt x :=
    div_le_div_of_nonneg_right (by linarith only [hlogQ]) (Real.sqrt_nonneg x)
  dsimp only [gammaFactorFreeSeparation, gammaJointPrefixSeparation]
  linarith only [hJ, hN]

/-- Input: odd n, L >= 10 and log n <= L.
Claim: log(max(20000,4n)) is at most L+7/5.
Proof: handle the actual level or the fixed auxiliary level using explicit logarithm bounds.
Role: remove a separate ambient-level condition from witness extraction. -/
theorem gamma_log_pole_level_le_of_common_endpoint {n : ℕ} (hn : Odd n) {L : ℝ} (hL : 10 ≤ L)
    (hlog : Real.log n ≤ L) : Real.log (max 20000 (4 * n) : ℕ) ≤ L + 7 / 5 := by
  by_cases hq : 20000 ≤ 4 * n
  · rw [max_eq_right hq, Nat.cast_mul, Nat.cast_ofNat,
      Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) (Nat.cast_pos.mpr hn.pos).ne']
    linarith only [hlog, Analysis.log_four_le_seven_fifths]
  · rw [max_eq_left (le_of_not_ge hq)]
    have hl :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 20000) (by norm_num only : (20000 : ℝ) ≤ 46000)
    linarith only [hl, Analysis.log_46000_lt_eleven, hL]

/-- Input: odd nonsquare n, log n <= L and arbitrary scale x >= 4096.
Claim: the actual joint budget is below the scalar budget plus 7/60.
Proof: use the existing 13/15 small-scale allowance and enlarge the logarithmic terms.
Role: extend factor-independent comparison below the sharper scale-20000 gate. -/
theorem gamma_joint_prefix_le_factor_free_budget_small_scale {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) {L b x : ℝ} (hlog : Real.log n ≤ L) (hx : 4096 ≤ x) :
    gammaJointPrefixLocalBudget (NumberTheory.complexQuadraticCharacter n hn) b x ≤
      gammaFactorFreeJointBudget L b x + 7 / 60 := by
  obtain ⟨bridge⟩ := NumberTheory.exists_jacobiCharacterArithmeticData hn.pos hn hns
  let K := AnalyticNumberTheory.DirichletLFunction.gammaPrefixPowerIndices b
  have hl := gamma_jacobi_all_local_small_scale bridge K hx
  have he : bridge.character = (NumberTheory.complexQuadraticCharacter n hn).primitiveCharacter :=
    bridge.character_eq
  have hm := mul_le_mul_of_nonneg_left hlog (Analysis.gamma_ramified_dual_parameter_nonneg x)
  have hlog4 : Real.log (4 * (n : ℝ)) ≤ L + 7 / 5 := by
    rw [Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) (Nat.cast_pos.mpr hn.pos).ne']
    linarith only [hlog, Analysis.log_four_le_seven_fifths]
  have hlead := mul_le_mul_of_nonneg_left hlog4 (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
  rw [gammaJointPrefixLocalBudget, ← he]
  dsimp only [gammaFactorFreeJointBudget, gammaScaleSignedDualBudget]
  linarith only [hl, hm, hlead]

/-- Input: the small-scale data and log Q <= L+7/5.
Claim: the scalar margin is at most the actual even-character margin plus 7/60.
Proof: compare the local and pole budgets with their signs retained.
Role: convert a scalar margin of at least 7/60 into actual witness separation. -/
theorem gamma_factor_free_separation_le_joint_add_small_scale {n Q : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) {L b x : ℝ} (hlog : Real.log n ≤ L) (hx : 4096 ≤ x)
    (hlogQ : Real.log Q ≤ L + 7 / 5) :
    gammaFactorFreeSeparation L b x ≤
      gammaJointPrefixSeparation Q (NumberTheory.complexQuadraticCharacter n hn) b x (-3 / 2) +
        7 / 60 := by
  have hJ := gamma_joint_prefix_le_factor_free_budget_small_scale (b := b) hn hns hlog hx
  have hN :
    ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x ≤ ((7 / 6 : ℝ) * (L + 7 / 5) + 4) / Real.sqrt x :=
    div_le_div_of_nonneg_right (by linarith only [hlogQ]) (Real.sqrt_nonneg x)
  dsimp only [gammaFactorFreeSeparation, gammaJointPrefixSeparation]
  linarith only [hJ, hN]

end PseudoPrime.LLS
