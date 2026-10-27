/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaEulerSeed100
public import PseudoPrime.LLS.GammaEulerErrorEnvelopes
public import PseudoPrime.LLS.GammaEulerTailErrorCertificate
public import PseudoPrime.LLS.GammaEulerSeed100Bounds

/-! # Certified seed and half-line error constants for Euler-prefix transport -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Definition: ten millionth-grid node intervals at cutoff 100.
Output: compact rational power data. Role: verify the seed error without numerical oracles. -/
def errorSeed100Ratios : ℚ → ℚ × ℚ :=
  Analysis.smallSeedRatios [7943, 5011, 2511, 1000, 251, 39, 2, 0, 0, 0]

/-- Claim: all ten seed node intervals pass the twentieth-power check.
Proof: kernel arithmetic reduction. Role: justify the real node upper endpoints. -/
theorem error_seed100_ratio_check :
    Analysis.gammaFiniteEulerRatioCheck 100 errorSeed100Ratios = true := by decide +kernel

/-- Claim: the certified logarithm interval at 100 ends below 4606/1000.
Proof: kernel Taylor arithmetic. Role: supply the logarithm input to the generic envelope. -/
theorem error_seed100_log_check :
    Analysis.rationalLogIntervalCheck 100 7 20 4 (4606 / 1000) = true := by decide +kernel

/-- Definition: sum of absolute node coefficients times their rational error envelopes.
Output: a finite rational bound. Role: certify the actual error budget at cutoff 100. -/
def errorSeed100Budget : ℚ :=
  (Analysis.gammaResolventCoefficients.map
      (fun ab ↦
        let σ := (1 / 2 : ℚ) + ab.1
        let v := (errorSeed100Ratios ab.1).2
        |ab.2| *
          ((1 / 20 : ℚ) * (σ ^ 2 * (10 * v) / (σ - 1 / 2)) +
            (1839 / 1000 : ℚ) * (v * (1 + σ * (4606 / 1000))) +
            (21 / 20 : ℚ) * (σ * v)))).sum

/-- Claim: the finite rational seed error allowance is at most 3/40.
Proof: exact kernel arithmetic. Role: fix a reusable numerical error cap. -/
theorem error_seed100_budget_check : errorSeed100Budget ≤ 3 / 40 := by decide +kernel

/-- Claim: the actual finite Euler error budget at 100 is at most 3/40, independently of RH.
Proof: apply the generic envelope to the checked root, logarithm and power endpoints.
Role: remove the seed error assumption from prefix transport. -/
theorem gammaEulerTailErrorBudget_le_seed100 : gammaEulerTailErrorBudget 100 ≤ (3 / 40 : ℝ) := by
  have hr : Real.sqrt (100 : ℝ) ≤ 10 := by
    apply (Real.sqrt_le_left (by norm_num only : (0 : ℝ) ≤ 10)).mpr
    norm_num only
  have hl := (Analysis.rationalLogIntervalCheck_sound error_seed100_log_check).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
  have h :=
    gammaEulerTailErrorBudget_le_envelope (by norm_num only : (1 : ℝ) ≤ 100) hr hl
      (fun a ↦ ((errorSeed100Ratios a).2 : ℝ))
      (fun ab hab ↦ (Analysis.gamma_finite_ratio_check_sound error_seed100_ratio_check ab hab).2)
  have hc : gammaEulerTailErrorBudget 100 ≤ (errorSeed100Budget : ℝ) := by
    norm_num only [errorSeed100Budget, gammaEulerErrorEnvelope, Rat.cast_list_sum, List.map_map,
      Function.comp_def, Rat.cast_mul, Rat.cast_abs, Rat.cast_add, Rat.cast_div, Rat.cast_pow,
      Rat.cast_sub, Rat.cast_ofNat, Rat.cast_one] at h ⊢
    exact h
  have he := (Rat.cast_le (K := ℝ)).mpr error_seed100_budget_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at he
  exact hc.trans he

/-- Input: b>=50000. Claim: the two cutoff error budgets sum to at most 377/5000.
Proof: monotonicity and the existing cutoff-50000 certificate.
Role: control transport errors uniformly on the entire target half-line. -/
theorem gammaEulerTailErrorBudget_seed100_add_le {b : ℝ} (hb : 50000 ≤ b) :
    gammaEulerTailErrorBudget 100 + gammaEulerTailErrorBudget b ≤ (377 / 5000 : ℝ) := by
  have hm := gammaEulerTailErrorBudget_antitone_of_three_le (by norm_num only : (3 : ℝ) ≤ 50000) hb
  have he := gamma_tail_error_budget_le
  linarith only [gammaEulerTailErrorBudget_le_seed100, hm, he]

/-- Input: RH, b>=50000 and signed boundary-tail bounds A,B.
Claim: 317/100+A-B-377/5000 bounds the target prefix below.
Proof: substitute the uniform error cap into the certified seed transport.
Role: retain only boundary obligations in the analytic prefix lower bound. -/
theorem gamma_euler_prefix_lower_from_seed100_error (hRH : RiemannHypothesis) {b A B : ℝ}
    (hb : 50000 ≤ b) (hA : A ≤ gammaEulerBoundaryTail 100) (hB : gammaEulerBoundaryTail b ≤ B) :
    (317 / 100 : ℝ) + A - B - 377 / 5000 ≤
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  exact
    gamma_euler_prefix_lower_from_seed100 hRH (by linarith only [hb]) hA hB
      (gammaEulerTailErrorBudget_seed100_add_le hb)

/-- Input: RH, odd nonsquare n, log n<=L, x>=4096, b>=50000 and boundary/dual caps.
Claim: the actual Jacobi joint budget has the displayed bound with a proved error constant.
Proof: instantiate the seed comparison with the uniform error cap.
Role: eliminate the error-budget field from the witness comparison. -/
theorem gamma_joint_prefix_le_from_seed100_error (hRH : RiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) {b A B L x D : ℝ} (hb : 50000 ≤ b) (hlog : Real.log n ≤ L) (hx : 4096 ≤ x)
    (hA : A ≤ gammaEulerBoundaryTail 100) (hB : gammaEulerBoundaryTail b ≤ B)
    (hD : gammaScaleSignedDualBudget L x ≤ D) :
    gammaJointPrefixLocalBudget (NumberTheory.complexQuadraticCharacter n hn) b x ≤
      (11783423 / 25000000 : ℝ) * (L + 7 / 5) + 3 / 4 + D - 2 * (317 / 100 + A - B - 377 / 5000) +
        7 / 60 := by
  exact
    gamma_joint_prefix_le_from_seed100 hRH hn hns (by linarith only [hb]) hlog hx hA hB
      (gammaEulerTailErrorBudget_seed100_add_le hb) hD

end PseudoPrime.LLS
