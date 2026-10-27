/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RiemannOneSidedLogCap
public import PseudoPrime.LLS.GammaSmallCheckpointBounds

/-! # Analytic Euler-prefix transport from cutoff 1000 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: a fixed Gamma node. Definition: consecutive trillionth-grid endpoints.
Output: a rational interval for 1000 to the negative node exponent.
Role: separate endpoint discovery from the subsequent kernel certificate. -/
def checkpoint1000Ratios (a : ℚ) : ℚ × ℚ :=
  let rs : List ℕ := [707945784, 354813389, 125892541, 31622776, 3981071, 251188, 3981, 7, 0, 0]
  let r := rs[(Analysis.gammaResolventCoefficients.map Prod.fst).idxOf a]?.getD 0
  ((r : ℚ) / 1000000000000, ((r + 1 : ℕ) : ℚ) / 1000000000000)

/-- Claim: all ten power intervals at cutoff 1000 pass the common ratio checker.
Proof: exact twentieth-power kernel arithmetic. Role: certify the numerical node input. -/
theorem checkpoint1000_node_check :
    Analysis.gammaFiniteEulerRatioCheck 1000 checkpoint1000Ratios = true := by decide +kernel

/-- Claim: the rational Euler weight, signed slope and main tail satisfy three caps.
Proof: signed endpoint selection and kernel rational arithmetic.
Role: retain both negative products in the analytic boundary estimate. -/
theorem checkpoint1000_scalar_checks :
    (435675 / 1000000000 : ℚ) ≤ Analysis.gammaFiniteEulerLower checkpoint1000Ratios ∧
      gammaFiniteWeightedUpper gammaSlopeRationalCoefficient checkpoint1000Ratios ≤
        (-470611 / 1000000000 : ℚ) ∧
      gammaFiniteWeightedUpper (gammaTailRationalCoefficient 1000) checkpoint1000Ratios ≤
        (8961672 / 1000000 : ℚ) := by
  decide +kernel

/-- Input: RH. Claim: the smoothed Mangoldt sum at 1000 is at least 984.
Proof: bound its refined one-sided error using sqrt(1000)<=32 and log(1000)<=10 log(2).
Role: bound the negative slope product without enumerating prime powers. -/
theorem checkpoint1000_smoothed_lower (hRH : RiemannHypothesis) :
    (984 : ℝ) ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 1000 := by
  have h := logWeightedMangoldtSum_ge_rational_refined hRH (by norm_num only : (1 : ℝ) < 1000)
  have hs : Real.sqrt (1000 : ℝ) ≤ 32 := (Real.sqrt_le_iff).mpr ⟨by norm_num only, by norm_num only⟩
  have hl :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 1000) (by norm_num only : (1000 : ℝ) ≤ 2 ^ 10)
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith only [h, hs, hl, Real.log_two_lt_d9]

/-- Input: RH. Claim: the smoothed sum at 800 is at most 800+3/2.
Proof: apply the one-sided square-root upper error and sqrt(800)<=30.
Role: supply the smaller endpoint for the asymmetric Chebyshev comparison. -/
theorem checkpoint1000_smoothed800_upper (hRH : RiemannHypothesis) :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 800 ≤ (800 + 3 / 2 : ℝ) := by
  have h := logWeightedMangoldtSum_le_add_sqrt_twentieth hRH (by norm_num only : (1 : ℝ) < 800)
  have hs : Real.sqrt (800 : ℝ) ≤ 30 := (Real.sqrt_le_iff).mpr ⟨by norm_num only, by norm_num only⟩
  linarith only [h, hs]

/-- Claim: log(1000/800)<=28/125. Proof: kernel-check a rational Taylor interval.
Role: avoid replacing the logarithm by the coarser relative interval length. -/
theorem checkpoint1000_log_ratio_upper : Real.log (1000 / 800 : ℝ) ≤ 28 / 125 := by
  have hc : Analysis.rationalLogIntervalCheck (5 / 4) 0 8 0 (28 / 125) = true := by decide +kernel
  have h := (Analysis.rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
  exact h

/-- Input: RH. Claim: psi(1000)>=810.
Proof: combine the one-sided smoothed bounds at 800 and 1000 with the checked log cap.
Role: retain the negative Chebyshev boundary contribution at the small checkpoint. -/
theorem checkpoint1000_psi_lower (hRH : RiemannHypothesis) : (810 : ℝ) ≤ Chebyshev.psi 1000 := by
  exact
    psi_lower_of_one_sided_log_cap (by norm_num only : (0 : ℝ) < 800)
      (by norm_num only : (800 : ℝ) < 1000) (checkpoint1000_smoothed800_upper hRH)
      (show (1000 : ℝ) - 16 ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 1000
        by
        norm_num only
        exact checkpoint1000_smoothed_lower hRH)
      (by norm_num only : (0 : ℝ) ≤ 810) checkpoint1000_log_ratio_upper (by norm_num only)

/-- Claim: the actual Euler weight at 1000 is at least 435675/10^9.
Proof: transfer the rational node lower bound to the real weight.
Role: supply the first nonnegative factor in the boundary comparison. -/
theorem checkpoint1000_weight_lower :
    (435675 / 1000000000 : ℝ) ≤ Analysis.gammaResolventEulerWeight 1000 := by
  have h := (Analysis.gamma_finite_ratio_check_euler_bounds checkpoint1000_node_check).1
  have hc := (Rat.cast_le (K := ℝ)).mpr checkpoint1000_scalar_checks.1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h hc
  linarith only [hc, h]

/-- Claim: the actual logarithmic Euler slope at 1000 is at most -470611/10^9.
Proof: use signed node bounds and the exact slope identity.
Role: supply the nonpositive coefficient of the smoothed-sum product. -/
theorem checkpoint1000_slope_upper : gammaEulerLogSlope 1000 ≤ (-470611 / 1000000000 : ℝ) := by
  have h := (gamma_finite_weighted_bounds checkpoint1000_node_check gammaSlopeRationalCoefficient).2
  have hc := (Rat.cast_le (K := ℝ)).mpr checkpoint1000_scalar_checks.2.1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] at h hc
  rw [← gamma_slope_eq_weighted] at h
  linarith only [h, hc]

/-- Claim: the integrated main tail at 1000 is at most 8961672/10^6.
Proof: transfer the signed rational comparison through the exact main-tail identity.
Role: complete the compact analytic boundary inputs. -/
theorem checkpoint1000_main_upper : gammaEulerTailMain 1000 ≤ (8961672 / 1000000 : ℝ) := by
  have h :=
    (gamma_finite_weighted_bounds checkpoint1000_node_check (gammaTailRationalCoefficient 1000)).2
  have hc := (Rat.cast_le (K := ℝ)).mpr checkpoint1000_scalar_checks.2.2
  rw [← gamma_tail_main_eq_weighted (by norm_num only : (0 : ℚ) < 1000)] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h hc
  linarith only [h, hc]

/-- Input: RH. Claim: the signed Euler boundary tail at 1000 is at most 163/20.
Proof: keep the negative psi and smoothed-sum products using the proved scalar inputs.
Role: certify a small checkpoint with ten node intervals and no prime-power payload. -/
theorem gamma_boundary1000_upper (hRH : RiemannHypothesis) :
    gammaEulerBoundaryTail 1000 ≤ (163 / 20 : ℝ) := by
  have h :=
    gamma_euler_boundary_tail_upper (by norm_num only : (0 : ℝ) ≤ 435675 / 1000000000)
      checkpoint1000_weight_lower (by norm_num only : (0 : ℝ) ≤ 810) (checkpoint1000_psi_lower hRH)
      checkpoint1000_slope_upper (by norm_num only) (by norm_num only : (0 : ℝ) ≤ 984)
      (checkpoint1000_smoothed_lower hRH) checkpoint1000_main_upper
  linarith only [h]

/-- Input: RH and any cutoff b>=1000. Claim: the full Euler prefix at b is at least 203/50.
Proof: transport the seed through the certified tail and use prefix monotonicity.
Role: eliminate the old 50000 checkpoint requirement from this weaker prefix estimate. -/
theorem gamma_prefix1000_lower_halfline (hRH : RiemannHypothesis) {b : ℝ} (hb : 1000 ≤ b) :
    (203 / 50 : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  have h :=
    gamma_prefix_lower_of_small_checkpoint (U := 163 / 20) hRH (by norm_num only : (100 : ℝ) ≤ 1000)
      hb
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]; exact gamma_boundary1000_upper hRH)
  norm_num only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat] at h
  exact h

/-- Input: RH, b>=1000 and an upper bound D for the signed dual budget.
Claim: the explicit prefix margin with constant 203/50 bounds actual separation below.
Proof: substitute the proved prefix in the generic algebraic comparison.
Role: connect the small checkpoint to witness and finite-maximum extraction. -/
theorem gamma_checkpoint1000_separation_le (hRH : RiemannHypothesis) {b L x D : ℝ} (hb : 1000 ≤ b)
    (hD : gammaScaleSignedDualBudget L x ≤ D) :
    gammaPrefixSeparation L x D (203 / 50) ≤ gammaFactorFreeSeparation L b x := by
  apply gamma_prefix_separation_le_of_prefix (C := 203 / 50) ?_ hD
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  exact gamma_prefix1000_lower_halfline hRH hb

end PseudoPrime.LLS
