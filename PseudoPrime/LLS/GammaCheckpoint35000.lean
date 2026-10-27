/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RiemannOneSidedLogCap
public import PseudoPrime.LLS.GammaSmallCheckpointBounds

/-! # Analytic Euler-prefix transport from cutoff 35000 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: a fixed Gamma node. Definition: consecutive trillionth-grid endpoints.
Output: a rational interval for 35000 to the negative node exponent.
Role: separate endpoint discovery from the subsequent kernel certificate. -/
def checkpoint35000Ratios (a : ℚ) : ℚ × ℚ :=
  let rs : List ℕ := [16932791, 5947326, 1237974, 152720, 6617, 100, 0, 0, 0, 0]
  let r := rs[(Analysis.gammaResolventCoefficients.map Prod.fst).idxOf a]?.getD 0
  ((r : ℚ) / 1000000000000, ((r + 1 : ℕ) : ℚ) / 1000000000000)

/-- Claim: all ten power intervals at cutoff 35000 pass the common ratio checker.
Proof: exact twentieth-power kernel arithmetic. Role: certify the numerical node input. -/
theorem checkpoint35000_node_check :
    Analysis.gammaFiniteEulerRatioCheck 35000 checkpoint35000Ratios = true := by
  decide +kernel

/-- Claim: the rational Euler weight, signed slope and main tail satisfy three caps.
Proof: signed endpoint selection and kernel rational arithmetic.
Role: retain both negative products in the analytic boundary estimate. -/
theorem checkpoint35000_scalar_checks :
    (9797 / 1000000000 : ℚ) ≤ Analysis.gammaFiniteEulerLower checkpoint35000Ratios ∧
      gammaFiniteWeightedUpper gammaSlopeRationalCoefficient checkpoint35000Ratios ≤
        (-10375 / 1000000000 : ℚ) ∧
      gammaFiniteWeightedUpper (gammaTailRationalCoefficient 35000) checkpoint35000Ratios ≤
        (7393 / 1000 : ℚ) := by
  decide +kernel

/-- Input: RH. Claim: the smoothed Mangoldt sum at 35000 is at least 34969.
Proof: bound its refined one-sided error using sqrt(35000)<=188 and log(35000)<=16 log(2).
Role: bound the negative slope product without enumerating prime powers. -/
theorem checkpoint35000_smoothed_lower (hRH : RiemannHypothesis) :
    (34969 : ℝ) ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 35000 := by
  have h := logWeightedMangoldtSum_ge_rational_refined hRH (by norm_num only : (1 : ℝ) < 35000)
  have hs : Real.sqrt (35000 : ℝ) ≤ 188 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num only, by norm_num only⟩
  have hl :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 35000) (by norm_num only : (35000 : ℝ) ≤ 2 ^ 16)
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hlog : Real.log (35000 : ℝ) ≤ 111 / 10 := by
    linarith only [hl, Real.log_two_lt_d9]
  linarith only [h, hs, hlog]

/-- Input: RH. Claim: the smoothed sum at 33800 is at most 33800+46/5.
Proof: apply the one-sided square-root upper error and sqrt(33800)<=184.
Role: supply the smaller endpoint for the asymmetric Chebyshev comparison. -/
theorem checkpoint35000_smoothed33800_upper (hRH : RiemannHypothesis) :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 33800 ≤ (33800 + 46 / 5 : ℝ) := by
  have h := logWeightedMangoldtSum_le_add_sqrt_twentieth hRH (by norm_num only : (1 : ℝ) < 33800)
  have hs : Real.sqrt (33800 : ℝ) ≤ 184 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num only, by norm_num only⟩
  linarith only [h, hs]

/-- Claim: the actual Euler weight at 35000 is at least 9797/10^9.
Proof: transfer the rational node lower bound to the real weight.
Role: supply the first nonnegative factor in the boundary comparison. -/
theorem checkpoint35000_weight_lower :
    (9797 / 1000000000 : ℝ) ≤ Analysis.gammaResolventEulerWeight 35000 := by
  have h := (Analysis.gamma_finite_ratio_check_euler_bounds checkpoint35000_node_check).1
  have hc := (Rat.cast_le (K := ℝ)).mpr checkpoint35000_scalar_checks.1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h hc
  linarith only [hc, h]

/-- Claim: the actual logarithmic Euler slope at 35000 is at most -10375/10^9.
Proof: use signed node bounds and the exact slope identity.
Role: supply the nonpositive coefficient of the smoothed-sum product. -/
theorem checkpoint35000_slope_upper :
    gammaEulerLogSlope 35000 ≤ (-10375 / 1000000000 : ℝ) := by
  have h :=
    (gamma_finite_weighted_bounds checkpoint35000_node_check gammaSlopeRationalCoefficient).2
  have hc := (Rat.cast_le (K := ℝ)).mpr checkpoint35000_scalar_checks.2.1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] at h hc
  rw [← gamma_slope_eq_weighted] at h
  linarith only [h, hc]

/-- Claim: the integrated main tail at 35000 is at most 7393/1000.
Proof: transfer the signed rational comparison through the exact main-tail identity.
Role: complete the compact analytic boundary inputs. -/
theorem checkpoint35000_main_upper : gammaEulerTailMain 35000 ≤ (7393 / 1000 : ℝ) := by
  have h :=
    (gamma_finite_weighted_bounds checkpoint35000_node_check (gammaTailRationalCoefficient 35000)).2
  have hc := (Rat.cast_le (K := ℝ)).mpr checkpoint35000_scalar_checks.2.2
  rw [← gamma_tail_main_eq_weighted (by norm_num only : (0 : ℚ) < 35000)] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h hc
  linarith only [h, hc]

/-- Under RH, the one-sided smoothed estimates imply psi(35000)>=32667.
The asymmetric difference quotient retains both errors. This bounds the signed boundary term. -/
theorem checkpoint35000_psi_lower (hRH : RiemannHypothesis) :
    (32667 : ℝ) ≤ Chebyshev.psi 35000 := by
  have h := psi_lower_of_one_sided_errors (by norm_num only : (0 : ℝ) < 33800)
    (by norm_num only : (33800 : ℝ) < 35000) (checkpoint35000_smoothed33800_upper hRH)
    (show (35000 : ℝ) - 31 ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 35000 by
      norm_num only
      exact checkpoint35000_smoothed_lower hRH)
  linarith only [h]

/-- Input: RH. Claim: the signed Euler boundary tail at 35000 is at most 6711/1000.
Proof: keep the negative psi and smoothed-sum products using the proved scalar inputs.
Role: certify a small checkpoint with ten node intervals and no prime-power payload. -/
theorem gamma_boundary35000_upper (hRH : RiemannHypothesis) :
    gammaEulerBoundaryTail 35000 ≤ (6711 / 1000 : ℝ) := by
  have h :=
    gamma_euler_boundary_tail_upper (by norm_num only : (0 : ℝ) ≤ 9797 / 1000000000)
      checkpoint35000_weight_lower (by norm_num only : (0 : ℝ) ≤ 32667)
      (checkpoint35000_psi_lower hRH)
      checkpoint35000_slope_upper (by norm_num only) (by norm_num only : (0 : ℝ) ≤ 34969)
      (checkpoint35000_smoothed_lower hRH) checkpoint35000_main_upper
  linarith only [h]

/-- Rational absolute error envelope at cutoff 35000, using the same ten node intervals.
The root cap is 188 and log cap is 56/5. This certifies the transport error without enumeration. -/
def checkpoint35000Error : ℚ :=
  (Analysis.gammaResolventCoefficients.map
    (fun ab ↦
      let σ := (1 / 2 : ℚ) + ab.1
      let v := (checkpoint35000Ratios ab.1).2
      |ab.2| * ((1 / 20 : ℚ) * (σ ^ 2 * (188 * v) / (σ - 1 / 2)) +
        (1839 / 1000 : ℚ) * (v * (1 + σ * (56 / 5))) + (21 / 20 : ℚ) * (σ * v)))).sum

/-- The rational envelope is at most 1/2000, by kernel rational arithmetic.
This supplies the absolute error input for half-line prefix transport. -/
theorem checkpoint35000_error_check : checkpoint35000Error ≤ 1 / 2000 := by
  decide +kernel

/-- The actual error budget is at most 1/2000, independently of RH.
Transfer the ten power endpoints through the general error envelope, preserving the signed main. -/
theorem checkpoint35000_error_upper : gammaEulerTailErrorBudget 35000 ≤ (1 / 2000 : ℝ) := by
  have hr : Real.sqrt (35000 : ℝ) ≤ 188 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num only, by norm_num only⟩
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 35000)
    (by norm_num only : (35000 : ℝ) ≤ 2 ^ 16)
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hlog : Real.log (35000 : ℝ) ≤ 56 / 5 := by
    linarith only [hl, Real.log_two_lt_d9]
  have h := gammaEulerTailErrorBudget_le_envelope (by norm_num only : (1 : ℝ) ≤ 35000)
    hr hlog (fun a ↦ ((checkpoint35000Ratios a).2 : ℝ))
    (fun ab hab ↦ (Analysis.gamma_finite_ratio_check_sound checkpoint35000_node_check ab hab).2)
  have hc : gammaEulerTailErrorBudget 35000 ≤ (checkpoint35000Error : ℝ) := by
    norm_num only [checkpoint35000Error, gammaEulerErrorEnvelope, Rat.cast_list_sum, List.map_map,
      Function.comp_def, Rat.cast_mul, Rat.cast_abs, Rat.cast_add, Rat.cast_div, Rat.cast_pow,
      Rat.cast_sub, Rat.cast_ofNat, Rat.cast_one] at h ⊢
    exact h
  have he := (Rat.cast_le (K := ℝ)).mpr checkpoint35000_error_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at he
  exact hc.trans he

/-- Under RH, every later Gamma prefix is at least 11147/2000.
Transport the seed through the certified signed boundary and absolute error at 35000.
This is the input to the Gaussian prefix comparison for the log240 MR branch. -/
theorem gamma_prefix35000_lower (hRH : RiemannHypothesis) {b : ℝ} (hb : 35000 ≤ b) :
    (11147 / 2000 : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  have h := gamma_prefix_lower_of_checkpoint_error (E := 1 / 2000) (U := 6711 / 1000) hRH
    (by norm_num only : (3 : ℝ) ≤ 35000) hb
    (by norm_num only [Rat.cast_div, Rat.cast_ofNat]; exact gamma_boundary35000_upper hRH)
    (by norm_num only [Rat.cast_div, Rat.cast_ofNat]; exact checkpoint35000_error_upper)
  norm_num only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat] at h
  exact h

end PseudoPrime.LLS
