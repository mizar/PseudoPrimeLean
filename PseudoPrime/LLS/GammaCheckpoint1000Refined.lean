/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaCheckpoint1000
/-! # Refined error and prefix bounds at the existing checkpoint 1000 -/

@[expose] public section
namespace PseudoPrime.LLS

/-- Input: RH. Claim: the signed Euler boundary tail at 1000 is at most 4073/500.
Proof: keep the negative psi and smoothed-sum products using the proved scalar inputs.
Role: certify a small checkpoint with ten node intervals and no prime-power payload. -/
theorem gamma_boundary1000_refined (hRH : RiemannHypothesis) :
    gammaEulerBoundaryTail 1000 ≤ (4073 / 500 : ℝ) := by
  have h :=
    gamma_euler_boundary_tail_upper (by norm_num only : (0 : ℝ) ≤ 435675 / 1000000000)
      checkpoint1000_weight_lower (by norm_num only : (0 : ℝ) ≤ 810) (checkpoint1000_psi_lower hRH)
      checkpoint1000_slope_upper (by norm_num only) (by norm_num only : (0 : ℝ) ≤ 984)
      (checkpoint1000_smoothed_lower hRH) checkpoint1000_main_upper
  linarith only [h]

/-- Rational absolute error envelope at cutoff 1000, using the same ten node intervals.
The root cap is 32 and log cap is 7. This certifies the transport error without enumeration. -/
def checkpoint1000Error : ℚ :=
  (Analysis.gammaResolventCoefficients.map
    (fun ab ↦
      let σ := (1 / 2 : ℚ) + ab.1
      let v := (checkpoint1000Ratios ab.1).2
      |ab.2| * ((1 / 20 : ℚ) * (σ ^ 2 * (32 * v) / (σ - 1 / 2)) +
        (1839 / 1000 : ℚ) * (v * (1 + σ * (7))) + (21 / 20 : ℚ) * (σ * v)))).sum

/-- The rational envelope is at most 9/1000, by kernel rational arithmetic.
This supplies the absolute error input for half-line prefix transport. -/
theorem checkpoint1000_error_check : checkpoint1000Error ≤ 9 / 1000 := by
  decide +kernel

/-- The actual error budget is at most 9/1000, independently of RH.
Transfer the ten power endpoints through the general error envelope, preserving the signed main. -/
theorem checkpoint1000_error_upper : gammaEulerTailErrorBudget 1000 ≤ (9 / 1000 : ℝ) := by
  have hr : Real.sqrt (1000 : ℝ) ≤ 32 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num only, by norm_num only⟩
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 1000)
    (by norm_num only : (1000 : ℝ) ≤ 2 ^ 10)
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hlog : Real.log (1000 : ℝ) ≤ 7 := by
    linarith only [hl, Real.log_two_lt_d9]
  have h := gammaEulerTailErrorBudget_le_envelope (by norm_num only : (1 : ℝ) ≤ 1000)
    hr hlog (fun a ↦ ((checkpoint1000Ratios a).2 : ℝ))
    (fun ab hab ↦ (Analysis.gamma_finite_ratio_check_sound checkpoint1000_node_check ab hab).2)
  have hc : gammaEulerTailErrorBudget 1000 ≤ (checkpoint1000Error : ℝ) := by
    norm_num only [checkpoint1000Error, gammaEulerErrorEnvelope, Rat.cast_list_sum, List.map_map,
      Function.comp_def, Rat.cast_mul, Rat.cast_abs, Rat.cast_add, Rat.cast_div, Rat.cast_pow,
      Rat.cast_sub, Rat.cast_ofNat, Rat.cast_one] at h ⊢
    exact h
  have he := (Rat.cast_le (K := ℝ)).mpr checkpoint1000_error_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at he
  exact hc.trans he

/-- Under RH, every later Gamma prefix is at least 413/100.
Transport the seed through the certified signed boundary and absolute error at 1000.
This supplies credit 413/100 to the clipped Gamma witness comparison. -/
theorem gamma_prefix1000_refined (hRH : RiemannHypothesis) {b : ℝ} (hb : 1000 ≤ b) :
    (413 / 100 : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  have h := gamma_prefix_lower_of_checkpoint_error (E := 9 / 1000) (U := 4073 / 500) hRH
    (by norm_num only : (3 : ℝ) ≤ 1000) hb
    (by norm_num only [Rat.cast_div, Rat.cast_ofNat]; exact gamma_boundary1000_refined hRH)
    (by norm_num only [Rat.cast_div, Rat.cast_ofNat]; exact checkpoint1000_error_upper)
  norm_num only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat] at h
  exact h

end PseudoPrime.LLS
