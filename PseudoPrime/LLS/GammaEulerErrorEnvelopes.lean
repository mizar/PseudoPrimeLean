/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaEulerTailErrorBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-! # Generic numerical envelopes and monotonicity for Euler-tail errors -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: sigma>1, cutoff a>=1, and upper bounds for sqrt a, a^(-sigma), log a.
Claim: the explicit RH error budget is bounded by the displayed scalar envelope.
Proof: compare each nonnegative product. Role: reuse rational node data at arbitrary cutoffs. -/
theorem powerRiemannErrorBudget_le_envelope {σ a r v l : ℝ} (hσ : 1 < σ) (ha : 1 ≤ a)
    (hr : Real.sqrt a ≤ r) (hv : a ^ (-σ) ≤ v) (hl : Real.log a ≤ l) :
    powerRiemannErrorBudget σ a ≤
      (1 / 20 : ℝ) * (σ ^ 2 * (r * v) / (σ - 1 / 2)) + (1839 / 1000 : ℝ) * (v * (1 + σ * l)) +
        (21 / 20 : ℝ) * (σ * v) := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hσ0 : 0 ≤ σ := (zero_lt_one.trans hσ).le
  have hd : 0 ≤ σ - 1 / 2 := by linarith only [hσ]
  have hv0 := (Real.rpow_nonneg ha0.le (-σ)).trans hv
  have hu : a ^ (1 / 2 - σ) ≤ r * v := by
    rw [show (1 / 2 : ℝ) - σ = 1 / 2 + (-σ) by ring, Real.rpow_add ha0, ← Real.sqrt_eq_rpow]
    exact mul_le_mul hr hv (Real.rpow_nonneg ha0.le _) ((Real.sqrt_nonneg a).trans hr)
  have hl0 : 0 ≤ 1 + σ * Real.log a :=
    add_nonneg (by norm_num only) (mul_nonneg hσ0 (Real.log_nonneg ha))
  have hlog := add_le_add_right (mul_le_mul_of_nonneg_left hl hσ0) 1
  have h1 :=
    mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hu (sq_nonneg σ)) hd)
      (by norm_num only : (0 : ℝ) ≤ 1 / 20)
  have h2 :=
    mul_le_mul_of_nonneg_left (mul_le_mul hv hlog hl0 hv0)
      (by norm_num only : (0 : ℝ) ≤ 1839 / 1000)
  have h3 :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv hσ0)
      (by norm_num only : (0 : ℝ) ≤ 21 / 20)
  exact add_le_add (add_le_add h1 h2) h3

/-- Input: sigma>1 and 3<=a<=b. Claim: the scalar RH error budget decreases.
Proof: combine decreasing powers with monotonicity of log(t)/t^sigma.
Role: propagate a certified cutoff error through an entire half-line. -/
theorem powerRiemannErrorBudget_antitone_of_three_le {σ a b : ℝ} (hσ : 1 < σ) (ha : 3 ≤ a)
    (hab : a ≤ b) : powerRiemannErrorBudget σ b ≤ powerRiemannErrorBudget σ a := by
  have hσ0 : 0 < σ := zero_lt_one.trans hσ
  have ha0 : 0 < a := by linarith only [ha]
  have hb0 := ha0.trans_le hab
  have hi : σ⁻¹ ≤ 1 := (inv_le_one₀ hσ0).mpr hσ.le
  have hexp : Real.exp σ⁻¹ ≤ a := ((Real.exp_le_exp.mpr hi).trans Real.exp_one_lt_three.le).trans ha
  have hlog :=
    Real.log_div_self_rpow_antitoneOn hσ0 (Set.mem_Ici.mpr hexp) (Set.mem_Ici.mpr (hexp.trans hab))
      hab
  simp only [div_eq_mul_inv, ← Real.rpow_neg ha0.le, ← Real.rpow_neg hb0.le] at hlog
  have hp := Real.rpow_le_rpow_of_nonpos ha0 hab (neg_nonpos.mpr hσ0.le)
  have hm := mul_le_mul_of_nonneg_left hlog hσ0.le
  have hs : b ^ (-σ) * (1 + σ * Real.log b) ≤ a ^ (-σ) * (1 + σ * Real.log a) := by
    nlinarith only [hp, hm]
  have hhalf : (1 / 2 : ℝ) - σ ≤ 0 := by linarith only [hσ]
  have hfirst :=
    mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha0 hab hhalf) (sq_nonneg σ))
        (show 0 ≤ σ - 1 / 2 by linarith only [hσ]))
      (show (0 : ℝ) ≤ 1 / 20 by norm_num only)
  have hsecond := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ 1839 / 1000 by norm_num only)
  have hthird :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hσ0.le)
      (show (0 : ℝ) ≤ 21 / 20 by norm_num only)
  exact add_le_add (add_le_add hfirst hsecond) hthird

/-- Input: root, power and logarithm upper bounds, and an exponent sigma.
Definition: the three-term scalar envelope for the integrated RH error.
Output: a real numerical allowance. Role: combine finite rational node certificates. -/
noncomputable def gammaEulerErrorEnvelope (r v l : ℝ) (σ : ℝ) : ℝ :=
  (1 / 20 : ℝ) * (σ ^ 2 * (r * v) / (σ - 1 / 2)) + (1839 / 1000 : ℝ) * (v * (1 + σ * l)) +
    (21 / 20 : ℝ) * (σ * v)

/-- Input: 3<=a<=b. Claim: the full signed-kernel absolute error budget decreases.
Proof: sum the scalar monotonicity inequalities with nonnegative coefficient magnitudes.
Role: reuse one finite cutoff certificate for every larger cutoff, independently of RH. -/
theorem gammaEulerTailErrorBudget_antitone_of_three_le {a b : ℝ} (ha : 3 ≤ a) (hab : a ≤ b) :
    gammaEulerTailErrorBudget b ≤ gammaEulerTailErrorBudget a := by
  dsimp only [gammaEulerTailErrorBudget, gammaRealPowerList]
  simp only [List.map_map, Function.comp_def]
  exact
    List.sum_le_sum
      (fun ab hab' ↦
        mul_le_mul_of_nonneg_left
          (powerRiemannErrorBudget_antitone_of_three_le
            (gammaResolvent_real_exponents_gt_one ab hab') ha hab)
          (abs_nonneg (ab.2 : ℝ)))

/-- Input: a>=1 and root, logarithm and node-power upper bounds.
Claim: the full kernel error budget is bounded by their finite envelope sum.
Proof: apply the scalar comparison to each certified node.
Role: certify cutoff constants without a new analytic proof for each scale. -/
theorem gammaEulerTailErrorBudget_le_envelope {a r l : ℝ} (ha : 1 ≤ a) (hr : Real.sqrt a ≤ r)
    (hl : Real.log a ≤ l) (v : ℚ → ℝ)
    (hv : ∀ ab ∈ Analysis.gammaResolventCoefficients, a ^ (-(1 / 2 + (ab.1 : ℝ))) ≤ v ab.1) :
    gammaEulerTailErrorBudget a ≤
      (Analysis.gammaResolventCoefficients.map
          (fun ab ↦
            |(ab.2 : ℝ)| * gammaEulerErrorEnvelope r (v ab.1) l (1 / 2 + (ab.1 : ℝ)))).sum := by
  dsimp only [gammaEulerTailErrorBudget, gammaRealPowerList]
  simp only [List.map_map, Function.comp_def]
  exact
    List.sum_le_sum
      (fun ab hab ↦
        mul_le_mul_of_nonneg_left
          (powerRiemannErrorBudget_le_envelope (gammaResolvent_real_exponents_gt_one ab hab) ha hr
            (hv ab hab) hl)
          (abs_nonneg (ab.2 : ℝ)))

end PseudoPrime.LLS
