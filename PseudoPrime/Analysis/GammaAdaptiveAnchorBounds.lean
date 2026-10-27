/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaAnchoredReciprocalBounds

/-! # Checked reciprocal Euler coefficients at arbitrary anchors -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a positive rational anchor, checked node intervals and a rational positive-node mass cap.
Claim: the real anchored coefficient is at most the cap. Proof: shift node powers and sum
nonnegative coefficient bounds. Role: certify arbitrary anchors without repeating their proofs. -/
theorem gamma_anchored_coefficient_le_of_check {a C : ℚ} {r : ℚ → ℚ × ℚ} (ha : 0 < a)
    (hc : gammaFiniteEulerRatioCheck a r = true)
    (hC : (gammaResolventCoefficients.map (fun ab ↦ max ab.2 0 * (a * (r ab.1).2))).sum ≤ C) :
    gammaAnchoredReciprocalCoefficient (a : ℝ) ≤ (C : ℝ) := by
  have haR : (0 : ℝ) < a := Rat.cast_pos.mpr ha
  have hn (ab : ℚ × ℚ) (hab : ab ∈ gammaResolventCoefficients) :
    (a : ℝ) ^ (1 - (1 / 2 + (ab.1 : ℝ))) ≤ (a : ℝ) * ((r ab.1).2 : ℝ) := by
    have h := (gamma_finite_ratio_check_sound hc ab hab).2
    rw [show (1 : ℝ) - (1 / 2 + (ab.1 : ℝ)) = -(1 / 2 + (ab.1 : ℝ)) + 1 by ring,
      Real.rpow_add_one haR.ne']
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left h haR.le
  have hs :=
    List.sum_le_sum
      (fun (ab : ℚ × ℚ) hab ↦ mul_le_mul_of_nonneg_left (hn ab hab) (le_max_right (ab.2 : ℝ) 0))
  have hCr := (Rat.cast_le (K := ℝ)).mpr hC
  norm_num only [Rat.cast_list_sum, List.map_map, Function.comp_def, Rat.cast_mul, Rat.cast_max,
    Rat.cast_zero] at hCr
  exact hs.trans hCr

/-- Input: a positive anchor a, p>1 with p>=a, and an anchored coefficient cap C.
Claim: the actual signed prime Euler cost is at most C/(p-1). Proof: bound every positive
power from the same anchor and sum the reciprocal series. Role: reusable prime-cost transfer. -/
theorem gamma_prime_euler_cost_le_of_anchored_coefficient {a p C : ℝ} (ha : 0 < a) (hp : 1 < p)
    (hap : a ≤ p) (hC : gammaAnchoredReciprocalCoefficient a ≤ C) :
    gammaPrimeEulerCost p ≤ C / (p - 1) := by
  apply gamma_prime_euler_cost_le_of_power_reciprocal hp
  intro k
  have hpow := hap.trans (le_self_pow₀ hp.le (Nat.succ_ne_zero k))
  have he := gamma_euler_weight_le_anchored_reciprocal ha hpow
  exact
    he.trans
      (mul_le_mul_of_nonneg_right hC (inv_nonneg.mpr (pow_nonneg (zero_lt_one.trans hp).le _)))

/-- Input: 0<a<=b. Claim: the anchored coefficient at b is no larger than at a.
Proof: each shifted exponent is nonpositive and every coefficient is nonnegative.
Role: justify improving the envelope when raising its anchor. -/
theorem gamma_anchored_coefficient_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    gammaAnchoredReciprocalCoefficient b ≤ gammaAnchoredReciprocalCoefficient a := by
  apply List.sum_le_sum
  intro ab habmem
  have hσ : (1 : ℝ) ≤ 1 / 2 + (ab.1 : ℝ) := by
    have h :=
      Rat.cast_lt (K := ℝ).mpr
        (List.forall_iff_forall_mem.mp gammaResolvent_scales_gt_half ab habmem)
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
    linarith only [h]
  exact
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha hab (sub_nonpos.mpr hσ))
      (le_max_right _ _)

end PseudoPrime.Analysis
