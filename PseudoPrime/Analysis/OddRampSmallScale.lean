/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaLocalScale1936

/-! # Continuous odd-prime ramp bounds from scale 1600 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- At bases at least three and scales between 1600 and 1764, the cutoff is
below the eighth power. At most seven powers remain, so the normalized count
including one endpoint is at most 21/100. -/
theorem odd_ramp_small1600 {p : ℕ} (hp : 3 ≤ p) {x : ℝ} (hx : 1600 ≤ x) (hX : x ≤ 1764) :
    (gammaRampPowerCount p x + 1) / Real.sqrt x ≤ (21 / 100 : ℝ) := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hpow : (99 / 40 : ℝ) * x < (p : ℝ) ^ (7 + 1) := by
    have hm := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 3) hpR 8
    norm_num only at hm
    linarith only [hX, hm]
  have hn :=
    gamma_ramp_count_le_of_power (Nat.lt_of_lt_of_le (by decide : 1 < 3) hp) (by linarith only [hx])
      hpow
  norm_num only at hn
  have hs : (40 : ℝ) ≤ Real.sqrt x :=
    (Real.le_sqrt (by norm_num only) (by linarith only [hx])).mpr
      (by
        norm_num only; exact hx)
  apply (div_le_iff₀ (by linarith only [hs] : 0 < Real.sqrt x)).mpr
  linarith only [hn, hs]

/-- At bases at least three and scales at least 1764, the logarithmic count
envelope is at most 21/100. Use the square-root tangent at 42 and the certified
lower bound 109/100 for the prime logarithm. -/
theorem odd_ramp_large1600 {p : ℕ} (hp : 3 ≤ p) {x : ℝ} (hx : 1764 ≤ x) :
    (Real.log ((99 / 40 : ℝ) * x) / Real.log p + 1) / Real.sqrt x ≤ (21 / 100 : ℝ) := by
  have hc : rationalLogIntervalCheck 42 6 20 0 (15 / 4) = true := by decide +kernel
  have h42 := (rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h42
  have hraw :=
    log_mul_add_div_sqrt_le_of_anchor (c := (99 / 40 : ℝ)) (a := 42) (b :=
      (109 / 100 : ℝ) * (21 / 100)) (d := 109 / 100) (by norm_num only) (by norm_num only)
      (by
        norm_num only; exact hx)
      (by linarith only [local1936_anchor_logs.1, h42]) (by norm_num only)
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hlogp : (109 / 100 : ℝ) ≤ Real.log p := by
    have h := Real.log_le_log (by norm_num only : (0 : ℝ) < 3) hpR
    linarith only [h, Real.log_three_gt_d9]
  have hcut : 0 ≤ Real.log ((99 / 40 : ℝ) * x) := Real.log_nonneg (by nlinarith only [hx])
  have hd := div_le_div_of_nonneg_left hcut (by norm_num only : (0 : ℝ) < 109 / 100) hlogp
  have hm := div_le_div_of_nonneg_right (add_le_add hd (le_refl (1 : ℝ))) (Real.sqrt_nonneg x)
  have he :
    (Real.log ((99 / 40 : ℝ) * x) / (109 / 100) + 1) / Real.sqrt x =
      ((Real.log ((99 / 40 : ℝ) * x) + 109 / 100) / Real.sqrt x) / (109 / 100) := by
    ring
  rw [he] at hm
  exact
    hm.trans ((div_le_iff₀ (by norm_num only : (0 : ℝ) < 109 / 100)).mpr (by linarith only [hraw]))

/-- For every base at least three and scale at least 1600, the normalized
cutoff count plus one is at most 21/100. Join the exact low-scale power count
and continuous logarithmic envelope, without checking individual scales. -/
theorem odd_ramp_count_le_of_ge_1600 {p : ℕ} (hp : 3 ≤ p) {x : ℝ} (hx : 1600 ≤ x) :
    (gammaRampPowerCount p x + 1) / Real.sqrt x ≤ (21 / 100 : ℝ) := by
  by_cases hX : x ≤ 1764
  · exact odd_ramp_small1600 hp hx hX
  · have hc :=
      gamma_ramp_count_le_log (Nat.lt_of_lt_of_le (by decide : 1 < 3) hp) (by linarith only [hx])
    exact
      (div_le_div_of_nonneg_right (add_le_add hc (le_refl (1 : ℝ))) (Real.sqrt_nonneg x)).trans
        (odd_ramp_large1600 hp (le_of_not_ge hX))

end PseudoPrime.Analysis
