/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogPowerAsymptotics

/-! # Uniform power budgets for signed half-scale character estimates -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For real exponents a < b, L^a/L^b tends to zero at infinity.
Rewrite the ratio as a negative real power on the positive half-line.
This supplies the three independent scale margins in the signed-half budget. -/
theorem tendsto_rpow_div_rpow_of_lt {a b : ℝ} (hab : a < b) :
    Filter.Tendsto (fun L : ℝ ↦ L ^ a / L ^ b) Filter.atTop (nhds 0) := by
  have h := tendsto_rpow_neg_atTop (sub_pos.mpr hab)
  have he : (fun L : ℝ ↦ L ^ (-(b - a))) =ᶠ[Filter.atTop] (fun L : ℝ ↦ L ^ a / L ^ b) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with L hL
    rw [show -(b - a) = a - b by ring, Real.rpow_sub hL]
  exact h.congr' he

/-- Fix a>1, 1-δ<a/2, positive C and θ and real cost constants. Uniformly for
large L, the lower window cutoff exceeds 200 and the signed-phase, square-root
and linear exclusion costs are strictly below θCL^a/2. Normalize by L^a and
use three vanishing power ratios. No character or conductor affects the start. -/
theorem eventually_signed_half_power_budget {a δ C θ C₁ C₂ Cₘ : ℝ} (ha : 1 < a) (hδ : 1 - δ < a / 2)
    (hC : 0 < C) (hθ : 0 < θ) :
    ∀ᶠ L : ℝ in Filter.atTop,
      200 ≤ θ * (C * L ^ a) ∧
        C₁ * Real.sqrt (C * L ^ a) * L ^ (1 - δ) +
            (C₂ + ((1 / 2 : ℝ) + 36 * Real.log 2)) * Real.sqrt (C * L ^ a) +
            2 * Real.log 2 * Cₘ * L <
          θ * (C * L ^ a) / 2 := by
  have h1 :=
    (tendsto_rpow_div_rpow_of_lt (show a / 2 + (1 - δ) < a by linarith only [hδ])).const_mul
      (C₁ * Real.sqrt C)
  have h2 :=
    (tendsto_rpow_div_rpow_of_lt (show a / 2 < a by linarith only [ha])).const_mul
      ((C₂ + ((1 / 2 : ℝ) + 36 * Real.log 2)) * Real.sqrt C)
  have h3 := (tendsto_rpow_div_rpow_of_lt ha).const_mul (2 * Real.log 2 * Cₘ)
  have hlim := (h1.add h2).add h3
  simp only [mul_zero, add_zero] at hlim
  have hsmall := hlim.eventually_lt_const (div_pos (mul_pos hθ hC) (by norm_num only : (0 : ℝ) < 2))
  have hlarge :=
    ((tendsto_rpow_atTop (show 0 < a by linarith only [ha])).const_mul_atTop
          (mul_pos hθ hC)).eventually_ge_atTop
      200
  filter_upwards [hsmall, hlarge, Filter.eventually_gt_atTop (0 : ℝ)] with L hs hl hL
  have hp := Real.rpow_pos_of_pos hL a
  have hsqrt : Real.sqrt (L ^ a) = L ^ (a / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hL.le]
    congr 1
    ring
  have hm := mul_lt_mul_of_pos_right hs hp
  rw [Real.rpow_one] at hm
  have he :
    (C₁ * Real.sqrt C * (L ^ (a / 2 + (1 - δ)) / L ^ a) +
          (C₂ + ((1 / 2 : ℝ) + 36 * Real.log 2)) * Real.sqrt C * (L ^ (a / 2) / L ^ a) +
          2 * Real.log 2 * Cₘ * (L / L ^ a)) *
        L ^ a =
      C₁ * Real.sqrt (C * L ^ a) * L ^ (1 - δ) +
        (C₂ + ((1 / 2 : ℝ) + 36 * Real.log 2)) * Real.sqrt (C * L ^ a) +
        2 * Real.log 2 * Cₘ * L := by
    rw [Real.sqrt_mul hC.le, hsqrt, Real.rpow_add hL]
    field_simp [hp.ne']
  refine ⟨?_, ?_⟩
  · nlinarith only [hl]
  · rw [he] at hm
    nlinarith only [hm]

/-- For 0<ε<min(2δ,1), a=2-ε satisfies the two power-budget inequalities
and a<2. Rearrange the strict exponent bounds. This specializes the uniform
power transfer to the fixed subquadratic exponents in the implementation plan. -/
theorem signed_half_exponents_of_epsilon {ε δ : ℝ} (hε : 0 < ε ∧ ε < min (2 * δ) 1) :
    1 < 2 - ε ∧ 1 - δ < (2 - ε) / 2 ∧ 2 - ε < 2 := by
  have hδ := lt_of_lt_of_le hε.2 (min_le_left (2 * δ) 1)
  have h1 := lt_of_lt_of_le hε.2 (min_le_right (2 * δ) 1)
  constructor
  · linarith only [h1]
  constructor
  · linarith only [hδ]
  · linarith only [hε.1]

end PseudoPrime.Analysis
