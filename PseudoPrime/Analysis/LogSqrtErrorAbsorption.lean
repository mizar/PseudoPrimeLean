/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogPowerAsymptotics

/-!
# Error absorption for the uniform Mellin-kernel comparison

Choose a sufficiently large real scale to control the logarithmic remainder, and reserve
a positive allowance in the integral coefficient. These estimates complete the numerical
step after the finite upper and lower bounds in Proposition 6.1.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For positive index, error constant, mass coefficient and allowance, choose a scale
threshold at least two so the uniform remainder is bounded by one quarter of the allowance
times the mass coefficient and the logarithmic modulus parameter. The latter parameter
must exceed an explicit constant. Use the vanishing logarithm-to-square-root ratio.
This controls the analytic and modulus errors in Proposition 6.1. -/
theorem exists_error_absorption_scale {H C B ε : ℝ} (hH : 0 < H) (hC : 0 < C) (hB : 0 < B)
    (hε : 0 < ε) :
    ∃ T : ℝ,
      2 ≤ T ∧
        ∀ x : ℝ,
          T ≤ x →
            ∀ L : ℝ,
              8 * H * C / (ε * B) ≤ L →
                H * C * (1 + L * Real.log x / Real.sqrt x) ≤ ε * B * L / 4 := by
  have hp : 0 < 8 * H * C := mul_pos (mul_pos (by norm_num only) hH) hC
  have heB := mul_pos hε hB
  have hr := (tendsto_log_pow_div_sqrt 1).eventually (eventually_lt_nhds (div_pos heB hp))
  simp only [pow_one] at hr
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (hr.and (Filter.eventually_ge_atTop (2 : ℝ)))
  refine ⟨max T 2, le_max_right _ _, ?_⟩
  intro x hx L hL
  have hx' := (hT x ((le_max_left T 2).trans hx)).1.le
  have hLpos : 0 < L := (div_pos hp heB).trans_le hL
  have hc := (div_le_iff₀ heB).mp hL
  have hr' := (le_div_iff₀ hp).mp hx'
  have hm := mul_le_mul_of_nonneg_right hr' hLpos.le
  rw [mul_div_assoc]
  nlinarith only [hc, hm]

/-- A comparison with a slightly reduced main coefficient implies the desired comparison
with factor `1+epsilon`, provided the coefficient allowance satisfies the stated identity.
Multiply by `1+epsilon` and cancel the positive common factor.
This restores the original integral coefficient after error absorption. -/
theorem coefficient_le_of_allowance {A H δ ε B L s : ℝ} (hε : 0 < ε)
    (hcoef : (A - H * δ) * (1 + ε) = A * (1 + 3 * ε / 4))
    (hbound : (A - H * δ) * s ≤ (1 + 3 * ε / 4) * B * L) : A * s ≤ (1 + ε) * B * L := by
  have he : 0 < 1 + ε := by linarith only [hε]
  have he' : 0 < 1 + 3 * ε / 4 := by linarith only [hε]
  have h := mul_le_mul_of_nonneg_right hbound he.le
  apply (mul_le_mul_iff_left₀ he').mp
  calc
    A * s * (1 + 3 * ε / 4) = ((A - H * δ) * (1 + ε)) * s := by
      rw [hcoef]; ring
    _ = (A - H * δ) * s * (1 + ε) := by ring
    _ ≤ ((1 + 3 * ε / 4) * B * L) * (1 + ε) := h
    _ = ((1 + ε) * B * L) * (1 + 3 * ε / 4) := by ring

/-- For positive main coefficient, index and error allowance, choose a positive reduction
whose coefficient identity converts a `1+3*epsilon/4` estimate to `1+epsilon`.
Use `A*epsilon/(4*H*(1+epsilon))` and cancel its positive denominator.
This leaves enough allowance for the two error contributions in Proposition 6.1. -/
theorem exists_coefficient_allowance {A H ε : ℝ} (hA : 0 < A) (hH : 0 < H) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ (A - H * δ) * (1 + ε) = A * (1 + 3 * ε / 4) := by
  have he : 0 < 1 + ε := by linarith only [hε]
  let δ := A * ε / (4 * H * (1 + ε))
  have hd : 0 < 4 * H * (1 + ε) := mul_pos (mul_pos (by norm_num only) hH) he
  refine ⟨δ, div_pos (mul_pos hA hε) hd, ?_⟩
  have hc : δ * (4 * H * (1 + ε)) = A * ε := div_mul_cancel₀ _ (ne_of_gt hd)
  nlinarith only [hc]

end PseudoPrime.Analysis
