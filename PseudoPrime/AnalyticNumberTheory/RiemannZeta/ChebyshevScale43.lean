/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevRosser

/-! # The logarithmic scale for the Chebyshev estimate -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- If `x > 0` and `0 ≤ δ ≤ 1/2`, bound the square root and three-halves
power at `x(1 + δ)` by linear expressions in `δ`. These estimates control
the low and high zero terms after the averaging scale is substituted. -/
theorem scale_power_bounds {x δ : ℝ} (hx : 0 < x) (hδ : 0 ≤ δ) (hu : δ ≤ 1 / 2) :
    Real.sqrt (x + x * δ) ≤ Real.sqrt x * (1 + δ / 2) ∧
      (x + x * δ) ^ (3 / 2 : ℝ) ≤ x ^ (3 / 2 : ℝ) * (1 + 2 * δ) := by
  have hp : 0 < 1 + δ := by linarith only [hδ]
  have hs : Real.sqrt (1 + δ) ≤ 1 + δ / 2 := by
    have hsq := Real.sq_sqrt hp.le
    have hn := Real.sqrt_nonneg (1 + δ)
    nlinarith only [hsq, hn, sq_nonneg δ]
  have hr := Real.rpow_add hp (1 : ℝ) (1 / 2 : ℝ)
  have he : (1 + δ) ^ (3 / 2 : ℝ) = (1 + δ) * Real.sqrt (1 + δ) := by
    convert hr using 1
    · norm_num only
    · rw [Real.rpow_one, Real.sqrt_eq_rpow]
  have hpow : (1 + δ) ^ (3 / 2 : ℝ) ≤ 1 + 2 * δ := by
    rw [he]
    have hm := mul_le_mul_of_nonneg_left hs hp.le
    have hd := mul_nonneg hδ (show 0 ≤ 1 - δ by linarith only [hu])
    nlinarith only [hm, hd]
  have hfact : x + x * δ = x * (1 + δ) := by ring
  rw [hfact, Real.sqrt_mul hx.le, Real.mul_rpow hx.le hp.le]
  exact
    ⟨mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg x),
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hx.le _)⟩

/-- Above 43, a coarse exponential lower bound suffices for the width and
cutoff conditions. Split the exponential at 20 and use `exp 1 > 2`. -/
theorem exp_half_lower {L : ℝ} (hL : 43 ≤ L) : 1000 * L ≤ Real.exp (L / 2) := by
  have he20 : (1048576 : ℝ) ≤ Real.exp 20 := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 by norm_num only) Real.exp_one_gt_two.le 20
    rw [← Real.exp_nat_mul] at h
    norm_num only at h ⊢
    exact h
  have he := Real.add_one_le_exp (L / 2 - 20)
  have hm := mul_le_mul he20 he (by linarith only [hL]) (Real.exp_pos 20).le
  have hexp : Real.exp (L / 2) = Real.exp 20 * Real.exp (L / 2 - 20) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  nlinarith only [hm, hL]

/-- For `L ≥ 43`, the chosen width is positive, the lower averaging endpoint
exceeds one, and the zero cutoff is at least 1000. The exponential lower
bound supplies all three conditions without finite zero data. -/
theorem scale43_conditions {L : ℝ} (hL : 43 ≤ L) :
    0 < Real.exp (L / 2) * L / Real.pi ∧
      1 < Real.exp L - Real.exp (L / 2) * L / Real.pi ∧
      1000 ≤ 2 * Real.pi * Real.exp (L / 2) / L := by
  have he := exp_half_lower hL
  have hL0 : 0 < L := by linarith only [hL]
  have hp := Real.pi_pos
  have he0 := Real.exp_pos (L / 2)
  have hs : Real.exp L = Real.exp (L / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hh : 0 < Real.exp (L / 2) * L / Real.pi := div_pos (mul_pos he0 hL0) hp
  have hhalf : Real.exp (L / 2) * L / Real.pi ≤ Real.exp L / 2 := by
    rw [hs, div_le_div_iff₀ hp (by norm_num only : (0 : ℝ) < 2)]
    have hm := mul_le_mul_of_nonneg_left he he0.le
    nlinarith only [hm, hL, hp, Real.pi_gt_three, he0]
  have hx : 1 < Real.exp L - Real.exp (L / 2) * L / Real.pi := by
    have he1 : 1000 ≤ Real.exp (L / 2) := by nlinarith only [he, hL]
    have hh2 := sq_nonneg (Real.exp (L / 2) - 1)
    rw [hs] at hhalf ⊢
    nlinarith only [hhalf, he1, hh2]
  have hT : 1000 ≤ 2 * Real.pi * Real.exp (L / 2) / L := by
    apply (le_div_iff₀ hL0).2
    have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * Real.pi by linarith only [hp])
    nlinarith only [hm, hL, hp, Real.pi_gt_three]
  exact ⟨hh, hx, hT⟩

/-- For `L ≥ 43`, apply the square-root and three-halves-power bounds to
the selected averaging width. The dimensionless width is at most one half. -/
theorem scale43_power_bounds {L : ℝ} (hL : 43 ≤ L) :
    let δ := L / (Real.pi * Real.exp (L / 2))
    Real.sqrt (Real.exp L + Real.exp (L / 2) * L / Real.pi) ≤ Real.exp (L / 2) * (1 + δ / 2) ∧
      (Real.exp L + Real.exp (L / 2) * L / Real.pi) ^ (3 / 2 : ℝ) ≤
        Real.exp L ^ (3 / 2 : ℝ) * (1 + 2 * δ) := by
  dsimp only
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hp := Real.pi_pos
  have he := Real.exp_pos (L / 2)
  have hd : 0 ≤ L / (Real.pi * Real.exp (L / 2)) := div_nonneg hL0 (mul_nonneg hp.le he.le)
  have hu : L / (Real.pi * Real.exp (L / 2)) ≤ 1 / 2 := by
    apply (div_le_iff₀ (mul_pos hp he)).2
    have hexp := exp_half_lower hL
    nlinarith only [hL, hexp, hp, Real.pi_gt_three]
  have hs : Real.exp L = Real.exp (L / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hw : Real.exp L * (L / (Real.pi * Real.exp (L / 2))) = Real.exp (L / 2) * L / Real.pi := by
    rw [hs]
    field_simp
  have hsqrt : Real.sqrt (Real.exp L) = Real.exp (L / 2) := by
    rw [hs, Real.sqrt_sq_eq_abs, abs_of_pos he]
  have h := scale_power_bounds (Real.exp_pos L) hd hu
  rw [hw, hsqrt] at h
  exact h

/-- Under RH and the stated Rosser-type zero count, substitute the width
`exp (L/2) L / π` and cutoff `2π exp (L/2) / L` into the Chebyshev error
bound for every `L ≥ 43`. The zero-count estimate remains an assumption. -/
theorem psi_error_scale43 (hRH : RiemannHypothesis) {L : ℝ} (hL : 43 ≤ L)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t)) :
    |Chebyshev.psi (Real.exp L) - Real.exp L| ≤
      (Real.exp (L / 2) * L / Real.pi) / 2 + Real.log (2 * Real.pi) +
        Real.sqrt (Real.exp L + Real.exp (L / 2) * L / Real.pi) *
          ((Real.log ((2 * Real.pi * Real.exp (L / 2) / L) / (2 * Real.pi))) ^ 2 / (2 * Real.pi) +
            1) +
        ((Real.exp L + Real.exp (L / 2) * L / Real.pi) ^ (3 / 2 : ℝ) + Real.exp L ^ (3 / 2 : ℝ)) /
            (Real.exp (L / 2) * L / Real.pi) *
          (Real.log (2 * Real.pi * Real.exp (L / 2) / L) /
            (Real.pi * (2 * Real.pi * Real.exp (L / 2) / L))) +
        1 / (Real.exp (L / 2) * L / Real.pi) := by
  obtain ⟨hh, hx, hT⟩ := scale43_conditions hL
  exact psi_error_of_rosser hRH hT hh hx hQ

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
