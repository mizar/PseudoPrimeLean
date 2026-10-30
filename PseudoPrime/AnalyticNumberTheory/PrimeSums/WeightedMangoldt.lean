/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.UnconditionalWeightedBounds
public import PseudoPrime.Analysis.MellinLogarithmicCutoff

/-! # Unconditional fourth-order weighted prime-sum error -/

public section

namespace PseudoPrime.AnalyticNumberTheory.PrimeSums

/-- There is a nonnegative constant B such that the actual logarithmically weighted
Mangoldt sum has error at most B*x/log(x)^4 for all sufficiently large x, unconditionally.
Choose height (log x)^8 in the proved cutoff estimate and absorb its three errors.
This is the smoothed arithmetic input for recovering second-order Chebyshev psi. -/
theorem exists_logWeighted_fourth_order :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ x : ℝ in Filter.atTop,
      |Arithmetic.logWeightedMangoldtSum x - x| ≤
        B * x / Real.log x ^ 4 := by
  obtain ⟨c, C, M, A, hc, hC, hM, hA, hb⟩ := RiemannZeta.exists_logWeighted_cutoff_bound
  refine ⟨C + M + 1, by linarith only [hC, hM], ?_⟩
  have hs := Real.tendsto_log_atTop.eventually (Analysis.eventually_log_cube_le_linear hc)
  have ha := Analysis.eventually_log_correction_le hA
  filter_upwards [hs, ha, Real.tendsto_log_atTop.eventually
    (Filter.eventually_ge_atTop (2 : ℝ)), Filter.eventually_gt_atTop (1 : ℝ)]
    with x hs ha hl hx
  have hy : 0 < Real.log x := (by norm_num only : (0 : ℝ) < 2).trans_le hl
  have hT : 0 < Real.log x ^ 8 := pow_pos hy 8
  have h := hb x (Real.log x ^ 8) hx hT
  have hlo := mul_le_mul_of_nonneg_left
    (Analysis.rpow_cutoff_le_log_fourth (zero_lt_one.trans hx) hl hs) hC
  rw [Analysis.eighth_power_tail_eq hy] at h
  have he : M * x * (1 / Real.log x ^ 4) = M * (x / Real.log x ^ 4) := by ring
  rw [he] at h
  calc
    _ ≤ C * (x / Real.log x ^ 4) + M * (x / Real.log x ^ 4) + x / Real.log x ^ 4 :=
      h.trans (add_le_add (add_le_add hlo le_rfl) ha)
    _ = _ := by ring

end PseudoPrime.AnalyticNumberTheory.PrimeSums
