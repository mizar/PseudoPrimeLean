/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPolePrincipalSupport
public import PseudoPrime.Analysis.ScaledLogMoments

/-! # Exact full-support principal moments and variation majorant -/

public section

namespace PseudoPrime.LLS.PaperStatements

/-- The full-support weighted derivative majorant integrates to
`(3625000/5250987) exp(7/25)`, by its second and third logarithmic moments. -/
theorem fourPole_full_majorant_integral :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ u ^ (3 / 4 : ℝ) * fourPoleVariationMajorant u)
        (Set.Ioc 0 (Real.exp (28 / 25 : ℝ))) ∧
      (∫ u : ℝ in Set.Ioc 0 (Real.exp (28 / 25 : ℝ)),
          u ^ (3 / 4 : ℝ) * fourPoleVariationMajorant u) =
        (3625000 / 5250987 : ℝ) * Real.exp (7 / 25) := by
  have h2 := Analysis.scaled_log_moment 2 (28 / 25) (s := 63 / 52) (by norm_num only)
  have h3 := Analysis.scaled_log_moment 3 (28 / 25) (s := 63 / 52) (by norm_num only)
  norm_num only at h2 h3
  rw [intervalIntegral.integral_of_le (Real.exp_pos _).le] at h2 h3
  have hi :=
    ((h3.1.const_mul ((6 / 13 : ℝ) * (25 / 26 : ℝ) ^ 3)).add
          (h2.1.const_mul ((75 / 26 : ℝ) * (25 / 26 : ℝ) ^ 2))).const_mul
      (Real.exp (-(14 / 13 : ℝ)) / 6)
  have hEq :
    (fun u : ℝ ↦
        u ^ (3 / 4 : ℝ) *
          fourPoleVariationMajorant
            u) =ᵐ[MeasureTheory.volume.restrict (Set.Ioc 0 (Real.exp (28 / 25 : ℝ)))]
      (fun u : ℝ ↦
        (Real.exp (-(14 / 13 : ℝ)) / 6) *
          ((6 / 13 : ℝ) * (25 / 26 : ℝ) ^ 3 * (u ^ (11 / 52 : ℝ) * (28 / 25 - Real.log u) ^ 3) +
            (75 / 26 : ℝ) * (25 / 26 : ℝ) ^ 2 *
              (u ^ (11 / 52 : ℝ) * (28 / 25 - Real.log u) ^ 2))) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    exact fourPoleVariationMajorant_eq hu.1
  refine ⟨hi.congr hEq.symm, ?_⟩
  rw [MeasureTheory.integral_congr_ae hEq, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add (h3.1.const_mul ((6 / 13 : ℝ) * (25 / 26 : ℝ) ^ 3))
      (h2.1.const_mul ((75 / 26 : ℝ) * (25 / 26 : ℝ) ^ 2)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, h3.2, h2.2]
  norm_num only [Nat.factorial, Nat.cast_ofNat]
  calc
    _ = (3625000 / 5250987 : ℝ) * (Real.exp (-(14 / 13 : ℝ)) * Real.exp (441 / 325)) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      norm_num only

/-- The full-support weighted majorant integral is below one.
Use `exp(7/25) ≤ 25/18` and an exact rational comparison. -/
theorem fourPole_full_majorant_lt_one :
    (∫ u : ℝ in Set.Ioc 0 (Real.exp (28 / 25 : ℝ)), u ^ (3 / 4 : ℝ) * fourPoleVariationMajorant u) <
      1 := by
  rw [fourPole_full_majorant_integral.2]
  have he :=
    Real.exp_bound_div_one_sub_of_interval (by norm_num only : (0 : ℝ) ≤ 7 / 25)
      (by norm_num only : (7 / 25 : ℝ) < 1)
  have hm := mul_le_mul_of_nonneg_left he (by norm_num only : (0 : ℝ) ≤ 3625000 / 5250987)
  norm_num only at hm
  exact hm.trans_lt (by norm_num only)

/-- The full-support principal integral equals the existing full Mellin weight moment.
The exterior zero values identify the finite interval with the positive-axis integral. -/
theorem fourPole_full_weight_integral :
    (∫ u : ℝ in (0 : ℝ)..Real.exp (28 / 25 : ℝ), fourPoleKernelWeight u) =
      (2 * (13 / 25 : ℝ) * Real.exp (14 / 25) / (1 + 13 / 25) ^ 4) := by
  have hs :=
    MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (μ := MeasureTheory.volume) (f :=
      fourPoleKernelWeight) measurableSet_Ioi.nullMeasurableSet
      (show Set.Ioc (0 : ℝ) (Real.exp (28 / 25 : ℝ)) ⊆ Set.Ioi 0 from fun u hu ↦ hu.1)
      (Filter.Eventually.of_forall
        (fun u hu ↦ by
          have hb : Real.exp (28 / 25 : ℝ) < u := by
            by_contra hn
            exact hu.2 ⟨hu.1, le_of_not_gt hn⟩
          exact fourPoleKernelWeight_zero_of_lt hb))
  rw [intervalIntegral.integral_of_le (Real.exp_pos _).le, ← hs]
  exact rationalPole_total_weight 2 (by norm_num only) (by norm_num only) (by norm_num only)

/-- The scaled full-support integral is `sqrt x` times the exact full principal moment. -/
theorem fourScaledWeight_full_integral {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ in (0 : ℝ)..(Real.exp (28 / 25 : ℝ) * x), fourScaledWeight x t) =
      Real.sqrt x * (2 * (13 / 25 : ℝ) * Real.exp (14 / 25) / (1 + 13 / 25) ^ 4) := by
  dsimp only [fourScaledWeight]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_div fourPoleKernelWeight hx.ne',
    zero_div, mul_div_cancel_right₀ _ hx.ne', fourPole_full_weight_integral]
  simp only [smul_eq_mul]
  have hs := Real.sq_sqrt hx.le
  apply (div_eq_iff (Real.sqrt_pos.mpr hx).ne').mpr
  calc
    _ = Real.sqrt x ^ 2 * (2 * (13 / 25 : ℝ) * Real.exp (14 / 25) / (1 + 13 / 25) ^ 4) := by rw [hs]
    _ = _ := by ring

end PseudoPrime.LLS.PaperStatements
