/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPolePrincipalLower

/-! # The full support of the fourth-pole principal weight -/

public section

namespace PseudoPrime.LLS.PaperStatements

/-- The actual kernel weight vanishes strictly beyond its positive support. -/
theorem fourPoleKernelWeight_zero_of_lt {u : ℝ} (hu : Real.exp (28 / 25 : ℝ) < u) :
    fourPoleKernelWeight u = 0 := by
  have hp := (Real.exp_pos (28 / 25 : ℝ)).trans hu
  change
    ((rationalPoleMellinKernel 2 (13 / 25) (14 / 25) (by norm_num only) (by norm_num only)
                (by norm_num only)).transform
            u).re /
        Real.sqrt u =
      0
  rw [rationalPole_transform _ _ _ _ hp, Complex.ofReal_re,
    Analysis.rationalPoleProfile_eq_zero 2 (13 / 25) (14 / 25)
      (by
        norm_num only at hu ⊢; exact hu),
    zero_div]

/-- The logarithmic coordinate vanishes at the exact upper support endpoint. -/
theorem fourPoleCoord_support : fourPoleCoord (Real.exp (28 / 25 : ℝ)) = 0 := by
  dsimp only [fourPoleCoord]
  rw [Real.log_exp]
  norm_num only

/-- At the upper support endpoint, the actual weight has derivative zero.
Join the auxiliary derivative on the left to the zero function on the right. -/
theorem fourPoleKernelWeight_support_deriv :
    HasDerivAt fourPoleKernelWeight 0 (Real.exp (28 / 25 : ℝ)) := by
  let b := Real.exp (28 / 25 : ℝ)
  have hb : 0 < b := Real.exp_pos _
  have hv : fourPoleCoord b = 0 := fourPoleCoord_support
  have hl : Real.log b = 28 / 25 := Real.log_exp _
  have hval : fourPoleKernelWeight b = 0 := by
    rw [show fourPoleKernelWeight b = fourPoleWeight b from fourPoleKernelWeight_eq hb hl.le]
    dsimp only [fourPoleWeight]
    rw [hv, zero_pow (by norm_num only), zero_mul, zero_div]
  have hd : fourPoleWeightDeriv b = 0 := by
    dsimp only [fourPoleWeightDeriv]
    rw [hv]
    norm_num only [zero_pow, mul_zero, sub_zero]
  have hleft : HasDerivWithinAt fourPoleKernelWeight 0 (Set.Ioc 0 b) b := by
    have h := (fourPoleWeight_hasDerivAt hb).hasDerivWithinAt (s := Set.Ioc 0 b)
    rw [hd] at h
    apply h.congr
    · intro u hu
      exact fourPoleKernelWeight_eq hu.1 ((Real.log_le_log hu.1 hu.2).trans hl.le)
    · exact fourPoleKernelWeight_eq hb hl.le
  have hright : HasDerivWithinAt fourPoleKernelWeight 0 (Set.Ici b) b := by
    apply (hasDerivAt_const b (0 : ℝ)).hasDerivWithinAt.congr
    · intro u hu
      rcases eq_or_lt_of_le (show b ≤ u from hu) with he | he
      · rw [← he, hval]
      · exact fourPoleKernelWeight_zero_of_lt he
    · exact hval
  apply (hleft.union hright).hasDerivAt
  apply Filter.mem_of_superset (Ioi_mem_nhds hb)
  intro u hu
  by_cases hut : u ≤ b
  · exact Or.inl ⟨hu, hut⟩
  · exact Or.inr (le_of_lt (lt_of_not_ge hut))

/-- For every positive argument, the derivative is the auxiliary derivative inside
the support and zero outside, including the matching zero at the endpoint. -/
theorem fourPoleKernelWeight_global_deriv {u : ℝ} (hu : 0 < u) :
    HasDerivAt fourPoleKernelWeight (if Real.log u ≤ 28 / 25 then fourPoleWeightDeriv u else 0)
      u := by
  by_cases hl : Real.log u < 28 / 25
  · rw [ite_eq_left hl.le]
    exact fourPoleKernelWeight_hasDerivAt hu hl
  · by_cases he : Real.log u = 28 / 25
    · have hue : u = Real.exp (28 / 25 : ℝ) := by rw [← he, Real.exp_log hu]
      subst u
      rw [Real.log_exp, ite_eq_left le_rfl]
      have hd : fourPoleWeightDeriv (Real.exp (28 / 25 : ℝ)) = 0 := by
        dsimp only [fourPoleWeightDeriv]
        rw [fourPoleCoord_support]
        norm_num only [zero_pow, mul_zero, sub_zero]
      rw [hd]
      exact fourPoleKernelWeight_support_deriv
    · have hgt : 28 / 25 < Real.log u := lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm he)
      rw [ite_eq_right (not_le_of_gt hgt)]
      have hb : Real.exp (28 / 25 : ℝ) < u := (Real.lt_log_iff_exp_lt hu).mp hgt
      apply (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds hb] with t ht
      exact fourPoleKernelWeight_zero_of_lt ht

/-- The scaled actual weight has the chain-rule derivative throughout the positive axis. -/
theorem fourScaledWeight_global_deriv {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    HasDerivAt (fourScaledWeight x)
      ((if Real.log (t / x) ≤ 28 / 25 then fourPoleWeightDeriv (t / x) else 0) / (x * Real.sqrt x))
      t := by
  have h :=
    ((fourPoleKernelWeight_global_deriv (div_pos ht hx)).comp t
          ((hasDerivAt_id t).div_const x)).div_const
      (Real.sqrt x)
  convert h using 1
  · rfl
  · ring

/-- At every positive scale, the derivative is integrable on any interval `[2,y]`.
The continuous auxiliary derivative bounds the measurable actual derivative. -/
theorem fourScaledWeight_deriv_integrableOn {x y : ℝ} (hx : 0 < x) :
    MeasureTheory.IntegrableOn (deriv (fourScaledWeight x)) (Set.Icc 2 y) := by
  have hc :
    ContinuousOn (fun t : ℝ ↦ fourPoleWeightDeriv (t / x) / (x * Real.sqrt x)) (Set.Icc 2 y) := by
    intro t ht
    have ht0 : 0 < t := (by norm_num only : (0 : ℝ) < 2).trans_le ht.1
    have h :=
      ContinuousAt.comp (g := fourPoleWeightDeriv) (f := fun t : ℝ ↦ t / x)
        (fourPoleWeightDeriv_continuousAt (div_pos ht0 hx)) (continuous_id.div_const x).continuousAt
    exact (h.div_const (x * Real.sqrt x)).continuousWithinAt
  apply MeasureTheory.Integrable.mono' hc.norm.integrableOn_Icc (aestronglyMeasurable_deriv _ _)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
  rw [(fourScaledWeight_global_deriv hx ((by norm_num only : (0 : ℝ) < 2).trans_le ht.1)).deriv]
  split_ifs with h
  · exact le_rfl
  · simp only [zero_div, norm_zero]
    exact norm_nonneg _

/-- Under RH, quantitative Abel summation holds at every cutoff at least two,
including cutoffs beyond the unit scale. -/
theorem fourScaledWeight_full_abel (hRH : RiemannHypothesis) {x y : ℝ} (hx : 0 < x) (hy : 2 ≤ y) :
    |(∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * fourScaledWeight x n) -
          (∫ t : ℝ in (2 : ℝ)..y, fourScaledWeight x t) -
          2 * fourScaledWeight x 2| ≤
      13 *
        (y ^ (3 / 4 : ℝ) * |fourScaledWeight x y| +
          ∫ t : ℝ in (2 : ℝ)..y, t ^ (3 / 4 : ℝ) * |deriv (fourScaledWeight x) t|) := by
  exact
    mangoldt_weighted_error hy
      (fun t ht ↦
        (fourScaledWeight_global_deriv hx
            ((by norm_num only : (0 : ℝ) < 2).trans_le ht.1)).differentiableAt)
      (fourScaledWeight_deriv_integrableOn hx)
      (fun t ht ↦ LLS.psi_error_le_thirteen hRH (by linarith only [ht.1]))

/-- The full principal series equals its finite sum up to the exact support cutoff.
All terms beyond the cutoff vanish; positive terms match the real scaled weight. -/
theorem fourPole_principal_sum_finite {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, (MellinKernel.summand rationalPoleFourKernel) (1 : DirichletCharacter ℂ 1) x n).re =
      ∑ n ∈ Finset.Ioc 0 ⌊Real.exp (28 / 25 : ℝ) * x⌋₊,
        ArithmeticFunction.vonMangoldt n * fourScaledWeight x n := by
  have hs := MellinKernel.summable_summand rationalPoleFourKernel (1 : DirichletCharacter ℂ 1) hx
  change
    Complex.reCLM
        (∑' n : ℕ, (MellinKernel.summand rationalPoleFourKernel) (1 : DirichletCharacter ℂ 1) x n) =
      _
  rw [Complex.reCLM.map_tsum hs]
  rw [tsum_eq_sum (s := Finset.Ioc 0 ⌊Real.exp (28 / 25 : ℝ) * x⌋₊)
      (fun n hn ↦ by
        change
          ((MellinKernel.summand rationalPoleFourKernel) (1 : DirichletCharacter ℂ 1) x n).re = 0
        by_cases hn0 : n = 0
        · subst n
          simp only [MellinKernel.summand, ite_true, Complex.zero_re]
        · have hlt : ⌊Real.exp (28 / 25 : ℝ) * x⌋₊ < n := by
            by_contra h
            exact hn (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0, le_of_not_gt h⟩)
          have hnr : Real.exp (28 / 25 : ℝ) * x < (n : ℝ) := Nat.lt_of_floor_lt hlt
          rw [fourPole_principal_summand_eq hx hn0]
          dsimp only [fourScaledWeight]
          rw [fourPoleKernelWeight_zero_of_lt ((lt_div_iff₀ hx).mpr hnr), zero_div, mul_zero])]
  apply Finset.sum_congr rfl
  intro n hn
  exact fourPole_principal_summand_eq hx (Nat.ne_of_gt (Finset.mem_Ioc.mp hn).1)

/-- At positive scale and argument, the scaled actual weight is bounded by `10/sqrt x`.
The interior bound and exterior vanishing cover the entire positive axis. -/
theorem fourScaledWeight_global_bound {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    |fourScaledWeight x t| ≤ 10 / Real.sqrt x := by
  by_cases hl : Real.log (t / x) ≤ 28 / 25
  · have hb := fourPoleKernelWeight_bounds (div_pos ht hx) hl
    dsimp only [fourScaledWeight]
    rw [abs_div, abs_of_nonneg hb.1, abs_of_nonneg (Real.sqrt_nonneg x)]
    exact div_le_div_of_nonneg_right hb.2 (Real.sqrt_nonneg x)
  · have hb : Real.exp (28 / 25 : ℝ) < t / x :=
      (Real.lt_log_iff_exp_lt (div_pos ht hx)).mp (lt_of_not_ge hl)
    dsimp only [fourScaledWeight]
    rw [fourPoleKernelWeight_zero_of_lt hb, zero_div, abs_zero]
    exact div_nonneg (by norm_num only) (Real.sqrt_nonneg x)

/-- At positive scale, the scaled actual weight is integrable on every interval `[0,y]`
with positive endpoint, using its global bound and positive-axis differentiability. -/
theorem fourScaledWeight_global_integrable {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    IntervalIntegrable (fourScaledWeight x) MeasureTheory.volume 0 y := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hy.le).mpr
  have hc : ContinuousOn (fourScaledWeight x) (Set.Ioc 0 y) := fun t ht ↦
    (fourScaledWeight_global_deriv hx ht.1).continuousAt.continuousWithinAt
  apply
    MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top
      (hc.aestronglyMeasurable measurableSet_Ioc) (10 / Real.sqrt x)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs]
  exact fourScaledWeight_global_bound hx ht.1

/-- Under RH and for scales at least two, the full principal series differs from its
full-support integral by at most thirteen times the weighted derivative integral plus
`40/sqrt x`. Exact support truncation and low-endpoint corrections make every term explicit;
the weighted integral still needs its numerical variation bound. -/
theorem fourPole_full_principal_error (hRH : RiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    |(∑' n : ℕ, (MellinKernel.summand rationalPoleFourKernel) (1 : DirichletCharacter ℂ 1) x n).re -
          (∫ t : ℝ in (0 : ℝ)..(Real.exp (28 / 25 : ℝ) * x), fourScaledWeight x t)| ≤
      13 *
          (∫ t : ℝ in (2 : ℝ)..(Real.exp (28 / 25 : ℝ) * x),
            t ^ (3 / 4 : ℝ) * |deriv (fourScaledWeight x) t|) +
        40 / Real.sqrt x := by
  let b := Real.exp (28 / 25 : ℝ)
  let y := b * x
  have hx0 : 0 < x := (by norm_num only : (0 : ℝ) < 2).trans_le hx
  have hb : 1 ≤ b := Real.one_le_exp_iff.mpr (by norm_num only)
  have hxy : x ≤ y := le_mul_of_one_le_left hx0.le hb
  have hy : 2 ≤ y := hx.trans hxy
  have hval : fourScaledWeight x y = 0 := by
    dsimp only [fourScaledWeight, y]
    rw [mul_div_cancel_right₀ b hx0.ne']
    have hk : fourPoleKernelWeight b = fourPoleWeight b :=
      fourPoleKernelWeight_eq (Real.exp_pos _) (by rw [Real.log_exp])
    rw [hk]
    dsimp only [fourPoleWeight]
    rw [show fourPoleCoord b = 0 from fourPoleCoord_support, zero_pow (by norm_num only), zero_mul,
      zero_div, zero_div]
  have ha := fourScaledWeight_full_abel hRH hx0 hy
  rw [hval, abs_zero, mul_zero, zero_add] at ha
  have h0 := fourScaledWeight_global_integrable hx0 ((by norm_num only : (0 : ℝ) < 2).trans_le hy)
  have h02 : IntervalIntegrable (fourScaledWeight x) MeasureTheory.volume 0 2 :=
    h0.mono_set
      (by
        rw [Set.uIcc_of_le (by linarith only [hy] : (0 : ℝ) ≤ y),
          Set.uIcc_of_le (by norm_num only : (0 : ℝ) ≤ 2)]
        exact Set.Icc_subset_Icc_right hy)
  have h2 : IntervalIntegrable (fourScaledWeight x) MeasureTheory.volume 2 y :=
    h0.mono_set
      (by
        rw [Set.uIcc_of_le (by linarith only [hy] : (0 : ℝ) ≤ y), Set.uIcc_of_le hy]
        exact Set.Icc_subset_Icc_left (by norm_num only))
  have hs := intervalIntegral.integral_add_adjacent_intervals h02 h2
  have he := fourPole_principal_sum_finite hx0
  have htri :=
    abs_sub
      ((∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * fourScaledWeight x n) -
        (∫ t : ℝ in (2 : ℝ)..y, fourScaledWeight x t) -
        2 * fourScaledWeight x 2)
      ((∫ t : ℝ in (0 : ℝ)..2, fourScaledWeight x t) - 2 * fourScaledWeight x 2)
  have hcorr := abs_sub (∫ t : ℝ in (0 : ℝ)..2, fourScaledWeight x t) (2 * fourScaledWeight x 2)
  have hl := fourScaledWeight_low_integral hx
  have hend := fourScaledWeight_lower_endpoint hx
  have hfinal :
    |(∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * fourScaledWeight x n) -
          (∫ t : ℝ in (0 : ℝ)..y, fourScaledWeight x t)| ≤
      13 * (∫ t : ℝ in (2 : ℝ)..y, t ^ (3 / 4 : ℝ) * |deriv (fourScaledWeight x) t|) +
        20 / Real.sqrt x +
        20 / Real.sqrt x := by
    have hid :
      (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * fourScaledWeight x n) -
          (∫ t : ℝ in (2 : ℝ)..y, fourScaledWeight x t) -
          2 * fourScaledWeight x 2 -
          ((∫ t : ℝ in (0 : ℝ)..2, fourScaledWeight x t) - 2 * fourScaledWeight x 2) =
        (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * fourScaledWeight x n) -
          (∫ t : ℝ in (0 : ℝ)..y, fourScaledWeight x t) := by
      linarith only [hs]
    rw [hid] at htri
    linarith only [htri, hcorr, ha, hl, hend]
  rw [he]
  convert hfinal using 1
  ring

end PseudoPrime.LLS.PaperStatements
