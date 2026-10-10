/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelBounds
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Continuity and local integrability of inverse Mellin kernels

The inverse transform is continuous on the positive axis by dominated convergence.
Its real part divided by the square root is integrable up to zero, using the kernel mass.
These properties supply the weight for the truncated principal-character comparison.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- Every admissible kernel has a continuous inverse Mellin transform on positive
arguments. On the imaginary line, the Mellin power has norm one; the integrable kernel
therefore dominates the parameter-dependent integral. This supports cutoff approximation. -/
theorem continuousOn_transform (K : MellinKernel) : ContinuousOn K.transform (Set.Ioi 0) := by
  have hc : (-1 / 2 : ℝ) < 0 := by norm_num only
  have hc' : (0 : ℝ) ≤ 1 / 2 + K.delta := by linarith only [K.delta_pos]
  have hi := integrable_line K hc hc'
  have hcont :
    ContinuousOn
      (fun u : ℝ ↦
        ∫ t : ℝ, K.function ((0 : ℂ) + Complex.I * t) * (u : ℂ) ^ (-((0 : ℂ) + Complex.I * t)))
      (Set.Ioi 0) := by
    apply
      MeasureTheory.continuousOn_of_dominated (bound := fun t : ℝ ↦
        ‖K.function ((0 : ℂ) + Complex.I * t)‖)
    · intro u hu
      exact (K.mellin_integrable 0 u hc hc' hu).aestronglyMeasurable
    · intro u hu
      apply MeasureTheory.ae_of_all
      intro t
      have hp := norm_mellin_power (c := 0) (t := t) hu
      simp only [Complex.ofReal_zero, neg_zero, Real.rpow_zero] at hp
      rw [norm_mul, hp, mul_one]
    · exact hi.norm
    · apply MeasureTheory.ae_of_all
      intro t u hu
      exact
        (continuousAt_const.mul
            (Complex.continuousAt_ofReal_cpow_const u (-((0 : ℂ) + Complex.I * t))
              (Or.inr (ne_of_gt hu)))).continuousWithinAt
  exact continuousOn_const.mul hcont

/-- The real inverse transform divided by the square root is continuous on the positive
axis. Combine transform continuity with the nonvanishing square root there.
This is the real weight used in the truncated Mangoldt comparison. -/
theorem continuousOn_weight (K : MellinKernel) :
    ContinuousOn (fun u : ℝ ↦ (K.transform u).re / Real.sqrt u) (Set.Ioi 0) := by
  apply
    (Complex.continuous_re.comp_continuousOn (continuousOn_transform K)).div
      Real.continuous_sqrt.continuousOn
  intro u hu
  exact ne_of_gt (Real.sqrt_pos.mpr hu)

/-- For every positive upper endpoint, the real comparison weight is integrable between
zero and that endpoint. Nonnegativity and the mass bound dominate it by
`K.mass * u^(-1/2)`, whose singularity is integrable. This permits removal of a cutoff at zero. -/
theorem integrableOn_weight (K : MellinKernel) {b : ℝ} (hb : 0 < b) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ (K.transform u).re / Real.sqrt u) (Set.Ioo 0 b) := by
  have hi :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hb).mpr (by norm_num only : (-1 : ℝ) < -(1 / 2 : ℝ))
  apply (hi.const_mul K.mass).mono'
  · exact ((continuousOn_weight K).mono (fun _ hu ↦ hu.1)).aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with u hu
    have hn : 0 ≤ (K.transform u).re / Real.sqrt u :=
      div_nonneg (K.mellin_nonneg u hu.1) (Real.sqrt_nonneg u)
    rw [Real.norm_eq_abs]
    apply (abs_of_nonneg hn).le.trans
    have h := (Complex.re_le_norm (K.transform u)).trans (norm_transform_le_mass K hu.1)
    have hd := div_le_div_of_nonneg_right h (Real.sqrt_nonneg u)
    rw [Real.rpow_neg (le_of_lt hu.1), ← Real.sqrt_eq_rpow]
    exact hd

/-- The comparison-weight integral between zero and a positive endpoint is at most
twice the kernel mass times the square root of the endpoint. Integrate the inverse-square-root
majorant explicitly. This quantifies the part discarded near zero in Proposition 6.1. -/
theorem integral_weight_le (K : MellinKernel) {b : ℝ} (hb : 0 < b) :
    (∫ u in Set.Ioo 0 b, (K.transform u).re / Real.sqrt u) ≤ 2 * K.mass * Real.sqrt b := by
  have hr : (-1 : ℝ) < -(1 / 2 : ℝ) := by norm_num only
  have hi := (intervalIntegral.integrableOn_Ioo_rpow_iff hb).mpr hr
  have hbound :=
    MeasureTheory.setIntegral_mono_on (integrableOn_weight K hb) (hi.const_mul K.mass)
      measurableSet_Ioo
      (fun u hu ↦ by
        have h :=
          div_le_div_of_nonneg_right
            ((Complex.re_le_norm (K.transform u)).trans (norm_transform_le_mass K hu.1))
            (Real.sqrt_nonneg u)
        rw [Real.rpow_neg (le_of_lt hu.1), ← Real.sqrt_eq_rpow]
        exact h)
  have hint : (∫ u in Set.Ioo 0 b, u ^ (-(1 / 2 : ℝ))) = 2 * Real.sqrt b := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ←
      intervalIntegral.integral_of_le (le_of_lt hb), integral_rpow (Or.inl hr)]
    have he : -(1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num only
    rw [he, Real.zero_rpow (by norm_num only : (1 / 2 : ℝ) ≠ 0), sub_zero, ← Real.sqrt_eq_rpow]
    ring
  rw [MeasureTheory.integral_const_mul, hint] at hbound
  nlinarith only [hbound]

/-- The integral over a shrinking positive interval tends to zero. Its nonnegativity
and the explicit mass-times-square-root upper bound give the squeeze argument.
This removes the singular endpoint from continuous-weight approximations. -/
theorem tendsto_integral_weight_zero (K : MellinKernel) :
    Filter.Tendsto (fun b : ℝ ↦ ∫ u in Set.Ioo 0 b, (K.transform u).re / Real.sqrt u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  apply squeeze_zero'
  · exact
      Filter.Eventually.of_forall
        (fun b ↦
          MeasureTheory.setIntegral_nonneg measurableSet_Ioo
            (fun u hu ↦ div_nonneg (K.mellin_nonneg u hu.1) (Real.sqrt_nonneg u)))
  · filter_upwards [self_mem_nhdsWithin] with b hb
    exact integral_weight_le K hb
  · have h := (Real.continuous_sqrt.tendsto 0).const_mul (2 * K.mass)
    simpa only [Real.sqrt_zero, mul_zero] using h.mono_left nhdsWithin_le_nhds

/-- For a fixed positive upper endpoint, the weight integral with a positive lower cutoff
converges to the full integral as the cutoff decreases to zero. Split at the cutoff
and use the vanishing initial integral. This supplies the integral side of cutoff removal. -/
theorem tendsto_integral_weight_cutoff (K : MellinKernel) {b : ℝ} (hb : 0 < b) :
    Filter.Tendsto (fun a : ℝ ↦ ∫ u in a..b, (K.transform u).re / Real.sqrt u)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ u in 0..b, (K.transform u).re / Real.sqrt u)) := by
  have ht :=
    (tendsto_const_nhds (x := (∫ u in 0..b, (K.transform u).re / Real.sqrt u))).sub
      (tendsto_integral_weight_zero K)
  have he :
    ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (∫ u in a..b, (K.transform u).re / Real.sqrt u) =
        (∫ u in 0..b, (K.transform u).re / Real.sqrt u) -
          ∫ u in Set.Ioo 0 a, (K.transform u).re / Real.sqrt u := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with a ha hab
    have hi :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (le_of_lt ha)).mpr (integrableOn_weight K ha)
    have hj :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (le_of_lt hab)).mpr
        ((integrableOn_weight K hb).mono_set (fun u hu ↦ ⟨lt_trans ha hu.1, hu.2⟩))
    have h := intervalIntegral.integral_add_adjacent_intervals hi hj
    rw [intervalIntegral.integral_of_le (le_of_lt ha),
      MeasureTheory.integral_Ioc_eq_integral_Ioo] at h
    linarith only [h]
  simpa only [sub_zero] using ht.congr' (he.mono (fun _ h ↦ h.symm))

end PseudoPrime.LLS.PaperStatements.MellinKernel
