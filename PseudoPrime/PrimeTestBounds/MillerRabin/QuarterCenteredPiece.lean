/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCombinedVariation
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleCenteredBound

/-! # Local variation bound for the centered principal integral -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, the centered error on any interval within the kernel support is
bounded by that interval's square-root and unweighted variations. Retaining
local integrals allows the finite and full principal sums to be combined. -/
theorem quarter_centered_piece_bound (hRH : RiemannHypothesis) {x a b : ℝ} (hx : 1 ≤ x) (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ Real.exp (21 / 8 : ℝ)) :
    |∫ u : ℝ in a..b, LLS.clippedShiftError x u * refinedSecondDensity u| ≤
      (1 / 20 : ℝ) * Real.sqrt x * (∫ u : ℝ in a..b, Real.sqrt u * |refinedSecondDensity u|) +
        (21 / 20 : ℝ) * (∫ u : ℝ in a..b, |refinedSecondDensity u|) := by
  let E : ℝ → ℝ := LLS.clippedShiftError x
  let S : Set ℝ := Set.Ioc a b
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hsub : S ⊆ Set.Ioc 0 (Real.exp (21 / 8 : ℝ)) := Set.Ioc_subset_Ioc ha hb
  have hEc : ContinuousOn E (Set.Icc a b) :=
    (LLS.clippedShiftError_continuousOn hx0 b).mono (Set.Icc_subset_Icc ha le_rfl)
  have hQ := refined_second_integrable.mono_set hsub
  have hiE : MeasureTheory.IntegrableOn (fun u ↦ E u * refinedSecondDensity u) S := by
    have hp :=
      MeasureTheory.IntegrableOn.mul_continuousOn_of_subset hQ hEc measurableSet_Ioc isCompact_Icc
        (Set.Ioc_subset_Icc_self : Set.Ioc a b ⊆ _)
    simpa only [S, mul_comm] using hp
  have hiAbs : MeasureTheory.IntegrableOn (fun u : ℝ ↦ |E u * refinedSecondDensity u|) S := by
    change
      MeasureTheory.Integrable (fun u : ℝ ↦ |E u * refinedSecondDensity u|)
        (MeasureTheory.volume.restrict S)
    simpa only [Real.norm_eq_abs] using hiE.norm
  have hiV := refined_second_variation.1.mono_set hsub
  have hiNfull :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ |refinedSecondDensity u|)
      (Set.Ioc 0 (Real.exp (21 / 8 : ℝ))) := by
    change
      MeasureTheory.Integrable (fun u : ℝ ↦ |refinedSecondDensity u|)
        (MeasureTheory.volume.restrict (Set.Ioc 0 (Real.exp (21 / 8 : ℝ))))
    simpa only [Real.norm_eq_abs] using refined_second_integrable.norm
  have hiN := hiNfull.mono_set hsub
  have hn :=
    MeasureTheory.norm_integral_le_integral_norm (f := fun u : ℝ ↦ E u * refinedSecondDensity u)
      (μ := MeasureTheory.volume.restrict S)
  simp only [Real.norm_eq_abs] at hn
  have hm :
    (∫ u : ℝ in S, |E u * refinedSecondDensity u|) ≤
      ∫ u : ℝ in S,
        ((1 / 20 : ℝ) * Real.sqrt x) * (Real.sqrt u * |refinedSecondDensity u|) +
          (21 / 20 : ℝ) * |refinedSecondDensity u| := by
    apply MeasureTheory.integral_mono_ae hiAbs ((hiV.const_mul _).add (hiN.const_mul _))
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    have hu0 : 0 ≤ u := ha.trans hu.1.le
    have he := LLS.clippedShiftError_abs_le hRH hx0 hu0
    rw [Real.sqrt_mul hx0.le] at he
    have h := mul_le_mul_of_nonneg_right he (abs_nonneg (refinedSecondDensity u))
    dsimp only [E, Pi.add_apply]
    rw [abs_mul]
    nlinarith only [h]
  rw [MeasureTheory.integral_add (hiV.const_mul _) (hiN.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hm
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hab]
  exact hn.trans hm

end PseudoPrime.PrimeTestBounds.MillerRabin
