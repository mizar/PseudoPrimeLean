/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredTailSign
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028SharpPrincipal
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleOneSided

/-! # Combined principal-kernel variation -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Combining the finite and full principal sums before taking absolute values
reduces the unweighted variation coefficient from five to three. The positive
tail equals minus the unit derivative and partially cancels the boundary term. -/
theorem quarter_combined_variation_unweighted :
    3 * (∫ u : ℝ in (0 : ℝ)..1, |refinedSecondDensity u|) +
        (∫ u : ℝ in (1 : ℝ)..Real.exp (21 / 8 : ℝ), |refinedSecondDensity u|) +
        4 * |refinedWeightDeriv 1| ≤
      3 * ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) + 2 * |refinedWeightDeriv 1| := by
  have h0 : (0 : ℝ) ≤ Real.exp (21 / 8 : ℝ) := (Real.exp_pos _).le
  have hi :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ |refinedSecondDensity u|)
      (Set.Ioc 0 (Real.exp (21 / 8 : ℝ))) := by
    change
      MeasureTheory.Integrable (fun u : ℝ ↦ |refinedSecondDensity u|)
        (MeasureTheory.volume.restrict (Set.Ioc 0 (Real.exp (21 / 8 : ℝ))))
    simpa only [Real.norm_eq_abs] using refined_second_integrable.norm
  have hs :=
    quarter_integral_split_one (fun u ↦ |refinedSecondDensity u|)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le h0).mpr hi)
  have hb := target028_unweighted_variation_bound
  have ht := quarter_abs_density_tail
  rw [abs_of_nonpos refined_unit_deriv_nonpos]
  linarith only [hs, hb, ht]

/-- The square-root-weighted combined variation gains twice the certified
positive tail. This estimate retains the boundary derivative contribution. -/
theorem quarter_combined_variation_sqrt :
    3 * (∫ u : ℝ in (0 : ℝ)..1, Real.sqrt u * |refinedSecondDensity u|) +
        (∫ u : ℝ in (1 : ℝ)..Real.exp (21 / 8 : ℝ), Real.sqrt u * |refinedSecondDensity u|) +
        4 * |refinedWeightDeriv 1| ≤
      3 * ((203 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5) - 2 * (179 / 1000 : ℝ) +
        4 * |refinedWeightDeriv 1| := by
  have h0 : (0 : ℝ) ≤ Real.exp (21 / 8 : ℝ) := (Real.exp_pos _).le
  have hs :=
    quarter_integral_split_one (fun u ↦ Real.sqrt u * |refinedSecondDensity u|)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le h0).mpr refined_second_variation.1)
  have hb := target028_sqrt_variation_bound
  have ht := quarter_sqrt_abs_density_tail_lower
  linarith only [hs, hb, ht]

end PseudoPrime.PrimeTestBounds.MillerRabin
