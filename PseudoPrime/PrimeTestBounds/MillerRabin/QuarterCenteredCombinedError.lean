/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredPiece

/-! # Centered error after combining the principal sums -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, combining the finite and full principal integrals first gives
three times the unit-interval variation plus the positive tail. The exact
tail identity and lower bound improve both centered error coefficients. -/
theorem quarter_centered_combined_error (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    -((1 / 20 : ℝ) * Real.sqrt x *
            (3 * ((203 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5) - 2 * (179 / 1000 : ℝ) +
              4 * |refinedWeightDeriv 1|) +
          (21 / 20 : ℝ) *
            (3 * ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) + 2 * |refinedWeightDeriv 1|)) ≤
      4 * (∫ u : ℝ in (0 : ℝ)..1, LLS.clippedShiftError x u * refinedSecondDensity u) -
        (∫ u : ℝ in (0 : ℝ)..Real.exp (21 / 8 : ℝ),
          LLS.clippedShiftError x u * refinedSecondDensity u) -
        4 * refinedWeightDeriv 1 * LLS.clippedShiftError x 1 := by
  let E : ℝ → ℝ := LLS.clippedShiftError x
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have he : (1 : ℝ) ≤ Real.exp (21 / 8 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num only)
  have h0 : (0 : ℝ) ≤ Real.exp (21 / 8 : ℝ) := (Real.exp_pos _).le
  have hEc : ContinuousOn E (Set.Icc 0 (Real.exp (21 / 8 : ℝ))) :=
    LLS.clippedShiftError_continuousOn hx0 _
  have hi :=
    MeasureTheory.IntegrableOn.mul_continuousOn_of_subset refined_second_integrable hEc
      measurableSet_Ioc isCompact_Icc
      (Set.Ioc_subset_Icc_self : Set.Ioc (0 : ℝ) (Real.exp (21 / 8 : ℝ)) ⊆ _)
  have hi' :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ E u * refinedSecondDensity u)
      (Set.Ioc 0 (Real.exp (21 / 8 : ℝ))) := by
    simpa only [mul_comm] using hi
  have hs :=
    quarter_integral_split_one (fun u ↦ E u * refinedSecondDensity u)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le h0).mpr hi')
  have ha :=
    abs_le.mp
      (quarter_centered_piece_bound hRH hx (a := 0) (b := 1) (by norm_num only) (by norm_num only)
        he)
  have hb :=
    abs_le.mp
      (quarter_centered_piece_bound hRH hx (a := 1) (b := Real.exp (21 / 8 : ℝ)) (by norm_num only)
        he le_rfl)
  have hE := LLS.clippedShiftError_abs_le hRH hx0 (show (0 : ℝ) ≤ 1 by norm_num only)
  simp only [mul_one] at hE
  have hd : refinedWeightDeriv 1 * E 1 ≤ |refinedWeightDeriv 1| * (Real.sqrt x / 20 + 21 / 20) := by
    calc
      _ ≤ |refinedWeightDeriv 1 * E 1| := le_abs_self _
      _ = |refinedWeightDeriv 1| * |E 1| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hE (abs_nonneg _)
  have hv :=
    mul_le_mul_of_nonneg_left quarter_combined_variation_sqrt
      (show (0 : ℝ) ≤ (1 / 20 : ℝ) * Real.sqrt x by positivity)
  have hn :=
    mul_le_mul_of_nonneg_left quarter_combined_variation_unweighted
      (show (0 : ℝ) ≤ (21 / 20 : ℝ) by norm_num only)
  dsimp only [E] at hs hd
  ring_nf at ha hb hd hv hn hs ⊢
  linarith only [ha.1, hb.2, hd, hv, hn, hs]

end PseudoPrime.PrimeTestBounds.MillerRabin
