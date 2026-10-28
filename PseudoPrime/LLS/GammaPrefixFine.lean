/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaPrefixRecovered

/-! # Fine actual prefix bounds from the existing seed and checkpoints -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The unchanged ten node intervals certify finer signed seed coefficients.
Exact rational arithmetic retains cancellation for the actual boundary comparison. -/
theorem fine_seed_scalar :
    Analysis.gammaFiniteEulerUpper errorSeed100Ratios ≤ (5462337 / 1000000000 : ℚ) ∧
      (-61382 / 10000000 : ℚ) ≤
        gammaFiniteWeightedLower gammaSlopeRationalCoefficient errorSeed100Ratios ∧
      (5164647 / 500000 : ℚ) ≤
        gammaFiniteWeightedLower (gammaTailRationalCoefficient 100) errorSeed100Ratios := by
  decide +kernel

/-- The existing lcm identity and a checked logarithm give psi(100) <= 94.046.
This unconditional cap controls the negative seed-weight product. -/
theorem fine_seed_psi : Chebyshev.psi 100 ≤ (94046 / 1000 : ℝ) := by
  have hn : Nat.lcmUpto 100 = 69720375229712477164533808935312303556800 := by decide +kernel
  have hc :
    Analysis.rationalLogIntervalCheck 69720375229712477164533808935312303556800 136 20
        (94045 / 1000) (94046 / 1000) =
      true := by
    decide +kernel
  have h := (Analysis.rationalLogIntervalCheck_sound hc).2
  have he := Chebyshev.psi_eq_log_lcmUpto 100
  norm_num only [Nat.cast_ofNat] at he
  rw [he, hn]
  simpa only [Rat.cast_ofNat, Rat.cast_div, Nat.cast_ofNat] using h

/-- The certified signed node intervals bound the actual seed Euler weight above.
Transfer the rational scalar cap through the existing finite-ratio theorem. -/
theorem fine_seed_weight : Analysis.gammaResolventEulerWeight 100 ≤ (5462337 / 1000000000 : ℝ) := by
  have h := (Analysis.gamma_finite_ratio_check_euler_bounds error_seed100_ratio_check).2
  have hr := (Rat.cast_le (K := ℝ)).mpr fine_seed_scalar.1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h hr
  exact h.trans hr

/-- The certified signed node intervals bound the actual seed logarithmic slope below.
The weighted identity preserves the negative coefficient in the boundary estimate. -/
theorem fine_seed_slope : (-61382 / 10000000 : ℝ) ≤ gammaEulerLogSlope 100 := by
  have h := (gamma_finite_weighted_bounds error_seed100_ratio_check gammaSlopeRationalCoefficient).1
  have hr := (Rat.cast_le (K := ℝ)).mpr fine_seed_scalar.2.1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h hr
  rw [gamma_slope_eq_weighted]
  norm_num only [neg_div] at hr ⊢
  exact hr.trans h

/-- The same node intervals bound the actual seed main tail below.
Use the exact weighted-tail identity to retain its positive contribution. -/
theorem fine_seed_main : (5164647 / 500000 : ℝ) ≤ gammaEulerTailMain 100 := by
  have h :=
    (gamma_finite_weighted_bounds error_seed100_ratio_check (gammaTailRationalCoefficient 100)).1
  have hr := (Rat.cast_le (K := ℝ)).mpr fine_seed_scalar.2.2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h hr
  rw [show (100 : ℝ) = ((100 : ℚ) : ℝ) by norm_num only,
    gamma_tail_main_eq_weighted (by norm_num only : (0 : ℚ) < 100)]
  exact hr.trans h

/-- Under RH, the corrected one-sided formula bounds the actual smoothed sum at 100.
The existing logarithm lower bound supplies the rational cap 91.503. -/
theorem fine_seed_smoothed (hRH : RiemannHypothesis) :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 100 ≤ (91503 / 1000 : ℝ) := by
  have h := logWeightedMangoldtSum_le_rational_corrected hRH (by norm_num only : (1 : ℝ) < 100)
  have hs : Real.sqrt (100 : ℝ) ≤ 10 := Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  linarith only [h, hs, sharp_log100]

/-- Under RH, the actual seed boundary is at least 9.25391.
Combine all signed weight, slope, main-tail and smoothed inputs before rounding. -/
theorem fine_seed_boundary (hRH : RiemannHypothesis) :
    (925391 / 100000 : ℝ) ≤ gammaEulerBoundaryTail 100 := by
  have h :=
    gamma_euler_boundary_tail_lower fine_seed_weight (by norm_num only) fine_seed_psi
      fine_seed_slope (by norm_num only)
      (gamma_logWeightedMangoldtSum_nonneg (by norm_num only : (0 : ℝ) < 100))
      (fine_seed_smoothed hRH) fine_seed_main
  linarith only [h]

/-- A checked sixteen-term Taylor interval encloses the actual endpoint logarithm.
These rational endpoints control the corrected smoothed bounds without new finite data. -/
theorem fine_log35000 :
    (10463103 / 1000000 : ℝ) ≤ Real.log 35000 ∧ Real.log 35000 ≤ 10463104 / 1000000 := by
  have hc :
    Analysis.rationalLogIntervalCheck 35000 15 16 (10463103 / 1000000) (10463104 / 1000000) =
      true := by
    decide +kernel
  simpa only [Rat.cast_ofNat, Rat.cast_div] using Analysis.rationalLogIntervalCheck_sound hc

/-- A checked sixteen-term Taylor interval encloses the actual endpoint logarithm.
These rational endpoints control the corrected smoothed bounds without new finite data. -/
theorem fine_log33800 :
    (10428216 / 1000000 : ℝ) ≤ Real.log 33800 ∧ Real.log 33800 ≤ 10428217 / 1000000 := by
  have hc :
    Analysis.rationalLogIntervalCheck 33800 15 16 (10428216 / 1000000) (10428217 / 1000000) =
      true := by
    decide +kernel
  simpa only [Rat.cast_ofNat, Rat.cast_div] using Analysis.rationalLogIntervalCheck_sound hc

/-- A checked sixteen-term Taylor interval encloses the actual endpoint logarithm.
These rational endpoints control the corrected smoothed bounds without new finite data. -/
theorem fine_log50000 :
    (10819778 / 1000000 : ℝ) ≤ Real.log 50000 ∧ Real.log 50000 ≤ 10819779 / 1000000 := by
  have hc :
    Analysis.rationalLogIntervalCheck 50000 16 16 (10819778 / 1000000) (10819779 / 1000000) =
      true := by
    decide +kernel
  simpa only [Rat.cast_ofNat, Rat.cast_div] using Analysis.rationalLogIntervalCheck_sound hc

/-- A checked sixteen-term Taylor interval encloses the actual endpoint logarithm.
These rational endpoints control the corrected smoothed bounds without new finite data. -/
theorem fine_log48500 :
    (10789319 / 1000000 : ℝ) ≤ Real.log 48500 ∧ Real.log 48500 ≤ 10789320 / 1000000 := by
  have hc :
    Analysis.rationalLogIntervalCheck 48500 16 16 (10789319 / 1000000) (10789320 / 1000000) =
      true := by
    decide +kernel
  simpa only [Rat.cast_ofNat, Rat.cast_div] using Analysis.rationalLogIntervalCheck_sound hc

/-- A short checked rational Taylor interval caps the endpoint logarithm ratio.
This retains the logarithmic denominator in the actual one-sided psi estimate. -/
theorem fine_log_ratio35 : Real.log (175 / 169 : ℝ) ≤ 348873 / 10000000 := by
  have hc :
    Analysis.rationalLogIntervalCheck (175 / 169) 0 8 (3488725 / 100000000) (348873 / 10000000) =
      true := by
    decide +kernel
  simpa only [Rat.cast_ofNat, Rat.cast_div] using (Analysis.rationalLogIntervalCheck_sound hc).2

/-- A short checked rational Taylor interval caps the endpoint logarithm ratio.
This retains the logarithmic denominator in the actual one-sided psi estimate. -/
theorem fine_log_ratio50 : Real.log (100 / 97 : ℝ) ≤ 3045921 / 100000000 := by
  have hc :
    Analysis.rationalLogIntervalCheck (100 / 97) 0 8 (3045920 / 100000000) (3045921 / 100000000) =
      true := by
    decide +kernel
  simpa only [Rat.cast_ofNat, Rat.cast_div] using (Analysis.rationalLogIntervalCheck_sound hc).2

/-- Under RH, the actual endpoint smoothed sum satisfies the displayed rational bound.
Insert the certified logarithm and square-root caps in the one-sided analytic formula. -/
theorem fine_smoothed35000 (hRH : RiemannHypothesis) :
    (699407 / 20 : ℝ) ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 35000 := by
  have h := logWeightedMangoldtSum_ge_rational_refined hRH (by norm_num only : (1 : ℝ) < 35000)
  have hs : Real.sqrt (35000 : ℝ) ≤ 187083 / 1000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  linarith only [h, hs, fine_log35000.2]

/-- Under RH, the actual endpoint smoothed sum satisfies the displayed rational bound.
Insert the certified logarithm and square-root caps in the one-sided analytic formula. -/
theorem fine_smoothed33800 (hRH : RiemannHypothesis) :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 33800 ≤ (67579 / 2 : ℝ) := by
  have h := logWeightedMangoldtSum_le_rational_corrected hRH (by norm_num only : (1 : ℝ) < 33800)
  have hs : Real.sqrt (33800 : ℝ) ≤ 183848 / 1000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  linarith only [h, hs, fine_log33800.1]

/-- Under RH, the actual endpoint smoothed sum satisfies the displayed rational bound.
Insert the certified logarithm and square-root caps in the one-sided analytic formula. -/
theorem fine_smoothed50000 (hRH : RiemannHypothesis) :
    (6245984 / 125 : ℝ) ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 50000 := by
  have h := logWeightedMangoldtSum_ge_rational_refined hRH (by norm_num only : (1 : ℝ) < 50000)
  have hs : Real.sqrt (50000 : ℝ) ≤ 223607 / 1000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  linarith only [h, hs, fine_log50000.2]

/-- Under RH, the actual endpoint smoothed sum satisfies the displayed rational bound.
Insert the certified logarithm and square-root caps in the one-sided analytic formula. -/
theorem fine_smoothed48500 (hRH : RiemannHypothesis) :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 48500 ≤ (24245327 / 500 : ℝ) := by
  have h := logWeightedMangoldtSum_le_rational_corrected hRH (by norm_num only : (1 : ℝ) < 48500)
  have hs : Real.sqrt (48500 : ℝ) ≤ 220228 / 1000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  linarith only [h, hs, fine_log48500.1]

/-- Under RH, the actual psi value satisfies this lower bound.
Use the asymmetric smoothed difference and certified logarithm ratio, retaining signed errors. -/
theorem fine_psi35000 (hRH : RiemannHypothesis) : (33847 : ℝ) ≤ Chebyshev.psi 35000 := by
  apply
    psi_lower_of_one_sided_log_cap (x := 33800) (U := -21 / 2) (V := 593 / 20) (R :=
      348873 / 10000000) (by norm_num only) (by norm_num only)
  · linarith only [fine_smoothed33800 hRH]
  · linarith only [fine_smoothed35000 hRH]
  · norm_num only
  · convert fine_log_ratio35 using 1; norm_num only
  · norm_num only

/-- Under RH, the actual psi value satisfies this lower bound.
Use the asymmetric smoothed difference and certified logarithm ratio, retaining signed errors. -/
theorem fine_psi50000 (hRH : RiemannHypothesis) : (48498 : ℝ) ≤ Chebyshev.psi 50000 := by
  apply
    psi_lower_of_one_sided_log_cap (x := 48500) (U := -4673 / 500) (V := 4016 / 125) (R :=
      3045921 / 100000000) (by norm_num only) (by norm_num only)
  · linarith only [fine_smoothed48500 hRH]
  · linarith only [fine_smoothed50000 hRH]
  · norm_num only
  · convert fine_log_ratio50 using 1; norm_num only
  · norm_num only

/-- Under RH, the actual boundary at 35000 is at most 6.6986.
Retain the negative psi and smoothed-sum terms with the unchanged node coefficients. -/
theorem fine_boundary35000 (hRH : RiemannHypothesis) :
    gammaEulerBoundaryTail 35000 ≤ (33493 / 5000 : ℝ) := by
  have h :=
    gamma_euler_boundary_tail_upper (by norm_num only : (0 : ℝ) ≤ 9797 / 1000000000)
      checkpoint35000_weight_lower (by norm_num only : (0 : ℝ) ≤ 33847) (fine_psi35000 hRH)
      checkpoint35000_slope_upper (by norm_num only) (by norm_num only : (0 : ℝ) ≤ 699407 / 20)
      (fine_smoothed35000 hRH) checkpoint35000_main_upper
  linarith only [h]

/-- Under RH, the actual boundary at 50000 is at most 6.57622.
Use the sharper actual arithmetic inputs with the unchanged checkpoint coefficients. -/
theorem fine_boundary50000 (hRH : RiemannHypothesis) :
    gammaEulerBoundaryTail 50000 ≤ (328811 / 50000 : ℝ) := by
  have h :=
    gamma_euler_boundary_tail_upper (by norm_num only : (0 : ℝ) ≤ 6716 / 1000000000)
      gamma_center_cutoff_weight_lower (by norm_num only : (0 : ℝ) ≤ 48498) (fine_psi50000 hRH)
      gamma_center_cutoff_slope_upper (by norm_num only)
      (by norm_num only : (0 : ℝ) ≤ 6245984 / 125) (fine_smoothed50000 hRH)
      gamma_center_cutoff_main_upper
  linarith only [h]

/-- Under RH, any certified target boundary and error transport the finer seed credit.
This version accepts arbitrary target scalar caps while preserving the old transport API. -/
theorem fine_prefix_at (hRH : RiemannHypothesis) {b B E : ℝ} (hb : 1 ≤ b)
    (hB : gammaEulerBoundaryTail b ≤ B) (hE : gammaEulerTailErrorBudget b ≤ E) :
    15877 / 5000 + 925391 / 100000 - B - (93 / 1250 + E) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  exact
    gamma_euler_prefix_lower_of_transport_bounds hRH (by norm_num only) hb recovered_seed_prefix
      (fine_seed_boundary hRH) hB (add_le_add recovered_seed_error hE)

/-- Under RH, every actual Gamma prefix beyond the displayed cutoff has this credit.
Transport the finer seed through the unchanged checkpoint and use nonnegative prefix monotonicity.
-/
theorem gamma_prefix1000_fine (hRH : RiemannHypothesis) {b : ℝ} (hb : 1000 ≤ b) :
    (42457 / 10000 : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  have h :=
    fine_prefix_at hRH (by norm_num only : (1 : ℝ) ≤ 1000) (recovered_boundary1000 hRH)
      recovered_error1000
  have hm :=
    recovered_prefix_mono (c := 42457 / 10000) hb
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]; linarith only [h])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hm
  exact hm

/-- Under RH, every actual Gamma prefix beyond the displayed cutoff has this credit.
Transport the finer seed through the unchanged checkpoint and use nonnegative prefix monotonicity.
-/
theorem gamma_prefix35000_fine (hRH : RiemannHypothesis) {b : ℝ} (hb : 35000 ≤ b) :
    (28279 / 5000 : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  have h :=
    fine_prefix_at hRH (by norm_num only : (1 : ℝ) ≤ 35000) (fine_boundary35000 hRH)
      checkpoint35000_error_upper
  have hm :=
    recovered_prefix_mono (c := 28279 / 5000) hb
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]; linarith only [h])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hm
  exact hm

/-- Under RH, every actual Gamma prefix beyond the displayed cutoff has this credit.
Transport the finer seed through the unchanged checkpoint and use nonnegative prefix monotonicity.
-/
theorem gamma_prefix50000_fine (hRH : RiemannHypothesis) {b : ℝ} (hb : 50000 ≤ b) :
    (144457 / 25000 : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  have h :=
    fine_prefix_at hRH (by norm_num only : (1 : ℝ) ≤ 50000) (fine_boundary50000 hRH)
      gamma_tail_error_budget_le
  have hm :=
    recovered_prefix_mono (c := 144457 / 25000) hb
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]; linarith only [h])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hm
  exact hm

/-- Under RH, every actual Gaussian prefix beyond the displayed cutoff has this credit.
Apply the existing pointwise kernel comparison with factor 17/20 to the actual Gamma sum. -/
theorem gaussian_prefix1000_fine (hRH : RiemannHypothesis) {b : ℝ} (hb : 1000 ≤ b) :
    (721769 / 200000 : ℝ) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gaussianResolventMangoldtWeight m := by
  have h := recovered_gaussian_prefix (gamma_prefix1000_fine hRH hb)
  linarith only [h]

/-- Under RH, every actual Gaussian prefix beyond the displayed cutoff has this credit.
Apply the existing pointwise kernel comparison with factor 17/20 to the actual Gamma sum. -/
theorem gaussian_prefix35000_fine (hRH : RiemannHypothesis) {b : ℝ} (hb : 35000 ≤ b) :
    (480743 / 100000 : ℝ) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gaussianResolventMangoldtWeight m := by
  have h := recovered_gaussian_prefix (gamma_prefix35000_fine hRH hb)
  linarith only [h]

/-- Under RH, every actual Gaussian prefix beyond the displayed cutoff has this credit.
Apply the existing pointwise kernel comparison with factor 17/20 to the actual Gamma sum. -/
theorem gaussian_prefix50000_fine (hRH : RiemannHypothesis) {b : ℝ} (hb : 50000 ≤ b) :
    (2455769 / 500000 : ℝ) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gaussianResolventMangoldtWeight m := by
  have h := recovered_gaussian_prefix (gamma_prefix50000_fine hRH hb)
  linarith only [h]

end PseudoPrime.LLS
