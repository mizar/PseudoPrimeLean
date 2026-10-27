/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.FiniteSignedEulerMassBounds
public import PseudoPrime.Analysis.Phase64EulerPrefixUpper

/-! # Certified full Euler mass for the first phase64 cell -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The ten checked power intervals at cutoff 500, with denominator 10^8.
The node order reuses the phase64 coefficients; exact power comparisons certify both endpoints. -/
def phase64Mass500Ratios (a : ℚ) : ℚ × ℚ :=
  let j := (Analysis.phaseResolvent64Coefficients.map Prod.fst).idxOf a
  let v := ([8944, 2580, 744, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD j 0
  ((v : ℚ) / 100000000, ((v : ℚ) + 1) / 100000000)

/-- The rational signed slope coefficient -c*sigma for the boundary term at 500. -/
def phase64Mass500SlopeCoeff (ab : ℚ × ℚ) : ℚ :=
  -ab.2 * (1 / 2 + ab.1)

/-- The rational signed main-integral coefficient c*500*sigma^2/(sigma-1). -/
def phase64Mass500MainCoeff (ab : ℚ × ℚ) : ℚ :=
  ab.2 * 500 * (1 / 2 + ab.1) ^ 2 / ((1 / 2 + ab.1) - 1)

/-- The rational integrated RH error envelope for one node, using sqrt(500)<=23
and log(500)<=63/10. Absolute coefficients are used only for this error. -/
def phase64Mass500ErrorNode (ab : ℚ × ℚ) : ℚ :=
  |ab.2| *
    ((1 / 20) *
        ((1 / 2 + ab.1) ^ 2 * (23 * (phase64Mass500Ratios ab.1).2) / ((1 / 2 + ab.1) - 1 / 2)) +
      (1839 / 1000) * ((phase64Mass500Ratios ab.1).2 * (1 + (1 / 2 + ab.1) * (63 / 10))) +
      (21 / 20) * ((1 / 2 + ab.1) * (phase64Mass500Ratios ab.1).2))

/-- The ten rational intervals contain all node powers at 500.
Exact kernel arithmetic verifies the generic denominator-20 power check. -/
theorem phase64_mass500_ratio_check :
    Analysis.finiteSignedEulerRatioCheck Analysis.phaseResolvent64Coefficients 20 500
        phase64Mass500Ratios =
      true := by
  decide +kernel

/-- The checked intervals give the weight lower bound, signed slope and main
upper bounds, and error upper allowance. Exact rational kernel arithmetic preserves cancellation. -/
theorem phase64_mass500_scalar_checks :
    (11 / 50000 : ℚ) ≤
        Analysis.finiteSignedEulerLower Analysis.phaseResolvent64Coefficients phase64Mass500Ratios ∧
      Analysis.finiteSignedEulerUpper
          (Analysis.phaseResolvent64Coefficients.map (fun ab ↦ (ab.1, phase64Mass500SlopeCoeff ab)))
          phase64Mass500Ratios ≤
        (-33 / 100000 : ℚ) ∧
      Analysis.finiteSignedEulerUpper
          (Analysis.phaseResolvent64Coefficients.map (fun ab ↦ (ab.1, phase64Mass500MainCoeff ab)))
          phase64Mass500Ratios ≤
        (49 / 100 : ℚ) ∧
      (Analysis.phaseResolvent64Coefficients.map phase64Mass500ErrorNode).sum ≤ (9 / 1000 : ℚ) := by
  decide +kernel

/-- The Chebyshev boundary at 500 is at least 500, unconditionally.
Use the checked lower bound 2^722<=lcm(1,...,500) and the logarithm lower bound for two. -/
theorem phase64_mass500_psi_lower : 500 ≤ Chebyshev.psi 500 := by
  have hn : 2 ^ 722 ≤ Nat.lcmUpto 500 := by decide +kernel
  have hnR : (2 : ℝ) ^ 722 ≤ (Nat.lcmUpto 500 : ℝ) := by exact_mod_cast hn
  have hm := Real.log_le_log (pow_pos (by norm_num only : (0 : ℝ) < 2) 722) hnR
  rw [Real.log_pow] at hm
  norm_num only [Nat.cast_ofNat] at hm
  have he := Chebyshev.psi_eq_log_lcmUpto 500
  norm_num only [Nat.cast_ofNat] at he
  rw [he]
  linarith only [hm, Real.log_two_gt_d9]

/-- The square root of 500 is at most 23, by squaring nonnegative quantities. -/
theorem phase64_mass500_sqrt_upper : Real.sqrt (500 : ℝ) ≤ 23 := by
  exact (Real.sqrt_le_iff).mpr ⟨by norm_num only, by norm_num only⟩

/-- The logarithm of 500 is at most 63/10.
A rational logarithm interval check supplies the endpoint. -/
theorem phase64_mass500_log_upper : Real.log (500 : ℝ) ≤ 63 / 10 := by
  have hc : Analysis.rationalLogIntervalCheck 500 9 20 0 (63 / 10) = true := by decide +kernel
  have h := (Analysis.rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

/-- The actual signed Euler weight at 500 is at least 11/50000.
Cast the rational lower check and apply the certified node-power intervals. -/
theorem phase64_mass500_weight_lower :
    (11 / 50000 : ℝ) ≤
      Analysis.finiteSignedEulerWeight Analysis.phaseResolvent64Coefficients 500 := by
  have h :=
    (Analysis.finiteSigned_ratio_check_euler_bounds Analysis.phaseResolvent64Coefficients
        (by norm_num only : 0 < (20 : ℕ)) phase64_mass500_ratio_check).1
  have hr := (Rat.cast_le (K := ℝ)).mpr phase64_mass500_scalar_checks.1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h hr
  exact hr.trans h

/-- The actual signed logarithmic slope at 500 is at most -33/100000.
Reweight the original node intervals by the exact signed slope coefficients. -/
theorem phase64_mass500_slope_upper :
    finiteSignedEulerLogSlope Analysis.phaseResolvent64Coefficients 500 ≤ -33 / 100000 := by
  have h :=
    (finiteSigned_weighted_euler_bounds Analysis.phaseResolvent64Coefficients
        phase64Mass500SlopeCoeff (by norm_num only : 0 < (20 : ℕ)) phase64_mass500_ratio_check).2
  have hr := (Rat.cast_le (K := ℝ)).mpr phase64_mass500_scalar_checks.2.1
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] at h hr
  rw [finiteSigned_slope_eq_weighted]
  simpa only [neg_div, phase64Mass500SlopeCoeff] using h.trans hr

/-- The actual signed main tail at 500 is at most 49/100.
Reweight the original intervals using the main-integral identity. -/
theorem phase64_mass500_main_upper :
    finiteSignedEulerTailMain Analysis.phaseResolvent64Coefficients 500 ≤ 49 / 100 := by
  have h :=
    (finiteSigned_weighted_euler_bounds Analysis.phaseResolvent64Coefficients
        phase64Mass500MainCoeff (by norm_num only : 0 < (20 : ℕ)) phase64_mass500_ratio_check).2
  have hr := (Rat.cast_le (K := ℝ)).mpr phase64_mass500_scalar_checks.2.2.1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h hr
  rw [show (500 : ℝ) = ((500 : ℚ) : ℝ) by norm_num only,
    finiteSigned_main_eq_weighted _ (by norm_num only : (0 : ℚ) < 500)]
  exact h.trans hr

/-- Under RH, the smoothed Mangoldt sum at 500 is at least 486.
Apply the refined global lower estimate with the certified root and logarithm bounds. -/
theorem phase64_mass500_smoothed_lower (hRH : RiemannHypothesis) :
    (486 : ℝ) ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 500 := by
  have h := logWeightedMangoldtSum_ge_rational_refined hRH (by norm_num only : (1 : ℝ) < 500)
  linarith only [h, phase64_mass500_sqrt_upper, phase64_mass500_log_upper]

/-- The integrated RH error allowance at 500 is at most 9/1000.
Use the generic node envelope and the checked rational sum. -/
theorem phase64_mass500_error_upper :
    finiteSignedEulerErrorBudget Analysis.phaseResolvent64Coefficients 500 ≤ 9 / 1000 := by
  have hl := (Analysis.finiteSignedPhaseNodeCheck_sound _ Analysis.phaseResolvent64_node_check).1
  have h :=
    finiteSignedEulerErrorBudget_le_envelope Analysis.phaseResolvent64Coefficients hl
      (by norm_num only : (1 : ℝ) ≤ 500) phase64_mass500_sqrt_upper phase64_mass500_log_upper
      (fun a ↦ ((phase64Mass500Ratios a).2 : ℝ))
      (fun ab hab ↦ by
        have he :=
          (Analysis.finiteSigned_ratio_check_sound Analysis.phaseResolvent64Coefficients
              (by norm_num only : 0 < (20 : ℕ)) phase64_mass500_ratio_check ab hab).2
        norm_num only [Rat.cast_ofNat] at he
        exact he)
  have hr := (Rat.cast_le (K := ℝ)).mpr phase64_mass500_scalar_checks.2.2.2
  norm_num only [Rat.cast_list_sum, List.map_map, Function.comp_def, phase64Mass500ErrorNode,
    Rat.cast_mul, Rat.cast_abs, Rat.cast_add, Rat.cast_div, Rat.cast_sub, Rat.cast_pow,
    Rat.cast_one, Rat.cast_ofNat] at hr
  exact h.trans hr

/-- Under RH, the full phase64 signed Euler mass is at most 31/10.
Combine the prefix upper bound and signed boundary/main estimates at 500.
This removes a numerical Euler-mass premise from the first-cell Jacobi criterion. -/
theorem phase64_euler_mass_le (hRH : RiemannHypothesis) :
    (∑' n : ℕ, Analysis.finiteSignedMangoldtWeight Analysis.phaseResolvent64Coefficients n) ≤
      (31 / 10 : ℝ) := by
  have hl := (Analysis.finiteSignedPhaseNodeCheck_sound _ Analysis.phaseResolvent64_node_check).1
  have hp :
    (∑ n ∈ Finset.Ioc 0 ⌊(500 : ℝ)⌋₊,
        Analysis.finiteSignedMangoldtWeight Analysis.phaseResolvent64Coefficients n) ≤
      (143 / 50 : ℝ) := by
    simpa only [Nat.floor_ofNat] using Analysis.phase64_prefix_seed_upper
  have h :=
    finiteSignedEulerMass_le_of_scalar_bounds hRH Analysis.phaseResolvent64Coefficients hl
      (by norm_num only : (1 : ℝ) ≤ 500) hp phase64_mass500_weight_lower (by norm_num only)
      phase64_mass500_psi_lower (by norm_num only) phase64_mass500_slope_upper (by norm_num only)
      (phase64_mass500_smoothed_lower hRH) (by norm_num only) phase64_mass500_main_upper
      phase64_mass500_error_upper
  linarith only [h]

end PseudoPrime.LLS
