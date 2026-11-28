/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterBridgeBoundary663
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterBridgePhase663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterBridgePhase663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalTrivial656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalWeights656

/-! # Principal comparison for the quarter-square bridge -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem bridge_log_box {r : ℝ} (hr : r ∈ Set.Icc 328 (663 / 2)) :
    (57 / 10 : ℝ) ≤ Real.log r ∧ Real.log r ≤ 5.804 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 27) (lo := 57 / 10) (hi := 6)
        (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 663 / 2) (j := 9) (n := 27) (lo := 5) (hi :=
        5.804) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl hu
  have hp := (by norm_num only : (0 : ℝ) < 328).trans_le hr.1
  exact
    ⟨hl.trans (Real.log_le_log (by norm_num only) hr.1), by
      linarith only [Real.log_le_log hp hr.2, hu]⟩

private theorem bridge_log_boundary {r : ℝ} (hr : r ∈ Set.Icc 328 (663 / 2)) :
    0.002065 ≤ 4 * quarterWeight656 (r ^ 2) (r ^ 2) * Real.log (2 * Real.pi) := by
  have hp := (by norm_num only : (0 : ℝ) < 328).trans_le hr.1
  rw [quarter_cutoff_weight_656 (sq_pos_of_pos hp), Real.sqrt_sq hp.le]
  have hlog : (1.837 : ℝ) ≤ Real.log (2 * Real.pi) := by linarith only [Analysis.log_two_mul_pi_gt]
  have hW : (0.09319731 : ℝ) ≤ (quarterKernel656.transform 1).re := by
    linarith only [quarter_unit_weight_656.1]
  have hw :=
    (div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 0.09319731) hp hr.2).trans
      (div_le_div_of_nonneg_right hW hp.le)
  have h :=
    mul_le_mul hw hlog (by norm_num only : (0 : ℝ) ≤ 1.837)
      ((by norm_num only : (0 : ℝ) ≤ 0.09319731 / (663 / 2)).trans hw)
  ring_nf at h ⊢
  linarith only [h]

/-- The three bridge intervals share the same principal comparison once
the signed Chebyshev boundary for the chosen cell has been supplied. -/
theorem quarter_bridge_principal_lower (hRH : RiemannHypothesis) {r C : ℝ}
    (hr : r ∈ Set.Icc 328 (663 / 2))
    (hC : C ≤ 4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2)) :
    let X := r ^ 2
    let S := fun n : ℕ ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) X n).re
    0.71780481 * r + C - 0.001384 - (0.8 + 3 * Real.log (2 * Real.pi)) * quarterWeight656 X 1 ≤
      4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) := by
  intro X S
  have h1 : 1 ≤ r := (by norm_num only : (1 : ℝ) ≤ 328).trans hr.1
  have hx : 1 ≤ X := one_le_pow₀ h1
  have hr' := (by norm_num only : (322 : ℝ) ≤ 328).trans hr.1
  have hl := bridge_log_box hr
  have hz : 14 ≤ 21 / 8 + Real.log X := by
    dsimp only [X]
    rw [Real.log_pow]
    linarith only [hl.1]
  have ht :=
    trivial_upper_weight hr'
      (by
        unfold shiftedCoord; rw [one_div, Real.log_inv, sub_neg_eq_add, Real.log_pow]
        linarith only [hl.1])
      (by
        unfold shiftedCoord; rw [one_div, Real.log_inv, sub_neg_eq_add, Real.log_pow]
        linarith only [hl.2])
  have hmass := quarter_integral_difference_656 hr'
  have hmiss := quarter_missing_mass_ratio_656 hx hz
  rw [Real.sqrt_sq (zero_le_one.trans h1)] at hmiss
  have hP := quarter_principal_explicit_656 hx
  have hZ := quarter_bridge_zero_abel_lower hRH hr
  have hB := bridge_log_boundary hr
  dsimp only [X, S] at hmass hmiss hP ⊢
  ring_nf at hmass hmiss hP ht hZ hC hB ⊢
  linarith only [hmass, hmiss, hP, ht, hZ, hC, bridge_weight_one hr.1, hB]

end PseudoPrime.PrimeTestBounds.MillerRabin
