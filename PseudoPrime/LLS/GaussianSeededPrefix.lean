/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaCheckpoint1000Sharp
public import PseudoPrime.LLS.GammaCheckpoint35000
public import PseudoPrime.LLS.RiemannOneSidedCheckpoint
public import PseudoPrime.LLS.GaussianGammaPrefixTransfer

/-! # Propagation of the sharp seed to the retained Gaussian prefixes -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under RH and b>=35000, the Gamma prefix is at least 11263/2000.
Transport the existing seed boundary 1156/125 through the unchanged target
boundary and tail-error certificate, then apply prefix monotonicity. -/
theorem gamma_prefix35000_seeded (hRH : RiemannHypothesis) {b : ℝ} (hb : 35000 ≤ b) :
    (11263 / 2000 : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  have h :=
    gamma_euler_prefix_lower_from_seed100 (b := 35000) (E := 151 / 2000) hRH (by norm_num only)
      (sharp_seed_boundary hRH) (gamma_boundary35000_upper hRH)
      (by linarith only [gammaEulerTailErrorBudget_le_seed100, checkpoint35000_error_upper])
  have hc :
    (11263 / 2000 : ℝ) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊(35000 : ℝ)⌋₊, Analysis.gammaResolventMangoldtWeight m := by
    linarith only [h]
  have hm :=
    Analysis.gamma_euler_prefix_lower_mono (c := 11263 / 2000) (Nat.floor_mono hb)
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]
        simpa only [Nat.floor_ofNat] using hc)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hm
  exact hm

/-- Under RH and b>=35000, the Gaussian prefix is at least 191471/40000.
Apply the existing pointwise factor 17/20 to the seeded Gamma prefix.
No new quadrature nodes or input enumeration are used. -/
theorem gaussian_prefix35000_seeded (hRH : RiemannHypothesis) {b : ℝ} (hb : 35000 ≤ b) :
    (191471 / 40000 : ℝ) ≤ ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gaussianResolventMangoldtWeight n := by
  have hg := gamma_prefix35000_seeded hRH hb
  have hs :=
    Finset.sum_le_sum (s := Finset.Ioc 0 ⌊b⌋₊) (fun n _ ↦ gaussian_gamma_mangoldt_weight_le n)
  rw [← Finset.mul_sum] at hs
  have hm := mul_le_mul_of_nonneg_left hg (by norm_num only : (0 : ℝ) ≤ 17 / 20)
  linarith only [hm, hs]

/-- Under RH and b>=50000, the Gamma prefix is at least 28783/5000.
Transport the existing seed boundary 1156/125 through the unchanged target
boundary and tail-error certificate, then apply prefix monotonicity. -/
theorem gamma_prefix50000_seeded (hRH : RiemannHypothesis) {b : ℝ} (hb : 50000 ≤ b) :
    (28783 / 5000 : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  have h :=
    gamma_euler_prefix_lower_from_seed100 (b := 50000) (E := 377 / 5000) hRH (by norm_num only)
      (sharp_seed_boundary hRH) (boundary50000_refined hRH)
      (by linarith only [gammaEulerTailErrorBudget_le_seed100, gamma_tail_error_budget_le])
  have hc :
    (28783 / 5000 : ℝ) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊(50000 : ℝ)⌋₊, Analysis.gammaResolventMangoldtWeight m := by
    linarith only [h]
  have hm :=
    Analysis.gamma_euler_prefix_lower_mono (c := 28783 / 5000) (Nat.floor_mono hb)
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]
        simpa only [Nat.floor_ofNat] using hc)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hm
  exact hm

/-- Under RH and b>=50000, the Gaussian prefix is at least 489311/100000.
Apply the existing pointwise factor 17/20 to the seeded Gamma prefix.
No new quadrature nodes or input enumeration are used. -/
theorem gaussian_prefix50000_seeded (hRH : RiemannHypothesis) {b : ℝ} (hb : 50000 ≤ b) :
    (489311 / 100000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gaussianResolventMangoldtWeight n := by
  have hg := gamma_prefix50000_seeded hRH hb
  have hs :=
    Finset.sum_le_sum (s := Finset.Ioc 0 ⌊b⌋₊) (fun n _ ↦ gaussian_gamma_mangoldt_weight_le n)
  rw [← Finset.mul_sum] at hs
  have hm := mul_le_mul_of_nonneg_left hg (by norm_num only : (0 : ℝ) ≤ 17 / 20)
  linarith only [hm, hs]

end PseudoPrime.LLS
