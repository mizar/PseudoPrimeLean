/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # The monotone comparison on the far Gaussian half-line -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The one-variable lower bound in H59, with the linear margin, logarithmic
loss and constant supplied separately. -/
@[expose]
public noncomputable def gaussianFarGap (ρ δ A B x : ℝ) : ℝ :=
  δ * x - A * Real.log (ρ * x) ^ 2 - B

/-- The slope of the H59 gap at a positive scale and argument. -/
private theorem gaussian_far_gap_deriv {ρ x : ℝ} (hρ : 0 < ρ) (hx : 0 < x) (δ A B : ℝ) :
    HasDerivAt (gaussianFarGap ρ δ A B) (δ - 2 * A * (Real.log (ρ * x) / x)) x := by
  have hc : ρ / (ρ * x) = 1 / x := by
    calc
      _ = (ρ * 1) / (ρ * x) := by rw [mul_one]
      _ = _ := mul_div_mul_left 1 x hρ.ne'
  have h := ((hasDerivAt_id x).const_mul ρ).log (mul_pos hρ hx).ne'
  simp only [id_eq, mul_one, hc] at h
  have hd := (((hasDerivAt_id x).const_mul δ).sub ((h.pow 2).const_mul A)).sub_const B
  convert hd using 1
  · rfl
  · simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    ring

/-- The H59 gap grows on the half-line when its entrance slope is positive.
The ratio of the logarithm to the scale decreases above `exp 1`. -/
public theorem gaussian_far_gap_mono {ρ δ A B x₀ : ℝ} (hρ : 0 < ρ) (hA : 0 ≤ A)
    (he : Real.exp 1 ≤ ρ * x₀) (hd : 2 * A * (Real.log (ρ * x₀) / x₀) < δ) :
    StrictMonoOn (gaussianFarGap ρ δ A B) (Set.Ici x₀) := by
  have hx₀ : 0 < x₀ := pos_of_mul_pos_right ((Real.exp_pos 1).trans_le he) hρ.le
  have hder (x : ℝ) (hx : x₀ ≤ x) := gaussian_far_gap_deriv hρ (hx₀.trans_le hx) δ A B
  refine
    strictMonoOn_of_deriv_pos (convex_Ici x₀)
      (fun x hx ↦ (hder x hx).continuousAt.continuousWithinAt) ?_
  intro x hx
  have hx' : x₀ ≤ x := interior_subset hx
  have hmul := mul_le_mul_of_nonneg_left hx' hρ.le
  have h := Real.log_div_self_antitoneOn he (he.trans hmul) hmul
  have hr (t : ℝ) : ρ * (Real.log (ρ * t) / (ρ * t)) = Real.log (ρ * t) / t := by
    rw [← mul_div_assoc, mul_div_mul_left _ _ hρ.ne']
  have h' := mul_le_mul_of_nonneg_left h hρ.le
  simp only [hr] at h'
  rw [(hder x hx').deriv]
  exact sub_pos.mpr ((mul_le_mul_of_nonneg_left h' (mul_nonneg (by norm_num only) hA)).trans_lt hd)

/-- Positive entrance slope and gap imply a positive comparison at every
later point, including the entrance itself. -/
public theorem gaussian_far_gap_pos {ρ δ A B x₀ x : ℝ} (hρ : 0 < ρ) (hA : 0 ≤ A)
    (he : Real.exp 1 ≤ ρ * x₀) (hd : 2 * A * (Real.log (ρ * x₀) / x₀) < δ)
    (hg : 0 < gaussianFarGap ρ δ A B x₀) (hx : x₀ ≤ x) : 0 < gaussianFarGap ρ δ A B x :=
  hg.trans_le
    ((gaussian_far_gap_mono hρ hA he hd).monotoneOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx)
      hx)

/-- The coarse H58 bounds make the H56 comparison strictly positive
throughout the H59 half-line. The cutoff is evaluated at scale `ρ * L`. -/
public theorem gaussian_far_comparison_pos {ρ α α₀ L₀ L C E R : ℝ} (hρ : 0 < ρ) (hα : α₀ ≤ α)
    (he : Real.exp 1 ≤ ρ * L₀) (hL : L₀ ≤ L)
    (hd : (122 / 1000 : ℝ) * (Real.log (ρ * L₀) / L₀) < α₀ * ρ - 3 / 8)
    (hg : 0 < gaussianFarGap ρ (α₀ * ρ - 3 / 8) (61 / 1000) 187 L₀) (hC : 13 ≤ C)
    (hE : E ≤ (61 / 1000 : ℝ) * Real.log (ρ * L) ^ 2) (hR : R ≤ 200) :
    0 < α * (ρ * L) - 3 / 8 * L + C - E - R := by
  have h₀ : 0 < L₀ := pos_of_mul_pos_right ((Real.exp_pos 1).trans_le he) hρ.le
  have hm := mul_le_mul_of_nonneg_right hα (mul_nonneg hρ.le (h₀.trans_le hL).le)
  have hd' : 2 * (61 / 1000 : ℝ) * (Real.log (ρ * L₀) / L₀) < α₀ * ρ - 3 / 8 := by
    norm_num only at hd ⊢
    exact hd
  have h := gaussian_far_gap_pos hρ (by norm_num only) he hd' hg hL
  dsimp only [gaussianFarGap] at h
  linarith only [hm, h, hC, hE, hR]

/-- A rational radius below the square root of the fixed high cutoff coefficient. -/
@[expose]
public noncomputable def gaussianFarScale : ℝ :=
  519674375 / 1000000000

/-- The squared rational radius fits inside the high Gaussian cutoff. -/
public theorem gaussian_far_scale_sq : gaussianFarScale ^ 2 ≤ (0.270061456043740 : ℝ) := by
  norm_num only [gaussianFarScale]

/-- A cheap upper bound for the logarithm at the comparison anchor. -/
private theorem gaussian_far_anchor_log :
    0 ≤ Real.log (gaussianFarScale * 10 ^ 12) ∧ Real.log (gaussianFarScale * 10 ^ 12) ≤ 28 := by
  have ha : 1 ≤ gaussianFarScale * 10 ^ 12 := by norm_num only [gaussianFarScale]
  have h₂ := Real.log_two_lt_d9.trans (by norm_num only : (0.6931471808 : ℝ) < 7 / 10)
  have hl :=
    Real.log_le_log (zero_lt_one.trans_le ha)
      (show gaussianFarScale * 10 ^ 12 ≤ (2 : ℝ) ^ 40 by norm_num only [gaussianFarScale])
  rw [Real.log_pow] at hl
  simp only [Nat.cast_ofNat] at hl
  exact ⟨Real.log_nonneg ha, by linarith only [hl, h₂]⟩

/-- H58's coarse analytic bounds imply the strict H56 comparison for the
fixed rational scale, from the numerical anchor `10 ^ 12` onward. -/
public theorem gaussian_far_fixed_comparison {α L C E R : ℝ} (hα : (721605939 / 1000000000 : ℝ) ≤ α)
    (hL : 10 ^ 12 ≤ L) (hC : 13 ≤ C)
    (hE : E ≤ (61 / 1000 : ℝ) * Real.log (gaussianFarScale * L) ^ 2) (hR : R ≤ 200) :
    0 < α * (gaussianFarScale * L) - 3 / 8 * L + C - E - R := by
  have hρ : 0 < gaussianFarScale := by norm_num only [gaussianFarScale]
  have he : Real.exp 1 ≤ gaussianFarScale * 10 ^ 12 :=
    Real.exp_one_lt_three.le.trans (by norm_num only [gaussianFarScale])
  obtain ⟨h₀, hlog⟩ := gaussian_far_anchor_log
  have hsq := pow_le_pow_left₀ h₀ hlog 2
  apply gaussian_far_comparison_pos hρ hα he hL _ _ hC hE hR
  · norm_num only [gaussianFarScale] at hlog ⊢
    linarith only [hlog]
  · unfold gaussianFarGap
    norm_num only [gaussianFarScale] at hsq ⊢
    linarith only [hsq]

/-- The paper's far range lies beyond the numerical anchor used for H59. -/
public theorem gaussian_far_anchor_of_log {L : ℝ} (hL : 0 < L)
    (hlog : (75 / 2 : ℝ) ≤ Real.log (gaussianFarScale * L)) : (10 : ℝ) ^ 12 ≤ L := by
  apply le_of_not_gt
  intro h
  have hρ : 0 < gaussianFarScale := by norm_num only [gaussianFarScale]
  have hm := Real.log_le_log (mul_pos hρ hL) (mul_le_mul_of_nonneg_left h.le hρ.le)
  linarith only [hlog, hm, gaussian_far_anchor_log.2]

/-- The rational radius meets the lower scale condition of the H58 envelope. -/
public theorem gaussian_far_half_le_scale : (1 / 2 : ℝ) ≤ gaussianFarScale := by
  norm_num only [gaussianFarScale]

end PseudoPrime.PrimeTestBounds.MillerRabin
