/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianFarHalfline
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianWitnessCutoff
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # The K186 comparison at the final Gaussian cutoff -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A rational scale between the K186 linear threshold and the limiting cutoff radius. -/
@[expose]
public noncomputable def gaussianK186FarScale : ℝ :=
  5196744155 / 10000000000

/-- The K186 squared scale fits the final Gaussian cutoff from log two million.
The entrance exponential estimate uses only the constant and linear Taylor terms. -/
public theorem gaussian_k186_far_cutoff {L : ℝ} (hL : 2000000 ≤ L) :
    (gaussianK186FarScale * L) ^ 2 ≤ gaussianWitnessCutoff L := by
  have he : Real.exp (-(((2000000 : ℝ) / 11000) ^ 2)) ≤ 1 / 30000 := by
    rw [Real.exp_neg, one_div]
    apply (inv_le_inv₀ (Real.exp_pos _) (by norm_num only)).2
    exact
      (by norm_num only : (30000 : ℝ) ≤ (2000000 / 11000 : ℝ) ^ 2 + 1).trans (Real.add_one_le_exp _)
  have h :=
    gaussianCell_cutoff_le (a := 2000000) (c := gaussianK186FarScale ^ 2) (scale :=
      2 * gaussianK186FarScale) (by norm_num only) hL he (by norm_num only [gaussianK186FarScale])
      (by
        ring_nf
        exact le_rfl)
  convert h using 1
  ring

/-- At the K186 far comparison anchor, the scaled logarithm is between zero and 28. -/
private theorem gaussian_k186_anchor_log :
    0 ≤ Real.log (gaussianK186FarScale * 10 ^ 12) ∧
      Real.log (gaussianK186FarScale * 10 ^ 12) ≤ 28 := by
  have ha : 1 ≤ gaussianK186FarScale * 10 ^ 12 := by norm_num only [gaussianK186FarScale]
  have h₂ := Real.log_two_lt_d9.trans (by norm_num only : (0.6931471808 : ℝ) < 7 / 10)
  have hl :=
    Real.log_le_log (zero_lt_one.trans_le ha)
      (show gaussianK186FarScale * 10 ^ 12 ≤ (2 : ℝ) ^ 40 by norm_num only [gaussianK186FarScale])
  rw [Real.log_pow] at hl
  simp only [Nat.cast_ofNat] at hl
  exact ⟨Real.log_nonneg ha, by linarith only [hl, h₂]⟩

/-- The K186 main term gives a strict far comparison from log `10 ^ 12`
when the total loss is bounded by the indicated logarithmic and constant terms. -/
public theorem gaussian_k186_far_comparison_wide {α L loss : ℝ} (hα : (0.7216056623106 : ℝ) ≤ α)
    (hL : 10 ^ 12 ≤ L)
    (hloss : loss ≤ (7 / 20 : ℝ) * Real.log (gaussianK186FarScale * L) ^ 2 + 500) :
    0 < α * (gaussianK186FarScale * L) - 3 / 8 * L - loss := by
  have hρ : 0 < gaussianK186FarScale := by norm_num only [gaussianK186FarScale]
  have he : Real.exp 1 ≤ gaussianK186FarScale * 10 ^ 12 :=
    Real.exp_one_lt_three.le.trans (by norm_num only [gaussianK186FarScale])
  obtain ⟨h₀, hlog⟩ := gaussian_k186_anchor_log
  have hsq := pow_le_pow_left₀ h₀ hlog 2
  have hd :
    2 * (7 / 20 : ℝ) * (Real.log (gaussianK186FarScale * 10 ^ 12) / 10 ^ 12) <
      0.7216056623106 * gaussianK186FarScale - 3 / 8 := by
    norm_num only [gaussianK186FarScale] at hlog ⊢
    linarith only [hlog]
  have hg :
    0 <
      gaussianFarGap gaussianK186FarScale (0.7216056623106 * gaussianK186FarScale - 3 / 8) (7 / 20)
        500 (10 ^ 12) := by
    unfold gaussianFarGap
    norm_num only [gaussianK186FarScale] at hsq ⊢
    linarith only [hsq]
  have h := gaussian_far_gap_pos hρ (by norm_num only) he hd hg hL
  have hm :=
    mul_le_mul_of_nonneg_right hα
      (mul_nonneg hρ.le ((by norm_num only : (0 : ℝ) ≤ 10 ^ 12).trans hL))
  dsimp only [gaussianFarGap] at h
  linarith only [h, hm, hloss]

/-- Retain the far comparison for callers with the smaller log-square budget. -/
public theorem gaussian_k186_far_comparison {α L loss : ℝ} (hα : (0.7216056623106 : ℝ) ≤ α)
    (hL : 10 ^ 12 ≤ L)
    (hloss : loss ≤ (61 / 1000 : ℝ) * Real.log (gaussianK186FarScale * L) ^ 2 + 500) :
    0 < α * (gaussianK186FarScale * L) - 3 / 8 * L - loss := by
  apply gaussian_k186_far_comparison_wide hα hL
  linarith only [hloss, sq_nonneg (Real.log (gaussianK186FarScale * L))]

/-- At the contour anchor the available linear margin supports a constant
loss of twenty thousand in addition to the logarithmic-square loss. -/
public theorem gaussian_k186_far_comparison_anchor {α L loss : ℝ} (hα : (0.7216056623106 : ℝ) ≤ α)
    (hL : 30000000000000 ≤ L)
    (hloss : loss ≤ (7 / 20 : ℝ) * Real.log (gaussianK186FarScale * L) ^ 2 + 20000) :
    0 < α * (gaussianK186FarScale * L) - 3 / 8 * L - loss := by
  let A : ℝ := 30000000000000
  let ρ := gaussianK186FarScale
  have hρ : 0 < ρ := by norm_num only [ρ, gaussianK186FarScale]
  have he : Real.exp 1 ≤ ρ * A :=
    Real.exp_one_lt_three.le.trans (by norm_num only [ρ, A, gaussianK186FarScale])
  have hlog :=
    Real.log_le_log (Real.exp_pos 1 |>.trans_le he)
      (show ρ * A ≤ (2 : ℝ) ^ 44 by norm_num only [ρ, A, gaussianK186FarScale])
  rw [Real.log_pow, Nat.cast_ofNat] at hlog
  have hpos : 0 ≤ Real.log (ρ * A) :=
    Real.log_nonneg ((Real.one_le_exp_iff.mpr zero_le_one).trans he)
  have hlog' : Real.log (ρ * A) ≤ 31 := by linarith only [hlog, Real.log_two_lt_d9]
  have hsq := pow_le_pow_left₀ hpos hlog' 2
  have hd : 2 * (7 / 20 : ℝ) * (Real.log (ρ * A) / A) < 0.7216056623106 * ρ - 3 / 8 := by
    norm_num only [ρ, A, gaussianK186FarScale] at hlog' ⊢
    linarith only [hlog']
  have hg : 0 < gaussianFarGap ρ (0.7216056623106 * ρ - 3 / 8) (7 / 20) 20000 A := by
    unfold gaussianFarGap
    norm_num only [ρ, A, gaussianK186FarScale] at hsq ⊢
    linarith only [hsq]
  have h := gaussian_far_gap_pos hρ (by norm_num only) he hd hg hL
  have hm :=
    mul_le_mul_of_nonneg_right hα
      (mul_nonneg hρ.le ((by norm_num only : (0 : ℝ) ≤ 30000000000000).trans hL))
  dsimp only [gaussianFarGap, ρ] at h hm
  linarith only [h, hm, hloss]

end PseudoPrime.PrimeTestBounds.MillerRabin
