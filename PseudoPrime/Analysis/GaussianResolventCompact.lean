/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianResolventDerivatives
public import PseudoPrime.Analysis.GaussianResolventTail

/-! # From Gaussian resolvent grid samples to global domination

The 16001 node inequalities imply global domination using actual curvature,
evenness, and the certified rational-analytic tail.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Every point of [0,16] lies in a cell of width 1/1000 with left index below
16000. The floor of 1000x locates the cell; handle the final endpoint separately. -/
theorem exists_cell_on_zero_sixteen_gaussian_grid {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 16) :
    ∃ j : ℕ, j < 16000 ∧ x ∈ Set.Icc ((j : ℝ) / 1000) (((j + 1 : ℕ) : ℝ) / 1000) := by
  by_cases he : x = 16
  · refine ⟨15999, by norm_num only, ?_⟩
    rw [he]
    norm_num only [Set.mem_Icc, Nat.cast_add, Nat.cast_one, and_self]
  · have hl : x < 16 := lt_of_le_of_ne hx.2 he
    have hn : 0 ≤ 1000 * x := mul_nonneg (by norm_num only) hx.1
    have hj : Nat.floor (1000 * x) < 16000 :=
      (Nat.floor_lt hn).mpr
        (by
          norm_num only; linarith only [hl])
    refine ⟨Nat.floor (1000 * x), hj, ?_⟩
    have hlo := Nat.floor_le hn
    have hhi := Nat.lt_floor_add_one (1000 * x)
    constructor
    · exact (div_le_iff₀ (by norm_num only : (0 : ℝ) < 1000)).mpr (by linarith only [hlo])
    · rw [Nat.cast_add, Nat.cast_one]
      exact (le_div_iff₀ (by norm_num only : (0 : ℝ) < 1000)).mpr (by linarith only [hhi])

/-- If all 16001 grid nodes have scaled gap at least 9/100000, the gap is
at least 123/4000000 throughout [0,16]. Locate the grid cell and apply actual curvature
interpolation to its two certified endpoints. -/
theorem gaussianResolventScaledGap_lower_of_grid
    (hnodes : ∀ j : ℕ, j ≤ 16000 → 9 / 100000 ≤ gaussianResolventScaledGap ((j : ℝ) / 1000)) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 16) : 123 / 4000000 ≤ gaussianResolventScaledGap t := by
  obtain ⟨j, hj, hcell⟩ := exists_cell_on_zero_sixteen_gaussian_grid ht
  have hju : j + 1 ≤ 16000 := Nat.succ_le_iff.mpr hj
  have ha : 0 ≤ (j : ℝ) / 1000 := div_nonneg (Nat.cast_nonneg j) (by norm_num only : (0 : ℝ) ≤ 1000)
  have hab : (j : ℝ) / 1000 < ((j + 1 : ℕ) : ℝ) / 1000 := by
    apply (div_lt_div_iff_of_pos_right (by norm_num only : (0 : ℝ) < 1000)).mpr
    rw [Nat.cast_add, Nat.cast_one]
    exact lt_add_one _
  have hw : ((j + 1 : ℕ) : ℝ) / 1000 - (j : ℝ) / 1000 ≤ 1 / 1000 := by
    rw [Nat.cast_add, Nat.cast_one]
    exact le_of_eq (by ring)
  exact gaussianResolvent_gap_ge_of_endpoints ha hab hw (hnodes j hj.le) (hnodes (j + 1) hju) hcell

/-- The scaled gap is even. Both the rational resolvent and Gaussian damping
depend on t², and the Gamma density depends on cosh(πt). This covers negative heights. -/
theorem gaussianResolventScaledGap_abs (t : ℝ) :
    gaussianResolventScaledGap |t| = gaussianResolventScaledGap t := by
  have he : Real.pi * |t| = |Real.pi * t| := by rw [abs_mul, abs_of_pos Real.pi_pos]
  dsimp only [gaussianResolventScaledGap, gaussianResolventScaled, gaussianResolventMajorant,
    scaledGaussianGammaNorm, scaledGammaHalfLineNorm, gammaHalfLineNorm, gaussianGammaDamping]
  simp only [sq_abs, he, Real.cosh_abs]

/-- The 16001 node inequalities imply domination of the actual Gaussian kernel
norm at every real height. Interpolation covers [0,16], evenness covers its reflection,
and the certified rational-analytic tail covers the remaining heights.
Only the finite node inequalities remain as certificate inputs. -/
theorem norm_gaussianGammaFunction_le_gaussianResolvent_of_grid
    (hnodes : ∀ j : ℕ, j ≤ 16000 → 9 / 100000 ≤ gaussianResolventScaledGap ((j : ℝ) / 1000))
    (t : ℝ) : ‖gaussianGammaFunction (Complex.I * (t : ℂ))‖ ≤ gaussianResolventMajorant t := by
  apply norm_gaussianGammaFunction_le_gaussianResolvent_of_compact _ t
  intro x hx
  have h :=
    gaussianResolventScaledGap_lower_of_grid hnodes
      (show |x| ∈ Set.Icc (0 : ℝ) 16 from ⟨abs_nonneg x, hx⟩)
  rw [gaussianResolventScaledGap_abs] at h
  have h0 : 0 ≤ gaussianResolventScaledGap x := (by norm_num only : (0 : ℝ) ≤ 123 / 4000000).trans h
  have hb : scaledGaussianGammaNorm x ≤ gaussianResolventScaled x := sub_nonneg.mp h0
  rw [scaledGaussianGammaNorm_eq_kernel_norm] at hb
  exact (mul_le_mul_iff_right₀ (by nlinarith only [sq_nonneg x] : 0 < 1 + x ^ 2)).mp hb

end PseudoPrime.Analysis
