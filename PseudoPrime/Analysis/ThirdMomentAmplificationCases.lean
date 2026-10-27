/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ThirdMomentAmplificationAlgebra

/-! # Main-term and error-term alternatives in third-moment amplification -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- If the Fourier main term controls B²E, the retained-energy relation
gives E³≤2048p⁴TJ³. Square E≤2JB and multiply by E. This handles the main
term without a separate small-correlation cutoff. -/
theorem energy_cube_le_of_main_term_dominates {p E B T J : ℝ} (hE : 0 ≤ E) (hcover : E ≤ 2 * J * B)
    (hmain : B ^ 2 * E ≤ 512 * p ^ 4 * T * J) : E ^ 3 ≤ 2048 * p ^ 4 * T * J ^ 3 := by
  have hs := pow_le_pow_left₀ hE hcover 2
  have h₁ := mul_le_mul_of_nonneg_right hs hE
  have h₂ :=
    mul_le_mul_of_nonneg_left hmain (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) (sq_nonneg J))
  nlinarith only [h₁, h₂]

/-- In the error-dominated case, use E=e², retained energy, and ΔE≤10T
to obtain E¹³≤104857600²p¹⁴T⁶J⁸. Cancel the positive Be, absorb the squared
height constraint, cube the retention bound, and finally square. This
is the source of the target p³² after T is replaced by its p³ logarithmic bound. -/
theorem energy_thirteenth_le_of_error_term_dominates {p e B D T J : ℝ} (hp : 0 ≤ p) (he : 0 < e)
    (hB : 0 < B) (hD : 0 ≤ D) (hT : 0 ≤ T) (hJ : 0 ≤ J) (hcover : e ^ 2 ≤ 2 * J * B)
    (hheight : D * e ^ 2 ≤ 10 * T) (herr : B ^ 4 * e ^ 4 ≤ 131072 * p ^ 7 * T * J * B * D ^ 2 * e) :
    e ^ 26 ≤ 10995116277760000 * p ^ 14 * T ^ 6 * J ^ 8 := by
  have hc : B ^ 3 * e ^ 3 ≤ 131072 * p ^ 7 * T * J * D ^ 2 :=
    (mul_le_mul_iff_left₀ (mul_pos hB he)).mp (by nlinarith only [herr])
  have hh := pow_le_pow_left₀ (mul_nonneg hD (sq_nonneg e)) hheight 2
  have h₁ := mul_le_mul_of_nonneg_right hc (pow_nonneg he.le 4)
  have h₂ :=
    mul_le_mul_of_nonneg_left hh
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 131072) (pow_nonneg hp 7)) hT) hJ)
  have hm : B ^ 3 * e ^ 7 ≤ 13107200 * p ^ 7 * T ^ 3 * J := by nlinarith only [h₁, h₂]
  have hs := pow_le_pow_left₀ (sq_nonneg e) hcover 3
  have h₃ := mul_le_mul_of_nonneg_right hs (pow_nonneg he.le 7)
  have h₄ :=
    mul_le_mul_of_nonneg_left hm (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 8) (pow_nonneg hJ 3))
  have hr : e ^ 13 ≤ 104857600 * p ^ 7 * T ^ 3 * J ^ 4 := by nlinarith only [h₃, h₄]
  have hf := pow_le_pow_left₀ (pow_nonneg he.le 13) hr 2
  convert hf using 1 <;> ring

end PseudoPrime.Analysis
