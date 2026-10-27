/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ThirdMomentAmplificationCases

/-! # Complete algebraic alternatives for the truncated energy comparison -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- When the diagonal does not dominate, square the amplified comparison
and combine it with the scaled off-diagonal estimate. Cancel positive p².
This retains both the Fourier main and error terms in a polynomial budget. -/
theorem amplified_square_le_of_non_diagonal {p E B D T J R : ℝ} (hp : 0 < p) (hE : 0 ≤ E)
    (ha : B ^ 2 * E ≤ p ^ 4 * D * B + p ^ 3 * R) (hd : ¬B ^ 2 * E ≤ 2 * p ^ 4 * D * B)
    (hR :
      p ^ 2 * R ^ 2 ≤ 64 * T * J * B ^ 2 * E + 16384 * T * J * B * D ^ 2 * p ^ 3 * Real.sqrt E) :
    B ^ 4 * E ^ 2 ≤
      256 * p ^ 4 * T * J * B ^ 2 * E + 65536 * p ^ 7 * T * J * B * D ^ 2 * Real.sqrt E := by
  have hdiag := lt_of_not_ge hd
  have hlin : B ^ 2 * E ≤ 2 * p ^ 3 * R := by linarith only [ha, hdiag]
  have hs := pow_le_pow_left₀ (mul_nonneg (sq_nonneg B) hE) hlin 2
  have h₁ := mul_le_mul_of_nonneg_left hs (sq_nonneg p)
  have h₂ :=
    mul_le_mul_of_nonneg_left hR (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) (pow_nonneg hp.le 6))
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hp)).mp
  nlinarith only [h₁, h₂]

/-- The proved truncated-band comparisons force a diagonal cubic bound,
a main-term cubic bound, or the target thirteenth-power error bound.
Split only according to which explicit contribution dominates, then use
the corresponding comparison. No low-correlation exclusion is assumed. -/
theorem third_moment_energy_alternatives {p E B D T J R : ℝ} (hp : 0 < p) (hE : 0 < E) (hB : 0 < B)
    (hD : 0 ≤ D) (hT : 0 ≤ T) (hJ : 0 ≤ J) (hcover : E ≤ 2 * J * B) (hheight : D * E ≤ 10 * T)
    (ha : B ^ 2 * E ≤ p ^ 4 * D * B + p ^ 3 * R)
    (hR :
      p ^ 2 * R ^ 2 ≤ 64 * T * J * B ^ 2 * E + 16384 * T * J * B * D ^ 2 * p ^ 3 * Real.sqrt E) :
    E ^ 3 ≤ 40 * p ^ 4 * T * J ∨
      E ^ 3 ≤ 2048 * p ^ 4 * T * J ^ 3 ∨ E ^ 13 ≤ 10995116277760000 * p ^ 14 * T ^ 6 * J ^ 8 := by
  by_cases hd : B ^ 2 * E ≤ 2 * p ^ 4 * D * B
  · exact Or.inl (energy_cube_le_of_diagonal_dominates hp.le hE.le hB hJ hcover hheight hd)
  right
  by_cases hm : B ^ 2 * E ≤ 512 * p ^ 4 * T * J
  · exact Or.inl (energy_cube_le_of_main_term_dominates hE.le hcover hm)
  right
  have hc := amplified_square_le_of_non_diagonal hp hE.le ha hd hR
  have hm' := mul_le_mul_of_nonneg_right (lt_of_not_ge hm).le (mul_nonneg (sq_nonneg B) hE.le)
  have herr : B ^ 4 * E ^ 2 ≤ 131072 * p ^ 7 * T * J * B * D ^ 2 * Real.sqrt E := by
    nlinarith only [hc, hm']
  have hs := Real.sq_sqrt hE.le
  have he4 : Real.sqrt E ^ 4 = E ^ 2 := by
    calc
      _ = (Real.sqrt E ^ 2) ^ 2 := by ring
      _ = _ := by rw [hs]
  have herr' : B ^ 4 * Real.sqrt E ^ 4 ≤ 131072 * p ^ 7 * T * J * B * D ^ 2 * Real.sqrt E := by
    simpa only [he4] using herr
  have h :=
    energy_thirteenth_le_of_error_term_dominates hp.le (Real.sqrt_pos.mpr hE) hB hD hT hJ
      (by simpa only [hs] using hcover) (by simpa only [hs] using hheight) herr'
  have he26 : Real.sqrt E ^ 26 = E ^ 13 := by
    calc
      _ = (Real.sqrt E ^ 2) ^ 13 := by ring
      _ = _ := by rw [hs]
  simpa only [he26] using h

end PseudoPrime.Analysis
