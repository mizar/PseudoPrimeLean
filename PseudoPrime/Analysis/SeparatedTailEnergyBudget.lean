/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ThirdMomentEnergyAlternatives

/-! # Separate cutoff-tail cost from the actual third moment -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Retain the third moment T in the off-diagonal estimate, but use a
separate cutoff budget H in Delta E<=10H. The error branch then has T^2H^4,
rather than T^6. Cancellation and squaring use the same positive budgets. -/
theorem energy_thirteenth_le_of_separated_error {p e B D T H J : ℝ} (hp : 0 ≤ p) (he : 0 < e)
    (hB : 0 < B) (hD : 0 ≤ D) (hT : 0 ≤ T) (hJ : 0 ≤ J) (hcover : e ^ 2 ≤ 2 * J * B)
    (hheight : D * e ^ 2 ≤ 10 * H) (herr : B ^ 4 * e ^ 4 ≤ 131072 * p ^ 7 * T * J * B * D ^ 2 * e) :
    e ^ 26 ≤ 10995116277760000 * p ^ 14 * T ^ 2 * H ^ 4 * J ^ 8 := by
  have hc : B ^ 3 * e ^ 3 ≤ 131072 * p ^ 7 * T * J * D ^ 2 :=
    (mul_le_mul_iff_left₀ (mul_pos hB he)).mp (by nlinarith only [herr])
  have hh := pow_le_pow_left₀ (mul_nonneg hD (sq_nonneg e)) hheight 2
  have h₁ := mul_le_mul_of_nonneg_right hc (pow_nonneg he.le 4)
  have h₂ :=
    mul_le_mul_of_nonneg_left hh
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 131072) (pow_nonneg hp 7)) hT) hJ)
  have hm : B ^ 3 * e ^ 7 ≤ 13107200 * p ^ 7 * T * H ^ 2 * J := by nlinarith only [h₁, h₂]
  have hs := pow_le_pow_left₀ (sq_nonneg e) hcover 3
  have h₃ := mul_le_mul_of_nonneg_right hs (pow_nonneg he.le 7)
  have h₄ :=
    mul_le_mul_of_nonneg_left hm (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 8) (pow_nonneg hJ 3))
  have hr : e ^ 13 ≤ 104857600 * p ^ 7 * T * H ^ 2 * J ^ 4 := by nlinarith only [h₃, h₄]
  have hf := pow_le_pow_left₀ (pow_nonneg he.le 13) hr 2
  convert hf using 1 <;> ring

/-- The actual amplification alternatives with separate cutoff cost H
are a diagonal cubic bound, a third-moment cubic bound, or the T^2H^4
error bound. This is the algebraic bridge from the log-free cutoff to log10. -/
theorem separated_tail_energy_alternatives {p E B D T H J R : ℝ} (hp : 0 < p) (hE : 0 < E)
    (hB : 0 < B) (hD : 0 ≤ D) (hT : 0 ≤ T) (hJ : 0 ≤ J) (hcover : E ≤ 2 * J * B)
    (hheight : D * E ≤ 10 * H) (ha : B ^ 2 * E ≤ p ^ 4 * D * B + p ^ 3 * R)
    (hR :
      p ^ 2 * R ^ 2 ≤ 64 * T * J * B ^ 2 * E + 16384 * T * J * B * D ^ 2 * p ^ 3 * Real.sqrt E) :
    E ^ 3 ≤ 40 * p ^ 4 * H * J ∨
      E ^ 3 ≤ 2048 * p ^ 4 * T * J ^ 3 ∨
      E ^ 13 ≤ 10995116277760000 * p ^ 14 * T ^ 2 * H ^ 4 * J ^ 8 := by
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
    energy_thirteenth_le_of_separated_error hp.le (Real.sqrt_pos.mpr hE) hB hD hT hJ
      (by simpa only [hs] using hcover) (by simpa only [hs] using hheight) herr'
  have he26 : Real.sqrt E ^ 26 = E ^ 13 := by
    calc
      _ = (Real.sqrt E ^ 2) ^ 13 := by ring
      _ = _ := by rw [hs]
  simpa only [he26] using h

end PseudoPrime.Analysis
