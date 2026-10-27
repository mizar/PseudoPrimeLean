/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Ring

/-! # Algebraic combination of quadratic and cubic correlation tails -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Nonnegative A,K,E,C,p with AK²≤E and AK³≤Cp³ satisfy
A³K⁸≤EC²p⁶. Multiply the quadratic bound by the square of the cubic bound.
This combines both tail estimates without choosing an optimizing height. -/
theorem mixed_band_mass_bound {A K E C p : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hquad : A * K ^ 2 ≤ E) (hcube : A * K ^ 3 ≤ C * p ^ 3) :
    A ^ 3 * K ^ 8 ≤ E * C ^ 2 * p ^ 6 := by
  have hs := pow_le_pow_left₀ (mul_nonneg hA (pow_nonneg hK 3)) hcube 2
  have hm := mul_le_mul hquad hs (sq_nonneg (A * K ^ 3)) hE
  convert hm using 1 <;> ring

/-- If t>0 and 0≤p≤2t, the Fourier-band error is at most 8sqrt(C)p sqrt(E).
Raise the comparison to the fourth power, use the combined tail budget,
and retain exact square-root identities. This is uniform in the band
height K and uses no asymptotic or numerical range assumption. -/
theorem mixed_band_fourier_error_le {A K E C p t : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hC : 0 ≤ C) (hp : 0 ≤ p) (ht : 0 < t) (hpt : p ≤ 2 * t) (hquad : A * K ^ 2 ≤ E)
    (hcube : A * K ^ 3 ≤ C * p ^ 3) :
    4 * K ^ 2 * (Real.sqrt (Real.sqrt (p ^ 2 * E * A ^ 3)) / t) ≤
      8 * Real.sqrt C * p * Real.sqrt E := by
  have hmass := mixed_band_mass_bound hA hK hE hquad hcube
  have hR : 0 ≤ p ^ 2 * E * A ^ 3 := mul_nonneg (mul_nonneg (sq_nonneg p) hE) (pow_nonneg hA 3)
  have hR4 : (Real.sqrt (Real.sqrt (p ^ 2 * E * A ^ 3))) ^ 4 = p ^ 2 * E * A ^ 3 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hR]
  have hC4 : (Real.sqrt C) ^ 4 = C ^ 2 := by rw [show 4 = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hC]
  have hE4 : (Real.sqrt E) ^ 4 = E ^ 2 := by rw [show 4 = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hE]
  have hp4 := pow_le_pow_left₀ hp hpt 4
  have hm :=
    mul_le_mul_of_nonneg_left hmass
      (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 256) (sq_nonneg p)) hE)
  have hh :=
    mul_le_mul_of_nonneg_left hp4
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 256) (sq_nonneg C)) (sq_nonneg E))
        (pow_nonneg hp 4))
  rw [← mul_div_assoc]
  apply (div_le_iff₀ ht).mpr
  apply
    le_of_pow_le_pow_left₀ (by decide : 4 ≠ 0)
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 8) (Real.sqrt_nonneg C)) hp)
          (Real.sqrt_nonneg E))
        ht.le)
  calc
    _ = 256 * K ^ 8 * (Real.sqrt (Real.sqrt (p ^ 2 * E * A ^ 3))) ^ 4 := by ring
    _ = 256 * p ^ 2 * E * (A ^ 3 * K ^ 8) := by
      rw [hR4]; ring
    _ ≤ 256 * p ^ 2 * E * (E * C ^ 2 * p ^ 6) := hm
    _ = 256 * C ^ 2 * E ^ 2 * p ^ 4 * p ^ 4 := by ring
    _ ≤ 256 * C ^ 2 * E ^ 2 * p ^ 4 * (2 * t) ^ 4 := hh
    _ = (8 * Real.sqrt C * p * Real.sqrt E * t) ^ 4 := by
      simp only [mul_pow, hC4, hE4]
      ring

end PseudoPrime.Analysis
