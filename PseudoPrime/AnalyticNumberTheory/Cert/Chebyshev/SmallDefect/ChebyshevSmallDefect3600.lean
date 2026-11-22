/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLcmBounds
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.SmallDefect.ChebyshevSmallPsiBounds

/-! # A small-range higher-prime-power bound through 3600 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A kernel-checked integer comparison proves `psi 16 ≤ 13.53`. -/
theorem psi_sixteen_le_1353 : Chebyshev.psi 16 ≤ (1353 / 100 : ℝ) := by
  have hc : Nat.lcmUpto 16 ≤ 2 ^ 10 * 3 ^ 6 := by decide +kernel
  change Chebyshev.psi (↑(16 : ℕ) : ℝ) ≤ (1353 / 100 : ℝ)
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have hp : (0 : ℝ) < Nat.lcmUpto 16 := by exact_mod_cast Nat.lcmUpto_pos 16
  have hc' : (Nat.lcmUpto 16 : ℝ) ≤ (2 : ℝ) ^ 10 * (3 : ℝ) ^ 6 := by exact_mod_cast hc
  have h := Real.log_le_log hp hc'
  rw [Real.log_mul (by norm_num only : (2 : ℝ) ^ 10 ≠ 0) (by norm_num only : (3 : ℝ) ^ 6 ≠ 0),
    Real.log_pow, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  linarith only [h, Real.log_two_lt_d9, Real.log_three_lt_d9]

/-- A kernel-checked integer comparison proves `psi 60 ≤ 57.55`. -/
theorem psi_sixty_le_5755 : Chebyshev.psi 60 ≤ (5755 / 100 : ℝ) := by
  have hc : Nat.lcmUpto 60 ≤ 2 ^ 64 * 3 ^ 12 := by decide +kernel
  change Chebyshev.psi (↑(60 : ℕ) : ℝ) ≤ (5755 / 100 : ℝ)
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have hp : (0 : ℝ) < Nat.lcmUpto 60 := by exact_mod_cast Nat.lcmUpto_pos 60
  have hc' : (Nat.lcmUpto 60 : ℝ) ≤ (2 : ℝ) ^ 64 * (3 : ℝ) ^ 12 := by exact_mod_cast hc
  have h := Real.log_le_log hp hc'
  rw [Real.log_mul (by norm_num only : (2 : ℝ) ^ 64 ≠ 0) (by norm_num only : (3 : ℝ) ^ 12 ≠ 0),
    Real.log_pow, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  linarith only [h, Real.log_two_lt_d9, Real.log_three_lt_d9]

/-- For `0 ≤ x ≤ 3600`, the cube-root psi contribution is at most 13.53. -/
theorem psi_cube_root_le_1353_3600 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 3600) :
    Chebyshev.psi (x ^ ((3 : ℝ)⁻¹)) ≤ (1353 / 100 : ℝ) := by
  apply (Chebyshev.psi_mono _).trans psi_sixteen_le_1353
  apply
    (Real.rpow_inv_le_iff_of_pos hx0 (by norm_num only : (0 : ℝ) ≤ 16)
        (by norm_num only : (0 : ℝ) < 3)).2
  norm_num only [Real.rpow_ofNat]
  linarith only [hx]

/-- For `0 ≤ x ≤ 3600`, the square-root psi contribution is at most 57.55. -/
theorem psi_square_root_le_5755_3600 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 3600) :
    Chebyshev.psi (x ^ ((2 : ℝ)⁻¹)) ≤ (5755 / 100 : ℝ) := by
  apply (Chebyshev.psi_mono _).trans psi_sixty_le_5755
  apply
    (Real.rpow_inv_le_iff_of_pos hx0 (by norm_num only : (0 : ℝ) ≤ 60)
        (by norm_num only : (0 : ℝ) < 2)).2
  norm_num only [Real.rpow_ofNat]
  exact hx

/-- For `0 ≤ x ≤ 3600`, the higher prime-power mass is at most 76.26.
The Costa-Pereira inequality reduces the claim to three checked psi prefixes. -/
theorem psi_sub_theta_le_7626 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 3600) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (7626 / 100 : ℝ) := by
  have h := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  linarith only [h, psi_square_root_le_5755_3600 hx0 hx, psi_cube_root_le_1353_3600 hx0 hx,
    psi_fifth_root_le_416 hx0 (hx.trans (by norm_num only))]

/-- For `0 ≤ x ≤ 3600`, the higher prime-power mass is at most 75.24.
The proof uses finer two-prime certificates for the small psi prefixes. -/
theorem psi_sub_theta_le_7524 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 3600) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (7524 / 100 : ℝ) := by
  have h := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  linarith only [h, psi_square_root_le_5755_3600 hx0 hx, psi_cube_root_le_1353_3600 hx0 hx,
    psi_fifth_root_le_416 hx0 (hx.trans (by norm_num only))]

/-- A kernel-checked integer comparison proves `psi 58 ≤ 54.07`. -/
theorem psi_fifty_eight_le_5407 : Chebyshev.psi 58 ≤ (5407 / 100 : ℝ) := by
  have hl : 2 ^ 77 ≤ Nat.lcmUpto 58 := by decide +kernel
  have hu : Nat.lcmUpto 58 ≤ 2 ^ (77 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  linarith only [h.2, Real.log_two_lt_d9]

/-- For `0 ≤ x ≤ 3479`, the square-root psi contribution is at most 54.07. -/
theorem psi_square_root_le_5407_3479 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 3479) :
    Chebyshev.psi (x ^ ((2 : ℝ)⁻¹)) ≤ (5407 / 100 : ℝ) := by
  have hr : x ^ ((2 : ℝ)⁻¹) ≤ (5899 / 100 : ℝ) := by
    apply
      (Real.rpow_inv_le_iff_of_pos hx0 (by norm_num only : (0 : ℝ) ≤ 5899 / 100)
          (by norm_num only : (0 : ℝ) < 2)).2
    norm_num only [Real.rpow_ofNat]
    linarith only [hx]
  have hf : ⌊(5899 / 100 : ℝ)⌋₊ = 58 :=
    (Nat.floor_eq_iff (by norm_num only)).2 (by norm_num only [and_self])
  have he : Chebyshev.psi (5899 / 100 : ℝ) = Chebyshev.psi 58 := by
    rw [Chebyshev.psi_eq_psi_coe_floor, hf]
    norm_num only [Nat.cast_ofNat]
  exact (Chebyshev.psi_mono hr).trans (he ▸ psi_fifty_eight_le_5407)

/-- For `0 ≤ x ≤ 3479`, the higher prime-power mass is at most 71.76.
The square-root contribution stops below 59, allowing a smaller psi prefix. -/
theorem psi_sub_theta_le_7176 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 3479) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (7176 / 100 : ℝ) := by
  have h := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have hx' : x ≤ 3600 := hx.trans (by norm_num only)
  linarith only [h, psi_square_root_le_5407_3479 hx0 hx, psi_cube_root_le_1353_3600 hx0 hx',
    psi_fifth_root_le_416 hx0 (hx.trans (by norm_num only))]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
