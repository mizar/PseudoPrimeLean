/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt81Million
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1423toMillion

/-! # Prime-power correction on the logarithmic phase band -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Transport integer power comparisons to the real root used by the Chebyshev defect. -/
private theorem root_bounds {x y : ℝ} (hy : 0 ≤ y) (hx : 0 ≤ x) (n : ℕ) (hn : 0 < n)
    (hl : y ^ n ≤ x) (hu : x ≤ (1000000 : ℝ) ^ n) :
    y ≤ x ^ ((n : ℝ)⁻¹) ∧ x ^ ((n : ℝ)⁻¹) ≤ 1000000 := by
  have hp : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  constructor
  · apply (Real.le_rpow_inv_iff_of_pos hy hx hp).2
    simpa only [Real.rpow_natCast] using hl
  · apply (Real.rpow_inv_le_iff_of_pos hx (by norm_num only) hp).2
    simpa only [Real.rpow_natCast] using hu

private theorem root_psi_upper {y c : ℝ} (hy : 0 < y)
    (h : |Chebyshev.psi y - y| / Real.sqrt y ≤ c) : Chebyshev.psi y ≤ y + c * Real.sqrt y := by
  have hb := (le_abs_self _).trans ((div_le_iff₀ (Real.sqrt_pos.mpr hy)).mp h)
  linarith only [hb]

/-- Finite psi bounds at three roots give the defect across the entire phase band. -/
private theorem phase_defect {x : ℝ} (hx : 1423 ^ 2 ≤ x) (hu : x ≤ 10 ^ 12) :
    let r := fun n : ℕ => x ^ ((n : ℝ)⁻¹)
    Chebyshev.psi x - Chebyshev.theta x ≤
      (r 2 + (4 / 5) * Real.sqrt (r 2)) + (r 3 + (81 / 100) * Real.sqrt (r 3)) +
        (r 5 + (81 / 100) * Real.sqrt (r 5)) := by
  have hx0 : 0 ≤ x := (by norm_num only : (0 : ℝ) ≤ 1423 ^ 2).trans hx
  have h2 :=
    root_bounds (by norm_num only : (0 : ℝ) ≤ 1423) hx0 2 (by decide) hx
      (hu.trans (by norm_num only))
  have h3 :=
    root_bounds (by norm_num only : (0 : ℝ) ≤ 17) hx0 3 (by decide)
      ((by norm_num only : (17 : ℝ) ^ 3 ≤ 1423 ^ 2).trans hx) (hu.trans (by norm_num only))
  have h5 :=
    root_bounds (by norm_num only : (0 : ℝ) ≤ 17) hx0 5 (by decide)
      ((by norm_num only : (17 : ℝ) ^ 5 ≤ 1423 ^ 2).trans hx) (hu.trans (by norm_num only))
  have b2 :=
    root_psi_upper ((by norm_num only : (0 : ℝ) < 1423).trans_le h2.1)
      (psi_error_le_four_fifths_million h2.1 h2.2)
  have b3 :=
    root_psi_upper ((by norm_num only : (0 : ℝ) < 17).trans_le h3.1) (psi81_million h3.1 h3.2)
  have b5 :=
    root_psi_upper ((by norm_num only : (0 : ℝ) < 17).trans_le h5.1) (psi81_million h5.1 h5.2)
  exact (Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x).trans (add_le_add (add_le_add b2 b3) b5)

/-- Exponential coordinates of the phase cells stay in the certified three-root range. -/
private theorem phase_defect_range {L : ℝ} (hl : 22 ≤ L) (hu : L ≤ 27) :
    1423 ^ 2 ≤ Real.exp L ∧ Real.exp L ≤ 10 ^ 12 := by
  have hlo :=
    pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 2)
      (show 2 ≤ Real.exp 1 by linarith only [Real.add_one_le_exp (1 : ℝ)]) 22
  have hhi :=
    pow_le_pow_left₀ (Real.exp_pos 1).le
      (show Real.exp 1 ≤ 11 / 4 by linarith only [Real.exp_one_lt_d9]) 27
  have e (n : ℕ) : Real.exp (n : ℝ) = (Real.exp 1) ^ n := by
    simpa only [mul_one] using Real.exp_nat_mul 1 n
  exact
    ⟨((by norm_num only : (1423 : ℝ) ^ 2 ≤ 2 ^ 22).trans (hlo.trans (e 22).ge)).trans
        (Real.exp_le_exp.mpr hl),
      ((Real.exp_le_exp.mpr hu).trans ((e 27).le.trans hhi)).trans (by norm_num only)⟩

/-- Express each normalized root and its square root as an exponential in log x. -/
private theorem root_decay (L s : ℝ) :
    (Real.exp L) ^ s / Real.sqrt (Real.exp L) = Real.exp (L * s - L / 2) ∧
      Real.sqrt ((Real.exp L) ^ s) / Real.sqrt (Real.exp L) = Real.exp (L * s / 2 - L / 2) := by
  simp only [Real.sqrt_eq_rpow, ← Real.exp_mul, Real.exp_sub, div_eq_mul_inv, one_mul, and_self]

/-- On the closed logarithmic band from 22 to 27, bound the normalized prime-power contribution
by one plus five decaying exponentials using the finite psi bounds at three roots. -/
theorem psi_theta_phase_defect {L : ℝ} (hl : 22 ≤ L) (hu : L ≤ 27) :
    (Chebyshev.psi (Real.exp L) - Chebyshev.theta (Real.exp L)) / Real.sqrt (Real.exp L) ≤
      1 + 4 / 5 * Real.exp (-L / 4) + Real.exp (-L / 6) + 81 / 100 * Real.exp (-L / 3) +
        Real.exp (-3 * L / 10) +
        81 / 100 * Real.exp (-2 * L / 5) := by
  obtain ⟨ha, hb⟩ := phase_defect_range hl hu
  have h := div_le_div_of_nonneg_right (phase_defect ha hb) (Real.sqrt_nonneg (Real.exp L))
  refine h.trans (le_of_eq ?_)
  dsimp only
  simp only [add_div, mul_div_assoc, (root_decay L _).1, (root_decay L _).2]
  ring_nf
  simp only [Real.exp_zero]

/-- Transfer a lower psi estimate at the same point to theta using a scalar correction bound. -/
theorem theta_lower_of_psi_phase {L U D : ℝ} (hl : 22 ≤ L) (hu : L ≤ 27)
    (hp : (Real.exp L - Chebyshev.psi (Real.exp L)) / Real.sqrt (Real.exp L) ≤ U)
    (hd :
      1 + 4 / 5 * Real.exp (-L / 4) + Real.exp (-L / 6) + 81 / 100 * Real.exp (-L / 3) +
          Real.exp (-3 * L / 10) +
          81 / 100 * Real.exp (-2 * L / 5) ≤
        D) :
    (Real.exp L - Chebyshev.theta (Real.exp L)) / Real.sqrt (Real.exp L) ≤ U + D := by
  have h := add_le_add hp ((psi_theta_phase_defect hl hu).trans hd)
  rwa [← add_div, sub_add_sub_cancel] at h

end PseudoPrime.AnalyticNumberTheory.Arithmetic
