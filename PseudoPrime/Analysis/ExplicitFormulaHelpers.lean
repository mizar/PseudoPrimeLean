/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! # Scalar normalization and series helpers for explicit formulas -/

public section

namespace PseudoPrime.Analysis
/-- Remove the nonzero contour normalization from a residue-ledger limit.
The resulting limit can be combined with convergent trivial-zero partial sums. -/
theorem tendsto_residueLedger_of_normalized {f : ℕ → ℂ} {L : ℂ}
    (h :
      Filter.Tendsto (fun m ↦ 2 * Real.pi * Complex.I * f m) Filter.atTop (nhds (Complex.I • L))) :
    Filter.Tendsto f Filter.atTop (nhds ((2 * Real.pi : ℝ)⁻¹ • L)) := by
  have hpi : (2 * Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num only) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hn : (2 * Real.pi : ℂ) * Complex.I ≠ 0 := mul_ne_zero hpi Complex.I_ne_zero
  have hl : ((2 * Real.pi : ℂ) * Complex.I)⁻¹ * (Complex.I • L) = (2 * Real.pi : ℝ)⁻¹ • L := by
    rw [smul_eq_mul, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul,
      Complex.ofReal_ofNat, mul_inv_rev]
    calc
      _ = (Complex.I⁻¹ * Complex.I) * ((2 * Real.pi : ℂ)⁻¹ * L) := by ring
      _ = _ := by rw [inv_mul_cancel₀ Complex.I_ne_zero, one_mul]
  rw [← hl]
  exact
    (h.const_mul (((2 * Real.pi : ℂ) * Complex.I)⁻¹)).congr (fun m ↦ inv_mul_cancel_left₀ hn (f m))


/-- An absolute error bounded by a nonnegative radius is a multiple of that
radius by a real number of absolute value at most one. The zero radius is handled directly. -/
theorem exists_theta_mul_of_abs_le {y c : ℝ} (h : |y| ≤ c) : ∃ θ : ℝ, |θ| ≤ 1 ∧ y = θ * c := by
  by_cases hc : c = 0
  · have hy : y = 0 := abs_eq_zero.mp (le_antisymm (hc ▸ h) (abs_nonneg y))
    exact ⟨0, by norm_num only [abs_zero], by rw [hy, zero_mul]⟩
  · have hcpos : 0 < c := lt_of_le_of_ne ((abs_nonneg y).trans h) (Ne.symm hc)
    refine ⟨y / c, ?_, (div_mul_cancel₀ y hc).symm⟩
    rw [abs_div, abs_of_pos hcpos]
    exact (div_le_one hcpos).mpr h


/-- The shifted Basel series has sum `pi^2/6`. Its missing zero-index term vanishes. -/
theorem tsum_shifted_basel_eq : (∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + 1) ^ 2) = Real.pi ^ 2 / 6 := by
  have h := hasSum_zeta_two.summable.tsum_eq_zero_add
  have he : (∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + 1) ^ 2) = ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 := by
    symm
    simpa only [Nat.cast_zero, zero_pow (by norm_num only : 2 ≠ 0), div_zero, Nat.cast_add,
      Nat.cast_one, zero_add] using h
  exact he.trans hasSum_zeta_two.tsum_eq

end PseudoPrime.Analysis
