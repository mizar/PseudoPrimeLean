/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev

/-! # Chebyshev bounds from least-common-multiple comparisons -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- If the least common multiple through `n` lies between consecutive powers of two,
the logarithmic identity for `psi n` places it between the corresponding multiples
of `log 2`. Integer inequalities can certify both sides without a prime table. -/
theorem psi_bounds_of_lcm_pow_two {n k : ℕ} (hlower : 2 ^ k ≤ Nat.lcmUpto n)
    (hupper : Nat.lcmUpto n ≤ 2 ^ (k + 1)) :
    (k : ℝ) * Real.log 2 ≤ Chebyshev.psi n ∧ Chebyshev.psi n ≤ (k + 1 : ℕ) * Real.log 2 := by
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num only) k
  have hl : (2 : ℝ) ^ k ≤ (Nat.lcmUpto n : ℝ) := by exact_mod_cast hlower
  have hp : (0 : ℝ) < Nat.lcmUpto n := by exact_mod_cast Nat.lcmUpto_pos n
  have hu : (Nat.lcmUpto n : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by exact_mod_cast hupper
  have h1 := Real.log_le_log hpos hl
  have h2 := Real.log_le_log hp hu
  rw [Real.log_pow] at h1 h2
  exact ⟨h1, h2⟩

/-- If the `q`th power of the least common multiple through `n` lies between consecutive
powers of two, the logarithmic identity bounds `q * psi n` between the corresponding multiples
of `log 2`. Taking a positive `q` permits tighter bounds than a single power-of-two comparison;
the integer inequalities are checked independently of any prime table. -/
theorem psi_bounds_of_lcm_pow_two_scaled {n k q : ℕ} (hlower : 2 ^ k ≤ (Nat.lcmUpto n) ^ q)
    (hupper : (Nat.lcmUpto n) ^ q ≤ 2 ^ (k + 1)) :
    (k : ℝ) * Real.log 2 ≤ (q : ℝ) * Chebyshev.psi n ∧
      (q : ℝ) * Chebyshev.psi n ≤ (k + 1 : ℕ) * Real.log 2 := by
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num only) k
  have hl : (2 : ℝ) ^ k ≤ (Nat.lcmUpto n : ℝ) ^ q := by exact_mod_cast hlower
  have hp : (0 : ℝ) < (Nat.lcmUpto n : ℝ) ^ q := pow_pos (by exact_mod_cast Nat.lcmUpto_pos n) q
  have hu : (Nat.lcmUpto n : ℝ) ^ q ≤ (2 : ℝ) ^ (k + 1) := by exact_mod_cast hupper
  have h1 := Real.log_le_log hpos hl
  have h2 := Real.log_le_log hp hu
  rw [Real.log_pow, Real.log_pow] at h1 h2
  exact ⟨h1, h2⟩

end PseudoPrime.AnalyticNumberTheory.Arithmetic
