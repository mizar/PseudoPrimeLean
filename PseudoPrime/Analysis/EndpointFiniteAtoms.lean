/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveComparison
public import PseudoPrime.Analysis.PointwiseReciprocalLowerBound

/-! # Generic prime-power contributions to principal endpoint sums -/

public section

namespace PseudoPrime.Analysis

/-- A certified lower prime logarithm bounds a reciprocal prime-power term. -/
theorem finitePrincipal_rec_atom {x a : ℝ} {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) (hx : 0 < x)
    (hnx : (p : ℝ) ^ k ≤ x) (hlog : a ≤ Real.log p) :
    a / (p : ℝ) ^ k * (1 - (p : ℝ) ^ k / x) ≤
      AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm x (p ^ k) := by
  rw [AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm_prime_pow hp hk]
  exact
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hlog (pow_nonneg (Nat.cast_nonneg p) k))
      (sub_nonneg.mpr ((div_le_one hx).mpr hnx))

/-- Certified prime and radius logarithms bound a smoothed prime-power term. -/
theorem finitePrincipal_log_atom {y a b z : ℝ} {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) (hy : 0 < y)
    (ha : a ≤ Real.log p) (hb : Real.log p ≤ b) (hz : z ≤ Real.log y) (hw : 0 ≤ 2 * z - k * b) :
    a * (2 * z - k * b) ≤
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm (y ^ 2) (p ^ k) := by
  rw [AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm_prime_pow
      (ne_of_gt (sq_pos_of_pos hy)) hp hk,
    Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  have hm := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  exact mul_le_mul ha (by linarith only [hz, hm]) hw (Real.log_nonneg (by exact_mod_cast hp.one_le))

end PseudoPrime.Analysis
