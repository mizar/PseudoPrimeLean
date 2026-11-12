/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! # An envelope bound for a finite Chebyshev interval -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- On `[39760, 65536]`, the Lee–Nosal error envelope is at least 600. The proof uses
rational bounds for the logarithm and for pi. -/
theorem lee_nosal_envelope_ge_600 {x : ℝ} (ha : 39760 ≤ x) (hb : x ≤ 65536) :
    (600 : ℝ) ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  have hl :=
    Real.log_le_log (show (0 : ℝ) < 2 ^ (15 : ℕ) by norm_num only)
      (show (2 : ℝ) ^ (15 : ℕ) ≤ x by
        norm_num only; linarith only [ha])
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hlo : (1039 / 100 : ℝ) ≤ Real.log x := by linarith only [hl, Real.log_two_gt_d9]
  have hu :=
    Real.log_le_log (show (0 : ℝ) < x by linarith only [ha])
      (show x ≤ (2 : ℝ) ^ (16 : ℕ) by
        norm_num only; linarith only [hb])
  rw [Real.log_pow] at hu
  norm_num only [Nat.cast_ofNat] at hu
  have hhi : Real.log x ≤ 12 := by linarith only [hu, Real.log_two_lt_d9]
  have hll :=
    Real.log_le_log (show (0 : ℝ) < Real.log x by linarith only [hlo])
      (show Real.log x ≤ (2 : ℝ) ^ (4 : ℕ) by
        norm_num only; linarith only [hhi])
  rw [Real.log_pow] at hll
  norm_num only [Nat.cast_ofNat] at hll
  have hgap : (759 / 100 : ℝ) ≤ Real.log x - Real.log (Real.log x) := by
    linarith only [hlo, hll, Real.log_two_lt_d9]
  have hprod : (788 / 10 : ℝ) ≤ Real.log x * (Real.log x - Real.log (Real.log x)) := by
    nlinarith only [mul_le_mul hlo hgap (by norm_num only : (0 : ℝ) ≤ 759 / 100)
        (by linarith only [hlo] : (0 : ℝ) ≤ Real.log x)]
  have hq :
    (302 / 100 : ℝ) ≤ Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
    apply (le_div_iff₀ (by nlinarith only [Real.pi_pos] : (0 : ℝ) < 8 * Real.pi)).2
    nlinarith only [hprod, Real.pi_lt_d2]
  have hs : (199 : ℝ) ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by nlinarith only [ha])
  have hm := mul_le_mul hs hq (by norm_num only : (0 : ℝ) ≤ 302 / 100) (Real.sqrt_nonneg x)
  nlinarith only [hm]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
