/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ScaledRationalExp
public import PseudoPrime.Analysis.RationalMellinWeightFast
public import PseudoPrime.Analysis.RationalMellinWeightAdaptive

/-! # Rational Gaussian-weight term for critical-line certificates -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- The rational Gaussian approximation for a nonnegative grid argument.
It uses rounded squaring below the cutoff and vanishes at and beyond it.
The result is the Gaussian factor in the finite critical-line certificate. -/
def certificateGaussian (y : ℚ) : ℚ :=
  if 54 ≤ y then 0
  else
    let p : ℚ := 314159265358979323846264338327950288419716939937510 / 10 ^ 50
    let q : ℚ := -p * y
    (Analysis.rationalScaledRealExp (10 ^ 60) q 64 8).1

/-- The rational Gaussian weight for a grid cell and Gaussian index.
The transposed finite sum and its adaptive order agree with the analytical
quadrature weight and permit exact cell-term certificates. -/
def certificateWeight (t a b : ℚ) (k : ℕ) : ℚ × ℚ :=
  Analysis.rationalGaussianWeightFast t a b
    (314159265358979323846264338327950288419716939937510 / 10 ^ 50)
    (Analysis.rationalGaussianOrder k) k

/-- The rational Gaussian-weight contribution for a height, grid cell and
Gaussian index. The cutoff skips terms whose Gaussian approximation is zero.
The output is a complex component pair used in internal finite certificates. -/
def certificateCellTerm (t : ℚ) (i k : ℕ) : ℚ × ℚ :=
  if 54 ≤ ((k : ℚ) + 1) ^ 2 * (1 + (i : ℚ) / 16) then (0, 0)
  else
    Analysis.rationalComplexScale (certificateGaussian (((k : ℚ) + 1) ^ 2 * (1 + (i : ℚ) / 16)))
      (certificateWeight t (1 + (i : ℚ) / 16) (1 + ((i + 1 : ℕ) : ℚ) / 16) k)

/-- Every Gaussian-weight term vanishes from cell 848 onward, for every
height and Gaussian index. The first Gaussian is already beyond the cutoff,
and increasing the index can only increase its argument. -/
theorem certificate_term_tail_zero (t : ℚ) {i : ℕ} (hi : 848 ≤ i) (k : ℕ) :
    certificateCellTerm t i k = 0 := by
  have hiq : (848 : ℚ) ≤ i := by exact_mod_cast hi
  have hbase : (54 : ℚ) ≤ 1 + (i : ℚ) / 16 := by linarith only [hiq]
  have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
  have hk : (1 : ℚ) ≤ ((k : ℚ) + 1) ^ 2 := by nlinarith only [hk0, sq_nonneg (k : ℚ)]
  have hc : (54 : ℚ) ≤ ((k : ℚ) + 1) ^ 2 * (1 + (i : ℚ) / 16) := by
    nlinarith only [hbase, hk, mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr hbase)]
  simp only [certificateCellTerm, ite_eq_left hc, Prod.mk_zero_zero]

/-- Rounding a Gaussian-weight term from cell 848 onward still gives zero.
This permits the tail of every finite certificate to be discharged uniformly. -/
theorem certificate_round_tail_zero (t : ℚ) {i : ℕ} (hi : 848 ≤ i) (k : ℕ) :
    Analysis.rationalComplexRound (10 ^ 60) (certificateCellTerm t i k) = 0 := by
  simp only [certificate_term_tail_zero t hi k, Analysis.rationalComplexRound,
    Analysis.rationalGridFloor, Prod.fst_zero, Prod.snd_zero, zero_mul, Int.floor_zero,
    Int.cast_zero, zero_div, Prod.mk_zero_zero]

end PseudoPrime.AnalyticNumberTheory.RiemannXi
