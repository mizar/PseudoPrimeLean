/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaFiniteEM8

/-! # Magnitude of the finite critical-line approximation -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

private theorem norm_critical_power_le_one (t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (-((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)))‖ ≤ 1 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith only [hn1]
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
  apply Real.rpow_le_one_of_one_le_of_nonpos hn1
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im]
  norm_num only

/-- For `14 ≤ t ≤ 100`, the finite Euler–Maclaurin approximation has norm at most 137.
Each of its 127 powers has norm at most one, and the grouped correction coefficient has
norm at most 10. The bound controls errors in the phase factor. -/
theorem norm_finiteEM8_le (t : ℝ) (ht : 14 ≤ t) (ht100 : t ≤ 100) : ‖finiteEM8 t‖ ≤ 137 := by
  rw [finiteEM8_eq_grouped]
  have hsum :
    ‖∑ n ∈ Finset.Icc (1 : ℕ) 127, (n : ℂ) ^ (-((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)))‖ ≤
      127 := by
    calc
      _ ≤
          ∑ n ∈ Finset.Icc (1 : ℕ) 127,
            ‖(n : ℂ) ^ (-((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.Icc (1 : ℕ) 127, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        exact norm_critical_power_le_one t n (Finset.mem_Icc.mp hn).1
      _ = _ := by
        norm_num only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
  have hc := norm_finiteEM8_coefficient_le t ht ht100
  have hpow := norm_critical_power_le_one t 128 (by norm_num only)
  have hm :
    ‖finiteEM8Coefficient t * (128 : ℂ) ^ (-((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)))‖ ≤ 10 := by
    rw [norm_mul]
    have hh := mul_le_mul hc hpow (norm_nonneg _) (by norm_num only : (0 : ℝ) ≤ 10)
    linarith only [hh]
  have h :=
    norm_add_le
      (∑ n ∈ Finset.Icc (1 : ℕ) 127, (n : ℂ) ^ (-((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))))
      (finiteEM8Coefficient t * (128 : ℂ) ^ (-((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))))
  linarith only [hsum, hm, h]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
