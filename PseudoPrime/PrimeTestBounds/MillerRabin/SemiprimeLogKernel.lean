/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.ProductFermatKernel
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Logarithmic bounds for a semiprime kernel -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For `n = p * q`, logarithmic bounds on a product radius and a count `C`
give `B ^ k < q` and put the local kernel gcd below `C`. Convert the log
inequalities using positivity, then bound the exact gcd by `p - 1`. This
supports both repeated and distinct prime-product semiprime cells. -/
theorem semiprime_kernel_of_log_bounds {n p q B C k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hprod : n = p * q) (hB : 1 < B) (hsize : (k : ℝ) * Real.log B < Real.log q)
    (hcount : Real.log p < Real.log (C : ℝ)) : B ^ k < q ∧ (q - 1).gcd (n - 1) < C := by
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr hq.pos
  have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr (zero_lt_one.trans hB)
  have hlog : Real.log ((B : ℝ) ^ k) < Real.log (q : ℝ) := by
    rw [Real.log_pow]
    exact hsize
  have hreal : (B : ℝ) ^ k < q := (Real.log_lt_log_iff (pow_pos hBpos _) hqpos).mp hlog
  have hnat : B ^ k < q := by exact_mod_cast hreal
  have hcpos : 0 < C := by
    by_contra h
    have hz : C = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.cast_zero, Real.log_zero] at hcount
    exact (not_lt_of_ge (Real.log_natCast_nonneg p)) hcount
  have hpchoose : p < C := by
    exact_mod_cast
      (Real.log_lt_log_iff (Nat.cast_pos.mpr hp.pos) (Nat.cast_pos.mpr hcpos)).mp hcount
  have hgcd : (q - 1).gcd (n - 1) ≤ p - 1 := by
    rw [hprod, Nat.mul_comm p q]
    exact NumberTheory.gcd_predecessor_product_le_cofactor hq.pos hp.one_lt
  exact ⟨hnat, hgcd.trans_lt ((Nat.sub_le p 1).trans_lt hpchoose)⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
