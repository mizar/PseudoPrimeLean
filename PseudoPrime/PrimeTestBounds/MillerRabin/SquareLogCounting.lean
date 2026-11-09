/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimePowerCountingCriteria

/-! # Logarithmic counting conditions for square inputs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For `n = p ^ 2`, logarithmic size and binomial-count inequalities imply
`B ^ k < p ^ 2` and `p - 1 < choose M k`. Positivity and monotonicity of
the real logarithm recover the natural inequalities. This connects analytic
square cells to the local prime-power witness criterion. -/
theorem square_choose_of_log_bounds {n p B M k : ℕ} (hp : p.Prime) (hn : n = p ^ 2) (hB : 1 < B)
    (hsize : (k : ℝ) * Real.log B < Real.log n)
    (hcount : Real.log n < 2 * Real.log (Nat.choose M k : ℝ)) :
    B ^ k < p ^ 2 ∧ p - 1 < Nat.choose M k := by
  have hpos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hnpos : (0 : ℝ) < n := by
    rw [hn, Nat.cast_pow]
    exact pow_pos hpos _
  have hsize' : Real.log ((B : ℝ) ^ k) < Real.log (n : ℝ) := by
    rw [Real.log_pow]
    exact hsize
  have hlt : (B : ℝ) ^ k < (n : ℝ) :=
    (Real.log_lt_log_iff (pow_pos (Nat.cast_pos.mpr (zero_lt_one.trans hB)) _) hnpos).mp hsize'
  have hpLog : Real.log n = 2 * Real.log p := by
    rw [hn, Nat.cast_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hcpos : 0 < Nat.choose M k := by
    by_contra h
    have hz : Nat.choose M k = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.cast_zero, Real.log_zero] at hcount
    have hpn := Real.log_natCast_nonneg p
    linarith only [hcount, hpLog, hpn]
  have hclog : Real.log (p : ℝ) < Real.log (Nat.choose M k : ℝ) := by linarith only [hcount, hpLog]
  have hpc : (p : ℝ) < (Nat.choose M k : ℝ) :=
    (Real.log_lt_log_iff hpos (Nat.cast_pos.mpr hcpos)).mp hclog
  have hnat : B ^ k < n := by exact_mod_cast hlt
  exact ⟨hn ▸ hnat, (Nat.sub_le p 1).trans_lt (Nat.cast_lt.mp hpc)⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
