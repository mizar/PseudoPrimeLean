/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev

/-! # Elementary lower bounds for finite prime counts -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- For every natural B, Chebyshev's theta lower bound is at most pi(B)*log B.
Bound each prime logarithm by log B and sum. This gives an unconditional prime-count
input for subgroup counting without listing the primes. -/
theorem chebyshev_lower_le_primeCounting_mul_log (B : ℕ) :
    (B : ℝ) * Real.log 2 - Real.log (B + 1) - 2 * Real.sqrt B * Real.log B ≤
      (B.primeCounting : ℝ) * Real.log B := by
  apply (Chebyshev.theta_ge B).trans
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  have hs :=
    Finset.sum_le_sum (s := B.primesLE) (g := fun _ ↦ Real.log (B : ℝ))
      (fun p hp ↦
        Real.log_le_log (Nat.cast_pos.mpr (Nat.mem_primesLE.mp hp).2.pos)
          (Nat.cast_le.mpr (Nat.mem_primesLE.mp hp).1))
  simpa only [Finset.sum_const, nsmul_eq_mul, Nat.primesLE_card_eq_primeCounting] using hs

/-- If B>1 and M*log B is at most the elementary Chebyshev lower expression,
then there are at least M primes at most B. Divide by the positive logarithm.
This supplies an integer count for the binomial subgroup criterion. -/
theorem le_primeCounting_of_chebyshev_lower {B M : ℕ} (hB : 1 < B)
    (hM :
      (M : ℝ) * Real.log B ≤
        (B : ℝ) * Real.log 2 - Real.log (B + 1) - 2 * Real.sqrt B * Real.log B) :
    M ≤ B.primeCounting := by
  have hl := hM.trans (chebyshev_lower_le_primeCounting_mul_log B)
  have hp : 0 < Real.log (B : ℝ) := Real.log_pos (Nat.one_lt_cast.mpr hB)
  exact Nat.cast_le.mp ((mul_le_mul_iff_left₀ hp).mp hl)

end PseudoPrime.NumberTheory
