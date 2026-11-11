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

/-- For every natural `B`, `B log 2 - log (B+1)` is at most `pi(B) log B`.
Use the lower bound for `psi` and group its prime powers by their underlying prime.
This supplies unconditional prime counts without a higher-prime-power error. -/
theorem chebyshev_lower_le_primeCounting_mul_log (B : ℕ) :
    (B : ℝ) * Real.log 2 - Real.log (B + 1) ≤ (B.primeCounting : ℝ) * Real.log B := by
  exact (Chebyshev.psi_ge B).trans (Chebyshev.psi_le_primeCounting_mul_log B)

/-- If B>1 and M*log B is at most the elementary Chebyshev lower expression,
then there are at least M primes at most B. Divide by the positive logarithm.
This supplies an integer count for the binomial subgroup criterion. -/
theorem le_primeCounting_of_chebyshev_lower {B M : ℕ} (hB : 1 < B)
    (hM : (M : ℝ) * Real.log B ≤ (B : ℝ) * Real.log 2 - Real.log (B + 1)) :
    M ≤ B.primeCounting := by
  have hl := hM.trans (chebyshev_lower_le_primeCounting_mul_log B)
  have hp : 0 < Real.log (B : ℝ) := Real.log_pos (Nat.one_lt_cast.mpr hB)
  exact Nat.cast_le.mp ((mul_le_mul_iff_left₀ hp).mp hl)

end PseudoPrime.NumberTheory
