/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GeneralTwoPoleGammaWitness
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TwoPolePrimeTrivialBounds

/-! # Character-free two-pole bounds under full prime triviality -/

@[expose] public section

namespace PseudoPrime.LLS

/-- If every small prime has character value one, each prime dividing the character
level lies above the cutoff. A nonzero character value forces coprimality.
This removes level-prime contributions from the positive part of a ramp comparison. -/
theorem level_prime_above_cutoff_of_all_prime_trivial {q p : ℕ} (χ : DirichletCharacter ℂ q) {b : ℝ}
    (ht : ∀ r : ℕ, r.Prime → (r : ℝ) ≤ b → χ r = 1) (hp : p ∈ q.primeFactors) : b < (p : ℝ) := by
  apply lt_of_not_ge
  intro hb
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hv := ht p hprime hb
  have hz : χ p ≠ 0 := by
    rw [hv]
    exact one_ne_zero
  have hc := (ZMod.isUnit_iff_coprime p q).mp (MulChar.apply_ne_zero_iff.mp hz)
  exact (hprime.coprime_iff_not_dvd.mp hc) (Nat.mem_primeFactors.mp hp).2.1

/-- At positive scale, if each level prime lies beyond the ramp cutoff, its full
local correction is nonpositive for any complex character. All positive powers
remain beyond the cutoff, where unit-disk positivity gives the sign. Sum the local
terms without replacing them by absolute-value costs. -/
theorem gammaLocalCorrection_nonpos_of_level_primes_above {q : ℕ} (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) (ht : ∀ p ∈ q.primeFactors, (99 / 40 : ℝ) * x ≤ p) :
    gammaQuadraticLocalCorrection χ x ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg ?_ (Real.sqrt_nonneg x)
  apply Finset.sum_nonpos
  intro p hp
  apply
    mul_nonpos_of_nonneg_of_nonpos
      (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le))
  apply tsum_nonpos
  intro k
  apply
    Analysis.exponentialRampLocalCorrection_tail_nonpos_of_norm_le_one
      (χ.primitiveCharacter.norm_le_one p)
  apply (le_div_iff₀ hx).mpr
  have hpow : (p : ℝ) ≤ (p : ℝ) ^ (k + 1) := by
    exact_mod_cast Nat.le_self_pow (Nat.succ_ne_zero k) p
  exact (ht p hp).trans hpow

end PseudoPrime.LLS
