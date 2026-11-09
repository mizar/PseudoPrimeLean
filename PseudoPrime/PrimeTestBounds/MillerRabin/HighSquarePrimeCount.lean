/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RelativeChebyshevLowerBounds

/-! # High-range prime supply at square radii -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, `psi (b ^ 2) ≥ (9 / 10) * b ^ 2` for every real `b ≥ 56`.
Apply the relative psi lower bound at width `1 / 20` and bound its remainder
by the difference between the two quadratic coefficients. This supplies the
uniform high-range prime-count estimate without enumerating primes. -/
theorem high_square_psi_lower (hRH : RiemannHypothesis) {b : ℝ} (hb : 56 ≤ b) :
    (9 / 10 : ℝ) * b ^ 2 ≤ Chebyshev.psi (b ^ 2) := by
  have hb0 : 0 ≤ b := by linarith only [hb]
  have hs : Real.sqrt (b ^ 2) = b := Real.sqrt_sq_eq_abs b |>.trans (abs_of_nonneg hb0)
  have hpsi :=
    LLS.psi_lower_relative_log_shift hRH (h := (1 / 20 : ℝ)) (by norm_num only) (by norm_num only)
      (sq_nonneg b)
  rw [hs] at hpsi
  have hprod : 0 ≤ (b - 56) * ((b + 56) / 20 - 2) := by
    apply mul_nonneg
    · linarith only [hb]
    · linarith only [hb]
  linarith only [hpsi, hprod]

/-- Under RH, a count whose logarithmic cost is at most nine tenths of a
square radius is no larger than the number of primes up to that radius.
Combine the high-range psi bound with mathlib's unconditional psi-to-pi bound. -/
theorem high_square_prime_count (hRH : RiemannHypothesis) {b M : ℕ} (hb : 56 ≤ b)
    (hM : (M : ℝ) * Real.log (b ^ 2 : ℕ) ≤ (9 / 10 : ℝ) * (b : ℝ) ^ 2) :
    M ≤ (b ^ 2).primeCounting := by
  have hB : 1 < b ^ 2 := by
    have hb2 : 2 ≤ b := by linarith only [hb]
    nlinarith only [hb2]
  have hpsi := high_square_psi_lower hRH (b := (b : ℝ)) (Nat.cast_le.mpr hb)
  norm_num only [Nat.cast_ofNat] at hpsi
  rw [← Nat.cast_pow] at hpsi hM
  have hl := hM.trans (hpsi.trans (Chebyshev.psi_le_primeCounting_mul_log (b ^ 2)))
  have hp : 0 < Real.log (b ^ 2 : ℕ) := Real.log_pos (Nat.one_lt_cast.mpr hB)
  exact Nat.cast_le.mp ((mul_le_mul_iff_left₀ hp).mp hl)

/-- Under RH, the floor of `(9 / 10) * b ^ 2 / log (b ^ 2)` is a lower
bound for the number of primes up to `b ^ 2` when `b ≥ 56`. The floor is at
most its argument and the logarithm is positive, so the preceding supply bound
applies to the exact high-range choice of `M`. -/
theorem high_square_floor_prime_count (hRH : RiemannHypothesis) {b : ℕ} (hb : 56 ≤ b) :
    ⌊((9 / 10 : ℝ) * (b : ℝ) ^ 2) / Real.log (b ^ 2 : ℕ)⌋₊ ≤ (b ^ 2).primeCounting := by
  have hB : 1 < b ^ 2 := by
    have hb2 : 2 ≤ b := by linarith only [hb]
    nlinarith only [hb2]
  have hu : 0 < Real.log (b ^ 2 : ℕ) := Real.log_pos (Nat.one_lt_cast.mpr hB)
  apply high_square_prime_count hRH hb
  have hx : 0 ≤ ((9 / 10 : ℝ) * (b : ℝ) ^ 2) / Real.log (b ^ 2 : ℕ) :=
    div_nonneg (mul_nonneg (by norm_num only) (sq_nonneg _)) hu.le
  have hf := Nat.floor_le hx
  have hm := mul_le_mul_of_nonneg_right hf hu.le
  rw [div_mul_cancel₀ _ hu.ne'] at hm
  exact hm

end PseudoPrime.PrimeTestBounds.MillerRabin
