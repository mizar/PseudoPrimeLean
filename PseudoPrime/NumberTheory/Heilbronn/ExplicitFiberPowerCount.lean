/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.ExplicitFiniteFiberCounts

/-! # Natural-power count bounds with the prescribed coefficient -/

public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For positive scale and precision satisfying `1/c≤1/(2a)`, raise the
explicit count bound to `a` and round its prime exponent up to an integer `g`.
Assume `1/84+1/a≤g/a`; monotonicity of real powers absorbs this rounding.
The result supplies the integer count input to finite-fiber energy budgets. -/
theorem boundedCongruenceCount_power_le_explicit_finite_fiber_of_exponent_bound {a c g : ℕ}
    (ha : 0 < a) (hc : 0 < c) (hprec : 1 / (c : ℝ) ≤ (1 / (a : ℝ)) / 2)
    (hratio : 1 / 84 + 1 / (a : ℝ) ≤ (g : ℝ) / a) :
    ∀ (p H : ℕ) [Fact p.Prime],
      Odd p →
        H < p →
        (H : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ) →
        boundedCongruenceCount p H ^ a ≤ finiteFiberCountCoefficient c a ^ a * H ^ a * p ^ g := by
  intro p H hp hodd hHp htop
  have hcount := boundedCongruenceCount_le_explicit_finite_fiber ha hc hprec p H hodd hHp htop
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hp1 : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (Fact.out : p.Prime).pos
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (boundedCongruenceCount p H)) hcount a
  have hratioPow := Real.rpow_le_rpow_of_exponent_le hp1 hratio
  have hpid : ((p : ℝ) ^ ((g : ℝ) / a)) ^ a = (p : ℝ) ^ g := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p),
      div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (ne_of_gt ha)), Real.rpow_natCast]
  have hprime : ((p : ℝ) ^ (1 / 84 + 1 / (a : ℝ))) ^ a ≤ (p : ℝ) ^ g := by
    calc
      _ ≤ ((p : ℝ) ^ ((g : ℝ) / a)) ^ a := pow_le_pow_left₀ (Real.rpow_nonneg hp0 _) hratioPow a
      _ = _ := hpid
  rw [mul_pow, mul_pow] at hpow
  have hfactor :
    (finiteFiberCountCoefficient c a : ℝ) ^ a * (H : ℝ) ^ a *
        ((p : ℝ) ^ (1 / 84 + 1 / (a : ℝ))) ^ a ≤
      (finiteFiberCountCoefficient c a : ℝ) ^ a * (H : ℝ) ^ a * (p : ℝ) ^ g :=
    mul_le_mul_of_nonneg_left hprime
      (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (Nat.cast_nonneg _) _))
  apply Nat.cast_le (α := ℝ).mp
  simpa only [Nat.cast_mul, Nat.cast_pow] using hpow.trans hfactor

/-- For a>0 and prescribed precision 1/c≤1/(2a), raise the explicit
full count estimate to a when g/a=1/84+1/a. The coefficient is exactly
the natural C_(c,a), without rounding. This supplies integer energy budgets. -/
theorem boundedCongruenceCount_power_le_explicit_finite_fiber {a c g : ℕ} (ha : 0 < a) (hc : 0 < c)
    (hprec : 1 / (c : ℝ) ≤ (1 / (a : ℝ)) / 2) (hratio : (g : ℝ) / a = 1 / 84 + 1 / (a : ℝ)) :
    ∀ (p H : ℕ) [Fact p.Prime],
      Odd p →
        H < p →
        (H : ℝ) ≤ (p : ℝ) ^ (5 / 28 : ℝ) →
        boundedCongruenceCount p H ^ a ≤ finiteFiberCountCoefficient c a ^ a * H ^ a * p ^ g := by
  exact
    boundedCongruenceCount_power_le_explicit_finite_fiber_of_exponent_bound ha hc hprec
      (by rw [hratio])

end PseudoPrime.NumberTheory.Heilbronn
