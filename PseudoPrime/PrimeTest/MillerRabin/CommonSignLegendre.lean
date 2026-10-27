/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.LocalLegendrePowers
public import PseudoPrime.PrimeTest.MillerRabin.WitnessSubgroup

/-! # Paired Legendre values on the actual common-sign subgroup

Reduction modulo prime factors preserves the unit and its common sign.
When the sign exponent is an odd multiple of each local half exponent,
the two local Legendre values agree and their product is one.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/-- A unit modulo n with sign power sigma has Legendre symbol sigma at a
prime factor p when its exponent is an odd multiple of p/2. Reduce the unit
through the canonical cast homomorphism and apply local Euler sign transport.
This is the prime-factor reduction used for the actual common-sign subgroup. -/
theorem legendre_unit_value_eq_sign_of_prime_factor_power {n p E k : ℕ} [NeZero n] [Fact p.Prime]
    [Fact (2 < p)] (hpn : p ∣ n) (u : (ZMod n)ˣ) {σ : ℤ} (hk : Odd k) (hE : E = (p / 2) * k)
    (hσ : σ = 1 ∨ σ = -1) (hpow : (u : ZMod n) ^ E = (σ : ZMod n)) :
    legendreSym p (((u : ZMod n).val : ℕ) : ℤ) = σ := by
  let f := ZMod.castHom hpn (ZMod p)
  have hrep : f (u : ZMod n) = ((u : ZMod n).val : ZMod p) := by
    calc
      f (u : ZMod n) = f (((u : ZMod n).val : ℕ) : ZMod n) :=
        congrArg f (ZMod.natCast_zmod_val (u : ZMod n)).symm
      _ = ((u : ZMod n).val : ZMod p) := map_natCast f _
  have hnon := (f.isUnit_map u.isUnit).ne_zero
  rw [hrep] at hnon
  have hp := congrArg f hpow
  rw [map_pow, map_intCast, hrep, hE] at hp
  apply legendre_eq_sign_of_half_mul_odd_power (by simpa only [Int.cast_natCast] using hnon) hk hσ
  simpa only [Int.cast_natCast] using hp

/-- Every unit in the actual common-sign subgroup has paired Legendre product
one at prime factors p and q when its exponent is an odd multiple of both
local half exponents. Membership supplies a shared sign; local reduction
identifies both symbols with it. This supplies paired-character triviality. -/
theorem legendre_pair_mul_eq_one_on_signSubgroup {n p q E kp kq : ℕ} [NeZero n] [Fact p.Prime]
    [Fact q.Prime] [Fact (2 < p)] [Fact (2 < q)] (hpn : p ∣ n) (hqn : q ∣ n) (hkp : Odd kp)
    (hkq : Odd kq) (hEp : E = (p / 2) * kp) (hEq : E = (q / 2) * kq) (u : (ZMod n)ˣ)
    (hu : u ∈ signSubgroup n E) :
    legendreSym p (((u : ZMod n).val : ℕ) : ℤ) * legendreSym q (((u : ZMod n).val : ℕ) : ℤ) =
      1 := by
  have hsign : ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ (u : ZMod n) ^ E = (σ : ZMod n) := by
    change u ^ E = 1 ∨ u ^ E = -1 at hu
    rcases hu with h | h
    · refine ⟨1, Or.inl rfl, ?_⟩
      simpa only [Units.val_pow_eq_pow_val, Units.val_one, Int.cast_one] using congrArg Units.val h
    · refine ⟨-1, Or.inr rfl, ?_⟩
      simpa only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, Int.cast_neg,
        Int.cast_one] using congrArg Units.val h
  obtain ⟨σ, hσ, hpow⟩ := hsign
  rw [legendre_unit_value_eq_sign_of_prime_factor_power hpn u hkp hEp hσ hpow,
    legendre_unit_value_eq_sign_of_prime_factor_power hqn u hkq hEq hσ hpow]
  rcases hσ with hσ | hσ
  · rw [hσ, one_mul]
  · rw [hσ, neg_mul_neg, one_mul]

end PseudoPrime.PrimeTest
