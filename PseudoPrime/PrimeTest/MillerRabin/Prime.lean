/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PrimeTest.MillerRabin.Spec
import Mathlib.FieldTheory.Finite.Basic

/-!
# Arithmetic preparation for Strong Miller–Rabin at primes
-/

namespace PseudoPrime.PrimeTest

private theorem pow_two_adic_eq_one_or_neg_one {F : Type*} [Field F] (x : F) :
    ∀ s : ℕ, x ^ (2 ^ s) = 1 → x = 1 ∨ ∃ r ∈ List.range s, x ^ (2 ^ r) = -1
  | 0, h => by
    left
    simpa only [pow_zero, pow_one] using h
  | s + 1, h => by
    have hsquare : (x ^ (2 ^ s)) ^ 2 = 1 := by
      calc
        (x ^ (2 ^ s)) ^ 2 = x ^ (2 ^ s * 2) := by rw [pow_mul]
        _ = x ^ (2 ^ (s + 1)) := by rw [pow_succ, Nat.mul_comm]
        _ = 1 := h
    rcases mul_self_eq_one_iff.mp (by simpa only [pow_two] using hsquare) with hpos | hneg
    · rcases pow_two_adic_eq_one_or_neg_one x s hpos with hx | ⟨r, hr, hxr⟩
      · exact Or.inl hx
      · exact
          Or.inr
            ⟨r, List.mem_range.mpr (Nat.lt_trans (List.mem_range.mp hr) (Nat.lt_succ_self s)), hxr⟩
    · exact Or.inr ⟨s, List.mem_range.mpr (Nat.lt_succ_self s), hneg⟩

/-- At a prime modulus, the computed exponent decomposition is `p - 1 = d * 2^s`. -/
theorem sub_eq_oddPart_mul_twoAdicPart {p : ℕ} :
    p - 1 = oddPart (p - 1) * 2 ^ twoAdicExponent (p - 1) := by
  rw [Nat.mul_comm]
  exact (twoAdicPart_mul_oddPart (p - 1)).symm

/-- The odd exponent in the prime decomposition is genuinely odd. -/
theorem prime_oddPart_odd {p : ℕ} (hp : p.Prime) : Odd (oddPart (p - 1)) := by
  apply oddPart_odd
  exact Nat.sub_ne_zero_of_lt hp.one_lt

private theorem strong_condition_of_prime {p a : ℕ} (hp : p.Prime) (ha : Nat.Coprime a p) :
    IsStrongMillerRabinProbablePrime p a := by
  let _ : Fact p.Prime := ⟨hp⟩
  let s := twoAdicExponent (p - 1)
  let d := oddPart (p - 1)
  have hpa : (a : ZMod p) ≠ 0 := by
    intro hzero
    exact (hp.coprime_iff_not_dvd.mp ha.symm) ((ZMod.natCast_eq_zero_iff a p).mp hzero)
  have hfermat : (a : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hpa
  have hdecomp : p - 1 = d * 2 ^ s := by exact sub_eq_oddPart_mul_twoAdicPart
  have hpow : ((a : ZMod p) ^ d) ^ (2 ^ s) = 1 := by
    rw [← pow_mul, ← hdecomp]
    exact hfermat
  rcases pow_two_adic_eq_one_or_neg_one ((a : ZMod p) ^ d) s hpow with hpos | hneg
  · left
    change zmodPowProof p a d = 1
    rw [zmodPowProof_eq_pow]
    exact hpos
  · right
    rcases hneg with ⟨r, hr, hneg⟩
    refine ⟨r, hr, ?_⟩
    rw [ZMod.natCast_self, zero_sub]
    rw [zmodPowProof_eq_pow]
    change (a : ZMod p) ^ (d * 2 ^ r) = -1
    simpa only [← pow_mul] using hneg

/-- A base coprime to a prime modulus passes the Strong Miller–Rabin test. -/
theorem strongMillerRabinWithBase_of_prime {p a : ℕ} (hp : p.Prime) (ha : Nat.Coprime a p) :
    strongMillerRabinWithBase p a = true := by
  exact (strongMillerRabinWithBase_eq_true_iff).2 (strong_condition_of_prime hp ha)

/-- Base `2` passes at every odd prime modulus. -/
theorem strongMillerRabinBase2_of_prime_of_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    strongMillerRabinBase2 p = true := by
  apply strongMillerRabinWithBase_of_prime hp
  apply Nat.coprime_comm.mpr
  apply hp.coprime_iff_not_dvd.mpr
  intro hdiv
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hdiv with hone | htwo
  · exact hp.ne_one hone
  · exact hp2 htwo

/-- The prechecked base-2 test accepts every prime, including `2`. -/
theorem strongMillerRabinBase2WithPrecheck_of_prime {p : ℕ} (hp : p.Prime) :
    strongMillerRabinBase2WithPrecheck p = true := by
  rcases eq_or_ne p 2 with rfl | hp2
  · rw [strongMillerRabinBase2WithPrecheck, primalityPrecheck_two]
  · have hlt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
    have hodd : Odd p := hp.odd_iff.mpr hlt
    rw [strongMillerRabinBase2WithPrecheck,
      primalityPrecheck_none_of_odd (by exact hlt) hodd hp.not_isSquare]
    exact strongMillerRabinBase2_of_prime_of_ne_two hp hp2

/-- The prechecked base-2 test satisfies the common primality-test interface. -/
theorem strongMillerRabinBase2WithPrecheck_spec :
    PrimalityTestSpec strongMillerRabinBase2WithPrecheck := by
  constructor
  · rw [strongMillerRabinBase2WithPrecheck, primalityPrecheck_zero]
  · rw [strongMillerRabinBase2WithPrecheck, primalityPrecheck_one]
  · rw [strongMillerRabinBase2WithPrecheck, primalityPrecheck_two]
  · intro n hn2 heven
    rw [strongMillerRabinBase2WithPrecheck, primalityPrecheck_even_false hn2 heven]
  · intro n hn
    exact strongMillerRabinBase2WithPrecheck_of_prime hn

end PseudoPrime.PrimeTest
