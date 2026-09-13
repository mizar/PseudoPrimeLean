/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Factorization lemmas for nonsquare moduli

This file isolates the elementary factorization input needed for the composite-modulus Jacobi
construction: a nonzero nonsquare has a prime factor occurring to an odd exponent.
-/

namespace PseudoPrime.NumberTheory

/-- Four is coprime to every odd natural number. -/
theorem four_coprime_of_odd {n : ℕ} (hn : Odd n) : Nat.Coprime 4 n := by
  have hnot : ¬2 ∣ n := by
    intro htwo
    exact (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr htwo)
  have htwo : Nat.Coprime 2 n := Nat.prime_two.coprime_iff_not_dvd.mpr hnot
  simpa only [show 2 ^ 2 = 4 by decide] using htwo.pow_left 2

/-- A nonzero nonsquare has a prime factor whose factorization exponent is odd. -/
theorem exists_prime_odd_factorization_of_not_square {r : ℕ} (hr0 : r ≠ 0) (hns : ¬IsSquare r) :
    ∃ p ∈ r.primeFactors, Odd (r.factorization p) := by
  by_contra hexists
  push Not at hexists
  let s := ∏ p ∈ r.primeFactors, p ^ (r.factorization p / 2)
  apply hns
  refine ⟨s, ?_⟩
  rw [Nat.prod_primeFactors_pow_factorization hr0]
  simp only [s]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have heven : Even (r.factorization p) := Nat.not_odd_iff_even.mp (hexists p hp)
  obtain ⟨k, hk⟩ := heven
  rw [← pow_add]
  congr 1
  omega

end PseudoPrime.NumberTheory
