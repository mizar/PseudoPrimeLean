/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Jacobi-symbol zero criteria and prime-factor witnesses

Mathlib supplies the general Jacobi-symbol theory. This file exposes its zero criterion and
extracts prime-denominator witnesses from Jacobi values at composite denominators.
-/

namespace PseudoPrime.NumberTheory

/--
For a nonzero denominator, the Jacobi symbol vanishes exactly when the numerator and denominator
are not coprime.  This exposes mathlib's existing zero criterion without rebuilding its proof.
-/
theorem jacobi_eq_zero_iff_not_coprime {a : ℤ} {n : ℕ} [NeZero n] :
    jacobiSym a n = 0 ↔ a.gcd n ≠ 1 :=
  jacobiSym.eq_zero_iff_not_coprime

/--
If a Jacobi symbol is `-1`, some prime divisor of its denominator already has Jacobi symbol
`-1`. This extracts prime witnesses from composite moduli.
-/
theorem exists_prime_dvd_jacobi_eq_neg_one {a : ℤ} {n : ℕ} (h : jacobiSym a n = -1) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ jacobiSym a p = -1 :=
  jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one h

/--
If a Jacobi symbol with nonzero denominator is not `1`, some prime divisor of the denominator
already has Jacobi symbol different from `1`.  Unlike the `-1` specialization, this also covers
the value `0`, which is needed by the factor-detecting first-stop classification.
-/
theorem exists_prime_dvd_jacobi_ne_one {a : ℤ} {n : ℕ} (hn : n ≠ 0) (h : jacobiSym a n ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ jacobiSym a p ≠ 1 := by
  have hp0 (p : ℕ) (hp : p ∈ n.primeFactorsList) : p ≠ 0 := (Nat.pos_of_mem_primeFactorsList hp).ne'
  rw [← Nat.prod_primeFactorsList hn, jacobiSym.list_prod_right hp0] at h
  obtain ⟨x, hx, hxne⟩ := List.exists_mem_ne_one_of_prod_ne_one h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  exact ⟨p, Nat.prime_of_mem_primeFactorsList hp, Nat.dvd_of_mem_primeFactorsList hp, hxne⟩

end PseudoPrime.NumberTheory
