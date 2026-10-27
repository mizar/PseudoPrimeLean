/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.LegendreSymbol.Basic

/-! # Local Legendre values from common sign powers

Odd multiples of a local half exponent retain Euler's quadratic-character value.
A common sign at two odd prime factors forces their Legendre product to be one.
These arithmetic lemmas do not import analytic witness bounds.
-/

@[expose] public section

/-! Euler values at odd multiples of the local half exponent. -/

namespace PseudoPrime.PrimeTest

/-- For a nonzero residue at a prime p, raising to an odd multiple of p/2
gives the Legendre symbol. Euler's criterion and the two possible nonzero
symbol values reduce the extra odd power. This is the local sign transport. -/
theorem pow_half_mul_odd_eq_legendre {p k : ℕ} [Fact p.Prime] {a : ℤ} (ha : (a : ZMod p) ≠ 0)
    (hk : Odd k) : (a : ZMod p) ^ ((p / 2) * k) = (legendreSym p a : ZMod p) := by
  rw [pow_mul, ← legendreSym.eq_pow p a]
  rcases legendreSym.eq_one_or_neg_one p ha with h | h
  · rw [h, Int.cast_one, one_pow]
  · rw [h, Int.cast_neg, Int.cast_one]
    exact Odd.neg_one_pow hk

/-- At an odd prime, a half-exponent odd multiple with value a supplied sign
forces the Legendre symbol to equal that sign. Apply local Euler transport and
exclude equality of one and minus one modulo a prime greater than two.
This identifies the common MR sign with the local quadratic-character value. -/
theorem legendre_eq_sign_of_half_mul_odd_power {p k : ℕ} [Fact p.Prime] [Fact (2 < p)] {a σ : ℤ}
    (ha : (a : ZMod p) ≠ 0) (hk : Odd k) (hσ : σ = 1 ∨ σ = -1)
    (hpow : (a : ZMod p) ^ ((p / 2) * k) = (σ : ZMod p)) : legendreSym p a = σ := by
  rw [pow_half_mul_odd_eq_legendre ha hk] at hpow
  have hne : (-1 : ZMod p) ≠ 1 := ZMod.neg_one_ne_one
  rcases hσ with hσ | hσ
  · subst σ
    rcases legendreSym.eq_one_or_neg_one p ha with h | h
    · exact h
    · rw [h, Int.cast_neg, Int.cast_one] at hpow
      exact False.elim (hne hpow)
  · subst σ
    rcases legendreSym.eq_one_or_neg_one p ha with h | h
    · rw [h, Int.cast_one, Int.cast_neg, Int.cast_one] at hpow
      exact False.elim (hne hpow.symm)
    · exact h

/-- If one exponent is an odd multiple of both local half exponents and gives
the same sign at two odd primes, the product of their Legendre symbols is one.
Identify each symbol with the shared sign and square the sign.
This supplies triviality of paired local quadratic characters on common-sign inputs. -/
theorem legendre_pair_mul_eq_one_of_common_sign_power {p q E kp kq : ℕ} [Fact p.Prime]
    [Fact q.Prime] [Fact (2 < p)] [Fact (2 < q)] {a σ : ℤ} (ha : (a : ZMod p) ≠ 0)
    (hb : (a : ZMod q) ≠ 0) (hkp : Odd kp) (hkq : Odd kq) (hσ : σ = 1 ∨ σ = -1)
    (hEp : E = (p / 2) * kp) (hEq : E = (q / 2) * kq) (hpowp : (a : ZMod p) ^ E = (σ : ZMod p))
    (hpowq : (a : ZMod q) ^ E = (σ : ZMod q)) : legendreSym p a * legendreSym q a = 1 := by
  rw [hEp] at hpowp
  rw [hEq] at hpowq
  rw [legendre_eq_sign_of_half_mul_odd_power ha hkp hσ hpowp,
    legendre_eq_sign_of_half_mul_odd_power hb hkq hσ hpowq]
  rcases hσ with hσ | hσ
  · rw [hσ, one_mul]
  · rw [hσ, neg_mul_neg, one_mul]

end PseudoPrime.PrimeTest
