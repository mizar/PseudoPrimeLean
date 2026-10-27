/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.PrimeTest.MillerRabin.KorseltCanonicalSign
public import PseudoPrime.PrimeTest.MillerRabin.LocalLegendrePowers
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Squarefree
public import PseudoPrime.NumberTheory.SquarefreeDivisibility

/-! # A global sign criterion for AGP strong pseudoprimes

The CRT argument in the AGP construction aims to make the residual Miller–Rabin
power equal to a common sign modulo the whole Carmichael number. This file
connects that global equality to the existing strong-pass predicate.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest.MillerRabin.AGP

/--
Inputs: `n` is odd and greater than one, and `x` is a residue modulo `n` whose
power by the odd part of `n - 1` is either `1` or `-1`.

Claim: `x` passes the strong Miller–Rabin test modulo `n`.

Content: the positive-sign case is the first pass branch; the negative-sign
case is the `j = 0` branch.

Proof: obtain positivity of the two-adic valuation from the canonical odd
decomposition, then use it as the bound for `j = 0`.

Role: this is the final local-to-test step for the common-sign condition in the
AGP construction; the prime-factor and CRT argument must supply the power equality.
-/
theorem strongMillerRabinPass_of_residual_power_eq_sign {n : ℕ} (hn : 1 < n) (hnOdd : Odd n)
    {x : ZMod n} (h : x ^ Nat.divMaxPow (n - 1) 2 = 1 ∨ x ^ Nat.divMaxPow (n - 1) 2 = -1) :
    PrimeTest.StrongMillerRabinPass n x := by
  rcases h with h | h
  · exact Or.inl h
  · right
    obtain ⟨hs, _, _⟩ := PrimeTest.odd_sub_canonical_decomp hn hnOdd
    refine ⟨0, hs, ?_⟩
    simpa only [pow_zero, one_mul] using h

/--
Inputs: `n` is odd and greater than one; `p` is prime and `3 mod 4`; the
Korselt divisibility `p - 1 ∣ n - 1` holds; and the base is nonzero modulo `p`.

Claim: the residual power of the base modulo `p` equals its Legendre symbol.

Content: the odd part of `n - 1` is an odd multiple of `p / 2`, so Euler's
criterion identifies the power with the quadratic character.

Proof: use `odd_part_korselt`, identify the odd part of `p - 1` with `p / 2`
from `p % 4 = 3`, then apply `pow_half_mul_odd_eq_legendre`.

Role: this supplies the prime-modulus calculation needed before combining the
common Legendre signs modulo the whole squarefree Carmichael number.
-/
theorem residual_power_eq_legendre_at_prime {n p b : ℕ} (hn : 1 < n) (hnOdd : Odd n) [Fact p.Prime]
    (hpMod : p % 4 = 3) (hpK : p - 1 ∣ n - 1) (hbp : ¬p ∣ b) :
    (b : ZMod p) ^ Nat.divMaxPow (n - 1) 2 = (legendreSym p b : ZMod p) := by
  have hpGt : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hpOdd : Odd p := Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_three hpMod)
  have hrepr : p = 3 + 4 * (p / 4) := by
    calc
      p = p % 4 + 4 * (p / 4) := (Nat.mod_add_div p 4).symm
      _ = 3 + 4 * (p / 4) := congrArg (fun r : ℕ => r + 4 * (p / 4)) hpMod
  have hhalf : p / 2 = 2 * (p / 4) + 1 := by
    calc
      p / 2 = (3 + 4 * (p / 4)) / 2 := congrArg (fun x : ℕ => x / 2) hrepr
      _ = (3 + 2 * 2 * (p / 4)) / 2 := by rw [show 4 = 2 * 2 by decide]
      _ = (3 + 2 * (2 * (p / 4))) / 2 :=
        congrArg (fun x : ℕ => (3 + x) / 2) (Nat.mul_assoc 2 2 (p / 4))
      _ = (3 + (2 * (p / 4)) * 2) / 2 :=
        congrArg (fun x : ℕ => (3 + x) / 2) (Nat.mul_comm 2 (2 * (p / 4)))
      _ = 3 / 2 + 2 * (p / 4) := Nat.add_mul_div_right 3 (2 * (p / 4)) (by decide : 0 < 2)
      _ = 2 * (p / 4) + 1 := by simp only [Nat.reduceDiv, Nat.add_comm]
  have hhalfOdd : Odd (p / 2) := ⟨p / 4, hhalf⟩
  have hpred : p - 1 = 2 * (p / 2) :=
    (Nat.two_mul_odd_div_two (Nat.odd_of_mod_four_eq_three hpMod)).symm
  have hpredNe : p - 1 ≠ 0 := ne_of_gt (Nat.sub_pos_of_lt hpGt)
  have hnot : ¬2 ∣ p / 2 := (Nat.not_even_iff_odd.mpr hhalfOdd) ∘ even_iff_two_dvd.mpr
  have hdiv : Nat.divMaxPow (p - 1) 2 = p / 2 := by
    calc
      Nat.divMaxPow (p - 1) 2 = (Nat.maxPowDvdDiv 2 (p - 1)).2 := rfl
      _ = (1, p / 2).2 :=
        congrArg Prod.snd <|
          Nat.maxPowDvdDiv_of_pow_mul_eq hpredNe (by simpa only [pow_one] using hpred.symm) hnot
      _ = p / 2 := rfl
  obtain ⟨k, hkOdd, hk⟩ := PrimeTest.odd_part_korselt hpGt hpOdd hn hnOdd hpK
  have hpower : Nat.divMaxPow (n - 1) 2 = (p / 2) * k := by
    calc
      Nat.divMaxPow (n - 1) 2 = Nat.divMaxPow (p - 1) 2 * k := hk
      _ = (p / 2) * k := congrArg (fun d : ℕ => d * k) hdiv
  rw [hpower]
  have hb0 : ((b : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    apply hbp
    have hZ : (p : ℤ) ∣ (b : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (b : ℤ) p).mp hz
    exact Int.natCast_dvd_natCast.mp hZ
  simpa only [Int.cast_natCast] using
    PrimeTest.pow_half_mul_odd_eq_legendre (a := (b : ℤ)) hb0 hkOdd

open PseudoPrime.NumberTheory in
/--
Inputs: `n` is nonzero and squarefree, `b` is positive, and each prime divisor
of `n` gives the same sign `σ` for the `d`-th power of `b` modulo that prime.

Claim: the same power equals `σ` modulo `n`.

Content: for sign `1`, each prime divides `b^d - 1`; for sign `-1`, each prime
divides `b^d + 1`. Squarefreeness lifts the corresponding divisibility to `n`.

Proof: translate the prime-modulus equalities to vanishing casts, apply
`dvd_of_squarefree_prime_dvd`, and translate the resulting divisibility back.

Role: this is the primewise-to-global step that turns a common Legendre sign into
the residual power equality used by the strong Miller–Rabin criterion.
-/
theorem residual_power_eq_sign_of_squarefree {n b d : ℕ} {σ : ℤ} (hn : Squarefree n) (hn0 : n ≠ 0)
    (hb : 0 < b) (hσ : σ = 1 ∨ σ = -1)
    (hlocal : ∀ p : ℕ, Nat.Prime p → p ∣ n → (b : ZMod p) ^ d = (σ : ZMod p)) :
    (b : ZMod n) ^ d = (σ : ZMod n) := by
  rcases hσ with hσ | hσ
  · subst σ
    have hpowpos : 1 ≤ b ^ d := Nat.one_le_pow d b hb
    have hdiv : n ∣ b ^ d - 1 := by
      apply dvd_of_squarefree_prime_dvd hn hn0
      intro p hp hpn
      have hlocalp := hlocal p hp hpn
      have hcast : ((b ^ d : ℕ) : ZMod p) = 1 := by
        simpa only [Nat.cast_pow, Nat.cast_one, Int.cast_one] using hlocalp
      have hzero : ((b ^ d - 1 : ℕ) : ZMod p) = 0 := by
        rw [Nat.cast_sub hpowpos, hcast, Nat.cast_one, sub_self]
      exact (ZMod.natCast_eq_zero_iff (b ^ d - 1) p).mp hzero
    have hglobalzero : ((b ^ d - 1 : ℕ) : ZMod n) = 0 :=
      (ZMod.natCast_eq_zero_iff (b ^ d - 1) n).mpr hdiv
    have hglobal : ((b ^ d : ℕ) : ZMod n) = 1 := by
      rw [Nat.cast_sub hpowpos] at hglobalzero
      have hsub : ((b ^ d : ℕ) : ZMod n) - 1 = 0 := by simpa only [Nat.cast_one] using hglobalzero
      exact sub_eq_zero.mp hsub
    simpa only [Nat.cast_pow, Int.cast_one] using hglobal
  · subst σ
    have hdiv : n ∣ b ^ d + 1 := by
      apply dvd_of_squarefree_prime_dvd hn hn0
      intro p hp hpn
      have hlocalp := hlocal p hp hpn
      have hzero : ((b ^ d + 1 : ℕ) : ZMod p) = 0 := by
        rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one, hlocalp]
        simp only [Int.cast_neg, Int.cast_one, neg_add_cancel]
      exact (ZMod.natCast_eq_zero_iff (b ^ d + 1) p).mp hzero
    have hglobalzero : ((b ^ d + 1 : ℕ) : ZMod n) = 0 :=
      (ZMod.natCast_eq_zero_iff (b ^ d + 1) n).mpr hdiv
    have hglobal : ((b ^ d : ℕ) : ZMod n) = -1 := by
      rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one] at hglobalzero
      have hsum : ((b ^ d : ℕ) : ZMod n) + 1 = 0 := by simpa only [Nat.cast_pow] using hglobalzero
      exact (eq_neg_iff_add_eq_zero).mpr hsum
    simpa only [Nat.cast_pow, Int.cast_neg, Int.cast_one] using hglobal

/--
Inputs: `n` is odd, greater than one, and squarefree; `b` is positive and is
nonzero modulo every prime divisor of `n`; those primes are `3 mod 4`, satisfy
Korselt divisibility, and give one common Legendre sign for `b`.

Claim: `b` passes the strong Miller–Rabin test modulo `n`.

Content: the local Euler criterion identifies each residual power with its
Legendre sign. Squarefreeness lifts that common sign to `ZMod n`.

Proof: apply `residual_power_eq_legendre_at_prime` at every prime divisor, lift
with `residual_power_eq_sign_of_squarefree`, then use the global sign criterion.

Role: this packages the local and squarefree arithmetic needed by the AGP
construction once its Carmichael factors and common sign have been supplied.
-/
theorem strongMillerRabinPass_of_common_legendre_sign {n b : ℕ} (hn : 1 < n) (hnOdd : Odd n)
    (hnSquarefree : Squarefree n) (hn0 : n ≠ 0) (hb : 0 < b)
    (hpMod : ∀ p : ℕ, Nat.Prime p → p ∣ n → p % 4 = 3)
    (hpK : ∀ p : ℕ, Nat.Prime p → p ∣ n → p - 1 ∣ n - 1)
    (hbp : ∀ p : ℕ, Nat.Prime p → p ∣ n → ¬p ∣ b) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (hleg : ∀ p : ℕ, (hp : Nat.Prime p) → p ∣ n → @legendreSym p ⟨hp⟩ b = σ) :
    PrimeTest.StrongMillerRabinPass n (b : ZMod n) := by
  have hlocal :
    ∀ p : ℕ, Nat.Prime p → p ∣ n → (b : ZMod p) ^ Nat.divMaxPow (n - 1) 2 = (σ : ZMod p) := by
    intro p hp hpn
    calc
      (b : ZMod p) ^ Nat.divMaxPow (n - 1) 2 = ((@legendreSym p ⟨hp⟩ b) : ZMod p) :=
        @residual_power_eq_legendre_at_prime n p b hn hnOdd ⟨hp⟩ (hpMod p hp hpn) (hpK p hp hpn)
          (hbp p hp hpn)
      _ = (σ : ZMod p) := congrArg (fun z : ℤ => (z : ZMod p)) (hleg p hp hpn)
  have hglobal := residual_power_eq_sign_of_squarefree hnSquarefree hn0 hb hσ hlocal
  rcases hσ with hσ | hσ
  · rw [hσ] at hglobal
    exact
      strongMillerRabinPass_of_residual_power_eq_sign hn hnOdd
        (Or.inl (by simpa only [Int.cast_one] using hglobal))
  · rw [hσ] at hglobal
    exact
      strongMillerRabinPass_of_residual_power_eq_sign hn hnOdd
        (Or.inr (by simpa only [Int.cast_neg, Int.cast_one] using hglobal))

/--
Inputs: a finite base set `W`; an odd, squarefree modulus greater than one;
prime factors congruent to `3 mod 4` satisfying Korselt divisibility; and for
each base in `W`, nonzero local residues with one common Legendre sign.

Claim: every base in `W` passes the strong Miller–Rabin test modulo `n`.

Content: the preceding one-base criterion applies independently to every
member of the finite set.

Proof: choose the supplied sign for each base and apply
`strongMillerRabinPass_of_common_legendre_sign`.

Role: this closes P1's finite-base interface under the local conditions used by
the AGP construction; establishing those conditions is the responsibility of P2.
-/
theorem strongMillerRabinPass_all_of_common_legendre_sign {n : ℕ} (W : Finset ℕ) (hn : 1 < n)
    (hnOdd : Odd n) (hnSquarefree : Squarefree n) (hn0 : n ≠ 0)
    (hpMod : ∀ p : ℕ, Nat.Prime p → p ∣ n → p % 4 = 3)
    (hpK : ∀ p : ℕ, Nat.Prime p → p ∣ n → p - 1 ∣ n - 1) (hbase : ∀ b ∈ W, 0 < b)
    (hbp : ∀ b ∈ W, ∀ p : ℕ, Nat.Prime p → p ∣ n → ¬p ∣ b)
    (hcommon :
      ∀ b ∈ W,
        ∃ σ : ℤ,
          (σ = 1 ∨ σ = -1) ∧ ∀ p : ℕ, (hp : Nat.Prime p) → p ∣ n → @legendreSym p ⟨hp⟩ b = σ) :
    ∀ b ∈ W, PrimeTest.StrongMillerRabinPass n (b : ZMod n) := by
  intro b hb
  obtain ⟨σ, hσ, hleg⟩ := hcommon b hb
  exact
    strongMillerRabinPass_of_common_legendre_sign hn hnOdd hnSquarefree hn0 (hbase b hb) hpMod hpK
      (hbp b hb) hσ hleg

end PseudoPrime.PrimeTest.MillerRabin.AGP
