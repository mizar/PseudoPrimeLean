/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.RationalQuotientPowers
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.NumberTheory.PrimeCounting

/-! # Explicit natural-power bounds for divisor and logarithmic losses -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- The exponent controlling the number of prime factors below `2^r`. For `r≥14`,
the wheel of residues coprime to 210 bounds this count by `2^(r-2)`; smaller
orders use the odd-number injection and the bound `2^(r-1)`. -/
def divisorPowerBoundExponent (r : ℕ) : ℕ :=
  if 14 ≤ r then 2 ^ (r - 2) else 2 ^ (r - 1)

/-- The explicit natural constant `(r!*2^r)^e`, where `e` is the proved
upper bound for the number of prime factors below `2^r`. The symbolic definition
avoids evaluating large powers in later coefficient bounds. -/
def divisorPowerBoundConstant (r : ℕ) : ℕ :=
  (r.factorial * 2 ^ r) ^ divisorPowerBoundExponent r

/-- The wheel-based exponent never exceeds the former odd-number count.
This lets general quotient bounds reuse estimates stated for `2^(r-1)`. -/
theorem divisorPowerBoundExponent_le_half (r : ℕ) : divisorPowerBoundExponent r ≤ 2 ^ (r - 1) := by
  by_cases h : 14 ≤ r
  · rw [divisorPowerBoundExponent, ite_eq_left h]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  · rw [divisorPowerBoundExponent, ite_eq_right h]

/-- The refined divisor coefficient is bounded by its earlier half-range form. -/
theorem divisorPowerBoundConstant_le_half (r : ℕ) :
    divisorPowerBoundConstant r ≤ (r.factorial * 2 ^ r) ^ (2 ^ (r - 1)) := by
  unfold divisorPowerBoundConstant
  exact
    Nat.pow_le_pow_right (Nat.mul_pos (Nat.factorial_pos _) (Nat.pow_pos (by decide : 0 < 2)))
      (divisorPowerBoundExponent_le_half r)

/-- The explicit natural constant 8^r*(9*r!)*divisorPowerBoundConstant(2r).
It bounds the r-th power of the quotient-growth coefficient by this constant times U^2.
The constant is independent of U and is retained symbolically. -/
def quotientPowerBoundConstant (r : ℕ) : ℕ :=
  8 ^ r * (9 * r.factorial) * divisorPowerBoundConstant (2 * r)

/-- For arbitrary natural a,r, bound (a+1)^r by r!*2^r*2^a.
Compare with an ascending factorial and bound the corresponding binomial coefficient
by a power of 2. -/
theorem successor_power_le_factorial_exp (a r : ℕ) :
    (a + 1) ^ r ≤ (r.factorial * 2 ^ r) * 2 ^ a := by
  calc
    _ ≤ (a + 1).ascFactorial r := Nat.pow_succ_le_ascFactorial _ _
    _ = r.factorial * (a + r).choose r := Nat.ascFactorial_eq_factorial_mul_choose _ _
    _ ≤ r.factorial * 2 ^ (a + r) := Nat.mul_le_mul_left _ (Nat.choose_le_two_pow _ _)
    _ = _ := by
      rw [pow_add]; ring

/-- For prime p and natural a,r, bound (a+1)^r by p^a, allowing an extra factor r!*2^r
only when p is less than 2^r. Separate small primes from large ones in the divisor product. -/
theorem prime_factor_divisor_power_bound {p : ℕ} (hp : p.Prime) (a r : ℕ) :
    (a + 1) ^ r ≤ (if p < 2 ^ r then r.factorial * 2 ^ r else 1) * p ^ a := by
  by_cases hsmall : p < 2 ^ r
  · rw [ite_eq_left hsmall]
    exact
      (successor_power_le_factorial_exp a r).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp.two_le a))
  · rw [ite_eq_right hsmall, one_mul]
    calc
      _ ≤ (2 ^ a) ^ r := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := a)) r
      _ = (2 ^ r) ^ a := by simp only [← pow_mul, Nat.mul_comm]
      _ ≤ _ := Nat.pow_le_pow_left (Nat.le_of_not_gt hsmall) a

/-- Primes below `2^r` inject into the half-sized range by sending `2` to `0`
and each odd prime `p` to `p/2`. This bounds the number of small prime
factors used in the divisor-power estimate. -/
theorem prime_range_card_le_half {r : ℕ} (hr : 1 ≤ r) :
    ((Finset.range (2 ^ r)).filter Nat.Prime).card ≤ 2 ^ (r - 1) := by
  let S := (Finset.range (2 ^ r)).filter Nat.Prime
  have hpow : 2 * 2 ^ (r - 1) = 2 ^ r := by
    calc
      2 * 2 ^ (r - 1) = 2 ^ (r - 1) * 2 := by ring
      _ = 2 ^ (r - 1 + 1) := (pow_succ 2 (r - 1)).symm
      _ = 2 ^ r := by rw [Nat.sub_add_cancel hr]
  have hcard :=
    Finset.card_le_card_of_injOn (s := S) (t := Finset.range (2 ^ (r - 1)))
      (fun p : ℕ => if p = 2 then 0 else p / 2)
      (by
        intro p hp
        have hmem := Finset.mem_filter.mp hp
        have hpbound : p < 2 ^ r := Finset.mem_range.mp hmem.1
        have hprime := hmem.2
        change (if p = 2 then 0 else p / 2) ∈ Finset.range (2 ^ (r - 1))
        by_cases htwo : p = 2
        · rw [ite_eq_left htwo]
          exact Finset.mem_range.mpr (Nat.pow_pos (by decide : 0 < 2))
        · rw [ite_eq_right htwo]
          apply Finset.mem_range.mpr
          obtain ⟨k, hk⟩ := hprime.odd_of_ne_two htwo
          have hpbound' : 2 * k + 1 < 2 * 2 ^ (r - 1) := by
            calc
              _ = p := hk.symm
              _ < 2 ^ r := hpbound
              _ = 2 * 2 ^ (r - 1) := hpow.symm
          have hdiv : p / 2 = k := Nat.div_eq_of_lt_le (by omega) (by omega)
          rw [hdiv]
          omega)
      (by
        intro x hx y hy hxy
        have hxprime := (Finset.mem_filter.mp hx).2
        have hyprime := (Finset.mem_filter.mp hy).2
        change (if x = 2 then 0 else x / 2) = (if y = 2 then 0 else y / 2) at hxy
        by_cases hxtwo : x = 2
        · subst x
          by_cases hytwo : y = 2
          · subst y
            rfl
          · rw [ite_eq_left rfl, ite_eq_right hytwo] at hxy
            obtain ⟨k, hk⟩ := hyprime.odd_of_ne_two hytwo
            have hygt : 1 < y := hyprime.one_lt
            have hdiv : y / 2 = k := Nat.div_eq_of_lt_le (by omega) (by omega)
            have hk0 : k = 0 := by omega
            rw [hk0] at hk
            rw [hk] at hygt
            norm_num only at hygt
        · by_cases hytwo : y = 2
          · subst y
            rw [ite_eq_right hxtwo, ite_eq_left rfl] at hxy
            obtain ⟨k, hk⟩ := hxprime.odd_of_ne_two hxtwo
            have hxgt : 1 < x := hxprime.one_lt
            have hdiv : x / 2 = k := Nat.div_eq_of_lt_le (by omega) (by omega)
            have hk0 : k = 0 := by omega
            rw [hk0] at hk
            rw [hk] at hxgt
            norm_num only at hxgt
          · rw [ite_eq_right hxtwo, ite_eq_right hytwo] at hxy
            obtain ⟨kx, hkx⟩ := hxprime.odd_of_ne_two hxtwo
            obtain ⟨ky, hky⟩ := hyprime.odd_of_ne_two hytwo
            have hxdiv : x / 2 = kx := Nat.div_eq_of_lt_le (by omega) (by omega)
            have hydiv : y / 2 = ky := Nat.div_eq_of_lt_le (by omega) (by omega)
            omega)
  simpa only [Finset.card_range] using hcard

/-- The wheel modulo 210 bounds the number of primes below `2^r` by `2^(r-2)`.
Every prime above 7 is coprime to 210; `Nat.primeCounting'_add_le` counts
such integers by the 48 reduced residue classes in each block of 210. -/
theorem prime_range_card_le_quarter {r : ℕ} (hr : 14 ≤ r) :
    ((Finset.range (2 ^ r)).filter Nat.Prime).card ≤ 2 ^ (r - 2) := by
  let q : ℕ := (2 ^ r - 211) / 210 + 1
  have hN : 211 ≤ 2 ^ r := by
    calc
      211 ≤ 2 ^ 14 := by decide
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by decide : 0 < 2) hr
  have hpi : Nat.primeCounting' 211 ≤ 211 := by
    rw [Nat.primeCounting', Nat.count_eq_card_filter_range]
    exact Finset.card_filter_le _ _
  have htotient : Nat.totient (210 : ℕ) = 48 := by decide
  have hcount : ((Finset.range (2 ^ r)).filter Nat.Prime).card = Nat.primeCounting' (2 ^ r) := by
    rw [Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hpc := Nat.primeCounting'_add_le (a := 210) (k := 211) (by decide) (by decide) (2 ^ r - 211)
  rw [Nat.add_sub_of_le hN] at hpc
  have hbound : ((Finset.range (2 ^ r)).filter Nat.Prime).card ≤ 211 + 48 * q := by
    rw [hcount]
    calc
      Nat.primeCounting' (2 ^ r) ≤
          Nat.primeCounting' 211 + Nat.totient 210 * ((2 ^ r - 211) / 210 + 1) :=
        hpc
      _ ≤ 211 + 48 * q := by
        rw [htotient]
        dsimp only [q]
        exact Nat.add_le_add_right hpi _
  have hquot : 210 * q ≤ 2 ^ r - 1 := by
    dsimp only [q]
    have hdiv := Nat.div_mul_le_self (2 ^ r - 211) 210
    omega
  have hNlarge : 10000 ≤ 2 ^ r := by
    calc
      10000 ≤ 2 ^ 14 := by decide
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by decide : 0 < 2) hr
  have hquarter : 4 * (211 + 48 * q) ≤ 2 ^ r := by omega
  have hpow : 2 ^ r = 4 * 2 ^ (r - 2) := by
    calc
      2 ^ r = 2 ^ ((r - 2) + 2) := by
        congr 1; omega
      _ = 2 ^ (r - 2) * 2 ^ 2 := pow_add 2 (r - 2) 2
      _ = 4 * 2 ^ (r - 2) := by
        norm_num only [pow_two]; ring
  rw [hpow] at hquarter
  omega

/-- For nonzero natural a and arbitrary r, the r-th power of its divisor count is at most
(r!*2^r)^(2^(r-1))*a. Multiply the local prime-factor bounds and count small primes
by the number of odd positions below 2^r,
and reconstruct a from its factorization. No asymptotic theorem is assumed. -/
theorem divisors_card_pow_le_explicit {a : ℕ} (ha : a ≠ 0) (r : ℕ) :
    a.divisors.card ^ r ≤ divisorPowerBoundConstant r * a := by
  by_cases hr : r = 0
  · subst r
    have hC : divisorPowerBoundConstant 0 = 1 := by decide
    rw [hC]
    simp only [pow_zero, one_mul]
    exact Nat.one_le_iff_ne_zero.mpr ha
  classical
  let D := r.factorial * 2 ^ r
  have hD : 0 < D := Nat.mul_pos (Nat.factorial_pos _) (Nat.pow_pos (by decide : 0 < 2))
  have hrpos : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr
  have hprimes : ((Finset.range (2 ^ r)).filter Nat.Prime).card ≤ divisorPowerBoundExponent r := by
    by_cases hquarter : 14 ≤ r
    · rw [divisorPowerBoundExponent, ite_eq_left hquarter]
      exact prime_range_card_le_quarter hquarter
    · rw [divisorPowerBoundExponent, ite_eq_right hquarter]
      exact prime_range_card_le_half hrpos
  have hsubset :
    a.primeFactors.filter (fun p ↦ p < 2 ^ r) ⊆ (Finset.range (2 ^ r)).filter Nat.Prime := by
    intro p hp
    have hmem := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmem.2, Nat.prime_of_mem_primeFactors hmem.1⟩
  have hcard : (a.primeFactors.filter (fun p ↦ p < 2 ^ r)).card ≤ divisorPowerBoundExponent r := by
    have h := Finset.card_le_card hsubset
    exact h.trans hprimes
  rw [Nat.card_divisors ha, ← Finset.prod_pow]
  calc
    _ ≤ ∏ p ∈ a.primeFactors, (if p < 2 ^ r then D else 1) * p ^ a.factorization p :=
      Finset.prod_le_prod
        (fun p hp ↦ prime_factor_divisor_power_bound (Nat.prime_of_mem_primeFactors hp) _ r)
    _ =
        (∏ p ∈ a.primeFactors, if p < 2 ^ r then D else 1) *
          (∏ p ∈ a.primeFactors, p ^ a.factorization p) :=
      Finset.prod_mul_distrib
    _ = D ^ (a.primeFactors.filter (fun p ↦ p < 2 ^ r)).card * a := by
      rw [Finset.prod_ite, ← Nat.prod_primeFactors_pow_factorization ha]
      simp only [Finset.prod_const, one_pow, mul_one]
    _ ≤ _ := Nat.mul_le_mul_right a (Nat.pow_le_pow_right hD hcard)
    _ = divisorPowerBoundConstant r * a := by simp only [divisorPowerBoundConstant, D]

/-- For natural U and positive r, the r-th power of the maximum divisor count up to U is at most
(r!*2^r)^(2^(r-1))*U. Choose an actual maximizing index and handle index zero separately. -/
theorem maxDivisorCount_pow_le_explicit (U : ℕ) {r : ℕ} (hr : 0 < r) :
    maxDivisorCount U ^ r ≤ divisorPowerBoundConstant r * U := by
  obtain ⟨a, ha, he⟩ :=
    Finset.exists_mem_eq_sup (Finset.range (U + 1)) ⟨0, Finset.mem_range.mpr (Nat.succ_pos U)⟩
      (fun a : ℕ ↦ a.divisors.card)
  change maxDivisorCount U = a.divisors.card at he
  rw [he]
  by_cases hz : a = 0
  · rw [hz, Nat.divisors_zero, Finset.card_empty, zero_pow (ne_of_gt hr)]
    exact Nat.zero_le _
  · exact
      (divisors_card_pow_le_explicit hz r).trans
        (Nat.mul_le_mul_left _ (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)))

/-- For positive natural U and arbitrary r, ceil(1+log U)^r is at most 9*r!*U.
Bound the ceiling by log U+2, use the exponential Taylor term and exp(2) at most 9. -/
theorem ceiling_log_power_le {U : ℕ} (hU : 0 < U) (r : ℕ) :
    Nat.ceil (1 + Real.log (U : ℝ)) ^ r ≤ (9 * r.factorial) * U := by
  have hu : (0 : ℝ) < U := Nat.cast_pos.mpr hU
  have hl := Real.log_nonneg (Nat.one_le_cast.mpr hU)
  have hk := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 1 + Real.log U by linarith only [hl])).le
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (Nat.ceil (1 + Real.log (U : ℝ)))) hk r
  have hshift : 1 + Real.log (U : ℝ) + 1 = Real.log (U : ℝ) + 2 := by ring
  rw [hshift] at hpow
  have hfac :=
    (div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos r))).mp
      (Real.pow_div_factorial_le_exp (Real.log U + 2) (by linarith only [hl]) r)
  have he2 : Real.exp (2 : ℝ) ≤ 9 := by
    have hs := mul_self_le_mul_self (Real.exp_pos (1 : ℝ)).le Real.exp_one_lt_three.le
    rw [show (2 : ℝ) = 1 + 1 from by norm_num only, Real.exp_add]
    norm_num only at hs
    exact hs
  have he := mul_le_mul_of_nonneg_left he2 hu.le
  rw [Real.exp_add, Real.exp_log hu] at hfac
  have hmul := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg r.factorial)
  have hout : (Nat.ceil (1 + Real.log (U : ℝ)) : ℝ) ^ r ≤ ((9 * r.factorial) * U : ℕ) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at *
    nlinarith only [hpow, hfac, hmul]
  apply Nat.cast_le (α := ℝ).mp
  simpa only [Nat.cast_pow] using hout

/-- For positive U,r, bound quotientPowerConstant(U)^r by quotientPowerBoundConstant(r)*U^2,
with the latter constant written explicitly. Combine the ceiling-log bound and the 2r-th-power
maximum-divisor bound. This permits arbitrarily small height-power losses by increasing r. -/
theorem quotientPowerConstant_pow_le_explicit {U r : ℕ} (hU : 0 < U) (hr : 0 < r) :
    quotientPowerConstant U ^ r ≤ quotientPowerBoundConstant r * U ^ 2 := by
  have hk := ceiling_log_power_le hU r
  have ht := maxDivisorCount_pow_le_explicit U (Nat.mul_pos (by decide : 0 < 2) hr)
  have hm := Nat.mul_le_mul_left (8 ^ r) (Nat.mul_le_mul hk ht)
  simpa only [quotientPowerConstant, quotientPowerBoundConstant, divisorPowerBoundConstant, mul_pow,
    pow_mul, pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hm

end PseudoPrime.NumberTheory.Heilbronn
