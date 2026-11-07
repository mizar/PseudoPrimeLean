/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleSpacingNat
public import PseudoPrime.PrimeTest.MillerRabin.TripleTwoAdic

/-! # Common predecessor valuations and factor gaps -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Two odd numbers above one with equal predecessor 2-adic valuations have
their difference divisible by the next power of two. Their canonical odd
parts differ by an even number; subtract the two decompositions and factor.
This is the common-valuation input for the Korselt gap estimate. -/
theorem two_pow_succ_dvd_sub {p q : ℕ} (hp : 1 < p) (hq : 1 < q) (hpO : Odd p) (hqO : Odd q)
    (hv : padicValNat 2 (p - 1) = padicValNat 2 (q - 1)) :
    2 ^ (padicValNat 2 (p - 1) + 1) ∣ q - p := by
  obtain ⟨_, hpo, hpd⟩ := PrimeTest.odd_sub_canonical_decomp hp hpO
  obtain ⟨_, hqo, hqd⟩ := PrimeTest.odd_sub_canonical_decomp hq hqO
  rw [← hv] at hqd
  have heven := (Nat.Odd.sub_odd hqo hpo).two_dvd
  have hmul := Nat.mul_dvd_mul_left (2 ^ padicValNat 2 (p - 1)) heven
  rw [← pow_succ, Nat.mul_sub_left_distrib, ← hqd, ← hpd,
    Nat.sub_sub_sub_cancel_right hp.le] at hmul
  exact hmul

/-- Three odd factors with equal predecessor valuations have a gap expression
whose 2-adic valuation strictly exceeds that of the middle predecessor.
Both successive differences are divisible by the next power of two, so their
positive gap combination is also divisible by it. This discharges the extra
valuation hypothesis in `triple_spacing_of_val_lt`. -/
theorem triple_gap_val_lt {p q r : ℕ} (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) (hpO : Odd p)
    (hqO : Odd q) (hrO : Odd r) (hpq : p + 2 ≤ q)
    (hv : padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hvr : padicValNat 2 (q - 1) = padicValNat 2 (r - 1)) :
    padicValNat 2 (q - 1) < padicValNat 2 ((q - p) * ((r - q) + 1) - (r - q)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpq' : p ≤ q := by linarith only [hpq]
  have hd2 : 2 ≤ q - p := by
    have h := Nat.sub_add_cancel hpq'
    linarith only [hpq, h]
  have hpos := triple_gap_pos (f := r - q) hd2
  have hd : 2 ^ (padicValNat 2 (q - 1) + 1) ∣ q - p := by
    rw [← hv]
    exact two_pow_succ_dvd_sub hp hq hpO hqO hv
  have hf := two_pow_succ_dvd_sub hq hr hqO hrO hvr
  have ht := Nat.dvd_sub (dvd_mul_of_dvd_left hd ((r - q) + 1)) hf
  have hv' := (padicValNat_dvd_iff_le (Nat.ne_of_gt hpos)).mp ht
  exact Nat.lt_of_succ_le hv'

/-- Ordered odd factors with common predecessor valuations and the middle
Korselt divisibility satisfy the real squared-largest-factor spacing bound.
The preceding valuation theorem discharges the last arithmetic hypothesis;
the result is the input for the logarithmic local-modulus comparison. -/
theorem triple_square_of_korselt {p q r : ℕ} (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) (hpO : Odd p)
    (hqO : Odd q) (hrO : Odd r) (hpq : p + 2 ≤ q) (hqr : q ≤ r)
    (hv : padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hvr : padicValNat 2 (q - 1) = padicValNat 2 (r - 1)) (hk : q - 1 ∣ p * r - 1) :
    (p : ℝ) * q + q * (4 * Real.sqrt ((p : ℝ) - 1) - 2) ≤ (r : ℝ) ^ 2 := by
  have hqr' : q + (r - q) = r := Nat.add_sub_of_le hqr
  have hk' : q - 1 ∣ p * (q + (r - q)) - 1 := by
    rw [hqr']; exact hk
  have hval := triple_gap_val_lt hp hq hr hpO hqO hrO hpq hv hvr
  have h := triple_spacing_of_val_lt hp.le hpq hk' hval
  simpa only [← Nat.cast_add, hqr'] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
