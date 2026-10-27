/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactorSplitBounds

/-! # Distinct prime counts retaining the logarithmic deficits of small primes -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For positive q at most A, a nonnegative logarithmic coefficient a, and a finite set of
prime exceptions with nonnegative deficits d, the number of distinct prime factors is at most
a log A plus the total exceptional deficit. Sum the per-prime inequality before enlarging the
logarithmic prime support. This retains small-prime logarithms instead of counting every small
integer as a possible prime. -/
theorem primeFactors_card_le_log_deficit {q A : ℕ} (hq : 0 < q) (hqA : q ≤ A) {a : ℝ} (ha : 0 ≤ a)
    (S : Finset ℕ) (d : ℕ → ℝ) (hd : ∀ p ∈ S, 0 ≤ d p)
    (hp : ∀ p : ℕ, p.Prime → (1 : ℝ) ≤ a * Real.log p + if p ∈ S then d p else 0) :
    (q.primeFactors.card : ℝ) ≤ a * Real.log A + ∑ p ∈ S, d p := by
  classical
  have hs :=
    Finset.sum_le_sum (s := q.primeFactors) (fun p h ↦ hp p (Nat.prime_of_mem_primeFactors h))
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_add_distrib, ← Finset.mul_sum, ←
    Finset.sum_filter] at hs
  have he : q.primeFactors.filter (fun p ↦ p ∈ S) ⊆ S := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hb := Finset.sum_le_sum_of_subset_of_nonneg he (fun p hp _ ↦ hd p hp)
  have hl :=
    (sum_log_primeFactors_le_log hq.ne').trans
      (Real.log_le_log (Nat.cast_pos.mpr hq) (Nat.cast_le.mpr hqA))
  have hm := mul_le_mul_of_nonneg_left hl ha
  exact hs.trans (add_le_add hm hb)

/-- For a positive natural p at most thirteen, log p is at most eight thirds. Use the tangent
at sixteen and the certified upper bound for log two. This proves nonnegativity of the six
exceptional prime deficits using one uniform real-variable estimate. -/
theorem log_natCast_le_eight_thirds_of_le_thirteen {p : ℕ} (hp : 0 < p) (hp13 : p ≤ 13) :
    Real.log p ≤ 8 / 3 := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have ht := Real.log_le_sub_one_of_pos (div_pos hp0 (by norm_num only : (0 : ℝ) < 16))
  rw [Real.log_div hp0.ne' (by norm_num only : (16 : ℝ) ≠ 0),
    show (16 : ℝ) = 2 ^ 4 by norm_num only, Real.log_pow] at ht
  norm_num only [Nat.cast_ofNat] at ht
  have hp13r : (p : ℝ) ≤ 13 := Nat.cast_le.mpr hp13
  linarith only [ht, hp13r, Real.log_two_lt_d9]

/-- At the six primes below sixteen, the deficit 1-(3/8) log p is nonnegative. Apply the
uniform logarithm bound for positive naturals through thirteen. These signs permit replacing
the exceptional factors actually dividing q by the entire fixed exception set. -/
theorem prime_log_deficit_six_nonneg :
    ∀ p ∈ ({2,3,5,7,11,13} : Finset ℕ), 0 ≤ 1 - (3 / 8 : ℝ) * Real.log p := by
  intro p hp
  have hr : ∀ p ∈ ({2,3,5,7,11,13} : Finset ℕ), 0 < p ∧ p ≤ 13 := by decide
  have hl := log_natCast_le_eight_thirds_of_le_thirteen (hr p hp).1 (hr p hp).2
  linarith only [hl]

/-- The sum of 1-(3/8) log p over the six primes below sixteen is at most five halves. Keep
all six logarithms, compare seven with five and eleven and thirteen with nine, and use the
certified logarithms of two, three and five. This is the only fixed finite cost in the uniform
prime-count estimate. -/
theorem prime_log_deficit_six_sum :
    (∑ p ∈ ({2,3,5,7,11,13} : Finset ℕ), (1 - (3 / 8 : ℝ) * Real.log p)) ≤ 5 / 2 := by
  have h9 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have h11 := Real.log_le_log (by norm_num only : (0 : ℝ) < 9) (by norm_num only : (9 : ℝ) ≤ 11)
  have h13 := Real.log_le_log (by norm_num only : (0 : ℝ) < 9) (by norm_num only : (9 : ℝ) ≤ 13)
  have h7 := Real.log_le_log (by norm_num only : (0 : ℝ) < 5) (by norm_num only : (5 : ℝ) ≤ 7)
  rw [h9] at h11 h13
  rw [Finset.sum_insert (by decide : (2 : ℕ) ∉ {3,5,7,11,13}),
    Finset.sum_insert (by decide : (3 : ℕ) ∉ {5,7,11,13}),
    Finset.sum_insert (by decide : (5 : ℕ) ∉ {7,11,13}),
    Finset.sum_insert (by decide : (7 : ℕ) ∉ {11,13}),
    Finset.sum_insert (by decide : (11 : ℕ) ∉ {13}), Finset.sum_singleton]
  norm_num only [Nat.cast_ofNat]
  linarith only [h11, h13, h7, Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]

/-- Every prime is charged at most by its logarithmic contribution (3/8) log p and its
nonnegative deficit if it belongs to the six-prime exception set. Outside the set, p is at
least sixteen and log sixteen exceeds eight thirds. This supplies the per-prime hypothesis
for the generic logarithmic-deficit estimate. -/
theorem prime_log_deficit_six_prime_bound {p : ℕ} (hp : p.Prime) :
    (1 : ℝ) ≤
      (3 / 8 : ℝ) * Real.log p +
        if p ∈ ({2,3,5,7,11,13} : Finset ℕ) then 1 - (3 / 8 : ℝ) * Real.log p else 0 := by
  by_cases hs : p ∈ ({2,3,5,7,11,13} : Finset ℕ)
  · rw [ite_eq_left hs]
    linarith only
  · rw [ite_eq_right hs, add_zero]
    have hsmall : ∀ p ∈ Finset.range 16, p.Prime → p ∈ ({2,3,5,7,11,13} : Finset ℕ) := by decide
    have hbig : 16 ≤ p := by
      by_contra h
      exact hs (hsmall p (Finset.mem_range.mpr (lt_of_not_ge h)) hp)
    have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 16) (Nat.cast_le.mpr hbig)
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num only, Real.log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    linarith only [hl, Real.log_two_gt_d9]

/-- For positive q at most A, its distinct prime count is at most 5/2+(3/8) log A. Apply the
generic finite-deficit theorem to the six primes below sixteen. No hypothesis on the size of
the logarithm, squarefreeness, parity or RH is needed. This removes the coarse cutoff cost
sixteen from small-scale local budgets. -/
theorem primeFactors_card_le_five_halves_add_three_eighths_log {q A : ℕ} (hq : 0 < q)
    (hqA : q ≤ A) : (q.primeFactors.card : ℝ) ≤ 5 / 2 + (3 / 8 : ℝ) * Real.log A := by
  have h :=
    primeFactors_card_le_log_deficit hq hqA (by norm_num only : (0 : ℝ) ≤ 3 / 8)
      ({2,3,5,7,11,13} : Finset ℕ) (fun p ↦ 1 - (3 / 8 : ℝ) * Real.log p)
      prime_log_deficit_six_nonneg (fun p hp ↦ prime_log_deficit_six_prime_bound hp)
  linarith only [h, prime_log_deficit_six_sum]

/-- For positive q at most A with log A at least twenty, its distinct prime count is at
most log A divided by two. Absorb the retained deficit five halves into the logarithm. This
supplies the half-logarithm budget at smaller analytic scales. -/
theorem primeFactors_card_le_half_log_of_twenty {q A : ℕ} (hq : 0 < q) (hqA : q ≤ A)
    (hL : 20 ≤ Real.log A) : (q.primeFactors.card : ℝ) ≤ Real.log A / 2 := by
  have h := primeFactors_card_le_five_halves_add_three_eighths_log hq hqA
  linarith only [h, hL]

/-- For positive q at most A with log A at least one hundred, its distinct prime count is at
most two fifths of log A. Absorb the finite deficit in the generic affine estimate. This is the
factor-count input for smaller-scale negative-witness comparisons. -/
theorem primeFactors_card_le_two_fifths_log_of_hundred {q A : ℕ} (hq : 0 < q) (hqA : q ≤ A)
    (hL : 100 ≤ Real.log A) : (q.primeFactors.card : ℝ) ≤ (2 / 5 : ℝ) * Real.log A := by
  have h := primeFactors_card_le_five_halves_add_three_eighths_log hq hqA
  linarith only [h, hL]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
