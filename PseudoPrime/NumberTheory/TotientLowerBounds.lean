/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Totient
public import PseudoPrime.NumberTheory.TotientPrimeCountBounds
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Totient lower bounds for large moduli

For at most five prime factors use Euler's rational product; for six or more use
the product of prime predecessors. Together they give the LLS Section 4.1 cutoff bound.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- For a finite set of at most five primes, the product of one minus their inverses
is at least sixteen over seventy-seven. Normalize each factor by ten elevenths;
only two, three, five and seven can reduce the normalized product below one.
Their fixed product and the cardinality bound give the lower bound. This is the
arithmetic estimate behind the small-prime-factor case of LLS Section 4.1. -/
theorem prod_totient_factors_ge_of_card_le_five (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime)
    (hc : s.card ≤ 5) : (16 / 77 : ℚ) ≤ ∏ p ∈ s, (1 - (p : ℚ)⁻¹) := by
  exact prod_totient_factors_ge_primeCount_ratio s hp (by decide : 1 ≤ 5) le_rfl hc

/-- A natural number with at most five distinct prime factors has totient at least
sixteen over seventy-seven times the number, as a rational inequality.
Apply the finite prime-factor product bound to Euler's product formula.
This reduces the large-modulus cutoff bound to a numerical inequality. -/
theorem totient_ge_sixteen_seventysevenths {q : ℕ} (hc : q.primeFactors.card ≤ 5) :
    (16 / 77 : ℚ) * q ≤ q.totient := by
  have hb :=
    prod_totient_factors_ge_of_card_le_five q.primeFactors
      (fun _ hp ↦ Nat.prime_of_mem_primeFactors hp) hc
  rw [Nat.totient_eq_mul_prod_factors]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg q)

/-- A modulus at least twenty thousand with at most five distinct prime factors
has totient at least 4156. Combine the rational product bound with the integer
totient's integrality. This proves one of the two arithmetic cases of LLS Section 4.1. -/
theorem totient_ge_4156_of_card_le_five {q : ℕ} (hq : 20000 ≤ q) (hc : q.primeFactors.card ≤ 5) :
    4156 ≤ q.totient := by
  apply Nat.le_of_not_lt
  intro hh
  have ht : q.totient ≤ 4155 := Nat.le_of_lt_succ hh
  have hqR : (20000 : ℚ) ≤ q := Nat.cast_le.mpr hq
  have htR : (q.totient : ℚ) ≤ 4155 := Nat.cast_le.mpr ht
  linarith only [totient_ge_sixteen_seventysevenths hc, hqR, htR]

/-- A prime outside the first five primes is at least thirteen.
Exclude the remaining integers through twelve by finite kernel computation.
This supplies the factor bound for moduli with at least six prime factors. -/
private theorem prime_ge_thirteen_of_not_small {p : ℕ} (hp : p.Prime)
    (hn : p ∉ ({2, 3, 5, 7, 11} : Finset ℕ)) : 13 ≤ p := by
  by_contra hh
  have hhi : p ≤ 12 := Nat.le_of_lt_succ (Nat.lt_of_not_ge hh)
  have hlo : 2 ≤ p := hp.two_le
  interval_cases p <;>
    first
    | exact hn (by decide)
    | exact (by decide : ¬Nat.Prime _) hp

/-- For a finite set of at least six primes, the product of their predecessors
is at least 5760. Normalize the predecessors by twelve; only the first five primes
can reduce the normalized product below one. Their fixed product and the cardinality
bound give the lower estimate used in LLS Section 4.1. -/
theorem prod_prime_predecessors_ge_of_card_ge_six (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime)
    (hc : 6 ≤ s.card) : (5760 : ℚ) ≤ ∏ p ∈ s, ((p : ℚ) - 1) := by
  classical
  let t : Finset ℕ := {2, 3, 5, 7, 11}
  let v : ℕ → ℚ := fun p ↦ if p ∈ t then ((p : ℚ) - 1) / 12 else 1
  have hv : ∀ p ∈ t, 0 ≤ v p ∧ v p ≤ 1 := by
    intro p hpt
    have he : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
      simpa only [t, Finset.mem_insert, Finset.mem_singleton] using hpt
    rcases he with rfl | rfl | rfl | rfl | rfl <;>
      norm_num only [v, t, Finset.mem_insert, Finset.mem_singleton, ite_true, ite_false, or_true,
        true_or, false_or, or_false, true_and]
  have hv0 : ∀ p, 0 ≤ v p := by
    intro p
    by_cases hpt : p ∈ t
    · exact (hv p hpt).1
    · simp only [v, ite_eq_right hpt, zero_le_one]
  have hpoint : ∀ p ∈ s, (12 : ℚ) * v p ≤ (p : ℚ) - 1 := by
    intro p hps
    by_cases hpt : p ∈ t
    · simp only [v, ite_eq_left hpt]
      ring_nf
      exact le_rfl
    · have hb : (13 : ℚ) ≤ p := Nat.cast_le.mpr (prime_ge_thirteen_of_not_small (hp p hps) hpt)
      simp only [v, ite_eq_right hpt, mul_one]
      linarith only [hb]
  have hprod :=
    Finset.prod_le_prod₀ (fun p _ ↦ mul_nonneg (by norm_num only : (0 : ℚ) ≤ 12) (hv0 p)) hpoint
  rw [Finset.prod_mul_distrib, Finset.prod_const] at hprod
  have hvt : (∏ p ∈ t, v p) ≤ ∏ p ∈ s ∩ t, v p :=
    Finset.prod_le_prod_of_subset_of_le_one₀ Finset.inter_subset_right (fun p hpt ↦ (hv p hpt).1)
      (fun p hpt _ ↦ (hv p hpt).2)
  have hvs : (∏ p ∈ t, v p) ≤ ∏ p ∈ s, v p := by
    simpa only [v, Finset.prod_ite_mem, Finset.inter_assoc, Finset.inter_self] using hvt
  have ht : (∏ p ∈ t, v p) = (480 : ℚ) / 12 ^ 5 := by
    norm_num only [v, t, Finset.prod_insert, Finset.prod_singleton, Finset.mem_insert,
      Finset.mem_singleton, ite_true, ite_false, or_true, true_or, false_or, or_false,
      not_false_eq_true]
  have hpow : (12 : ℚ) ^ 6 ≤ (12 : ℚ) ^ s.card := pow_le_pow_right₀ (by norm_num only) hc
  have hh :=
    mul_le_mul hpow hvs
      (by
        rw [ht]; norm_num only : (0 : ℚ) ≤ ∏ p ∈ t, v p)
      (pow_nonneg (by norm_num only : (0 : ℚ) ≤ 12) _)
  rw [ht] at hh
  norm_num only at hh
  exact hh.trans hprod

/-- A positive modulus with at least six distinct prime factors has totient at least 5760.
Bound the product of prime predecessors and use Euler's factorization formula,
whose remaining positive integer factor is at least one. This handles the complementary
case in the large-modulus totient bound of LLS Section 4.1. -/
theorem totient_ge_5760_of_card_ge_six {q : ℕ} (hq : 0 < q) (hc : 6 ≤ q.primeFactors.card) :
    5760 ≤ q.totient := by
  have hb :=
    prod_prime_predecessors_ge_of_card_ge_six q.primeFactors
      (fun _ hp ↦ Nat.prime_of_mem_primeFactors hp) hc
  have he : (∏ p ∈ q.primeFactors, (p - 1) : ℕ) ≥ 5760 := by
    apply (Nat.cast_le (α := ℚ)).mp
    rw [Nat.cast_prod]
    have hs : (∏ p ∈ q.primeFactors, ((p - 1 : ℕ) : ℚ)) = ∏ p ∈ q.primeFactors, ((p : ℚ) - 1) := by
      exact
        Finset.prod_congr rfl
          (fun p hp ↦ Nat.cast_sub (Nat.one_le_of_lt (Nat.pos_of_mem_primeFactors hp)))
    rw [hs]
    exact hb
  have hdiv : 1 ≤ q / ∏ p ∈ q.primeFactors, p :=
    Nat.succ_le_of_lt
      (Nat.div_pos (Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q))
        (Finset.prod_pos (fun p hp ↦ Nat.pos_of_mem_primeFactors hp)))
  rw [Nat.totient_eq_div_primeFactors_mul]
  exact he.trans (Nat.le_mul_of_pos_left _ hdiv)

/-- A modulus at least twenty thousand has totient at least 4156.
Split by whether it has at most five distinct prime factors and apply the two
product estimates. This establishes the arithmetic cutoff premise of LLS Section 4.1. -/
theorem totient_ge_4156 {q : ℕ} (hq : 20000 ≤ q) : 4156 ≤ q.totient := by
  by_cases hc : q.primeFactors.card ≤ 5
  · exact totient_ge_4156_of_card_le_five hq hc
  · have h6 : 6 ≤ q.primeFactors.card := Nat.le_of_not_lt (fun hh ↦ hc (Nat.le_of_lt_succ hh))
    exact
      (by decide : 4156 ≤ 5760).trans
        (totient_ge_5760_of_card_ge_six (lt_of_lt_of_le (by decide) hq) h6)

/-- For a modulus at least twenty thousand with at most five prime factors,
the sixth power of its totient is at least the fifth power of the modulus.
Raise the rational linear bound to the sixth power; the modulus lower bound absorbs
its coefficient. This is the few-prime-factor case of the fractional-power estimate
needed in the arithmetic-progression bound. -/
theorem totient_pow_six_ge_pow_five_of_card_le_five {q : ℕ} (hq : 20000 ≤ q)
    (hc : q.primeFactors.card ≤ 5) : q ^ 5 ≤ q.totient ^ 6 := by
  apply (Nat.cast_le (α := ℚ)).mp
  rw [Nat.cast_pow, Nat.cast_pow]
  have hqR : (20000 : ℚ) ≤ q := Nat.cast_le.mpr hq
  have hs : (1 : ℚ) ≤ (16 / 77 : ℚ) ^ 6 * q :=
    (by norm_num only : (1 : ℚ) ≤ (16 / 77 : ℚ) ^ 6 * 20000).trans
      (mul_le_mul_of_nonneg_left hqR (pow_nonneg (by norm_num only) _))
  have hb :=
    pow_le_pow_left₀ (mul_nonneg (by norm_num only : (0 : ℚ) ≤ 16 / 77) (Nat.cast_nonneg q))
      (totient_ge_sixteen_seventysevenths hc) 6
  have hm := mul_le_mul_of_nonneg_right hs (pow_nonneg (Nat.cast_nonneg q : (0 : ℚ) ≤ q) 5)
  calc
    (q : ℚ) ^ 5 ≤ (16 / 77 : ℚ) ^ 6 * (q : ℚ) ^ 6 := by convert hm using 1 <;> ring
    _ ≤ (q.totient : ℚ) ^ 6 := by simpa only [mul_pow] using hb

/-- For at least six distinct primes, the product of the sixth powers of their
predecessors divided by their fifth powers is at least one. Normalize by eight;
only the first five primes reduce a normalized factor below one. Their fixed
product and the cardinality bound give the totient power comparison. -/
theorem prod_totient_power_ratios_ge_one (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) (hc : 6 ≤ s.card) :
    (1 : ℚ) ≤ ∏ p ∈ s, (((p : ℚ) - 1) ^ 6 / (p : ℚ) ^ 5) := by
  classical
  let t : Finset ℕ := {2, 3, 5, 7, 11}
  let v : ℕ → ℚ := fun p ↦ if p ∈ t then (((p : ℚ) - 1) ^ 6 / (p : ℚ) ^ 5) / 8 else 1
  have hv : ∀ p ∈ t, 0 ≤ v p ∧ v p ≤ 1 := by
    intro p hpt
    have he : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
      simpa only [t, Finset.mem_insert, Finset.mem_singleton] using hpt
    rcases he with rfl | rfl | rfl | rfl | rfl <;>
      norm_num only [v, t, Finset.mem_insert, Finset.mem_singleton, ite_true, ite_false, or_true,
        true_or, false_or, or_false, true_and]
  have hv0 : ∀ p, 0 ≤ v p := by
    intro p
    by_cases hpt : p ∈ t
    · exact (hv p hpt).1
    · simp only [v, ite_eq_right hpt, zero_le_one]
  have hpoint : ∀ p ∈ s, (8 : ℚ) * v p ≤ ((p : ℚ) - 1) ^ 6 / (p : ℚ) ^ 5 := by
    intro p hps
    by_cases hpt : p ∈ t
    · simp only [v, ite_eq_left hpt]
      ring_nf
      exact le_rfl
    · have hb : (13 : ℚ) ≤ p := Nat.cast_le.mpr (prime_ge_thirteen_of_not_small (hp p hps) hpt)
      have hp0 : (0 : ℚ) < p := lt_of_lt_of_le (by norm_num only) hb
      have hr : (12 / 13 : ℚ) ≤ ((p : ℚ) - 1) / p := (le_div_iff₀ hp0).mpr (by linarith only [hb])
      have h6 := pow_le_pow_left₀ (by norm_num only : (0 : ℚ) ≤ 12 / 13) hr 6
      have hm :=
        mul_le_mul h6 hb (by norm_num only : (0 : ℚ) ≤ 13)
          (pow_nonneg (div_nonneg (by linarith only [hb]) hp0.le) 6)
      have he : (((p : ℚ) - 1) / p) ^ 6 * p = ((p : ℚ) - 1) ^ 6 / (p : ℚ) ^ 5 := by
        rw [div_pow, show (p : ℚ) ^ 6 = (p : ℚ) ^ 5 * p from pow_succ _ _, div_mul_eq_div_div,
          div_mul_cancel₀ _ hp0.ne']
      rw [he] at hm
      simp only [v, ite_eq_right hpt, mul_one]
      norm_num only at hm
      linarith only [hm]
  have hprod :=
    Finset.prod_le_prod₀ (fun p _ ↦ mul_nonneg (by norm_num only : (0 : ℚ) ≤ 8) (hv0 p)) hpoint
  rw [Finset.prod_mul_distrib, Finset.prod_const] at hprod
  have hvt : (∏ p ∈ t, v p) ≤ ∏ p ∈ s ∩ t, v p :=
    Finset.prod_le_prod_of_subset_of_le_one₀ Finset.inter_subset_right (fun p hpt ↦ (hv p hpt).1)
      (fun p hpt _ ↦ (hv p hpt).2)
  have hvs : (∏ p ∈ t, v p) ≤ ∏ p ∈ s, v p := by
    simpa only [v, Finset.prod_ite_mem, Finset.inter_assoc, Finset.inter_self] using hvt
  have ht : (∏ p ∈ t, v p) = (480 : ℚ) ^ 6 / 2310 ^ 5 / 8 ^ 5 := by
    norm_num only [v, t, Finset.prod_insert, Finset.prod_singleton, Finset.mem_insert,
      Finset.mem_singleton, ite_true, ite_false, or_true, true_or, false_or, or_false,
      not_false_eq_true]
  have hpow : (8 : ℚ) ^ 6 ≤ (8 : ℚ) ^ s.card := pow_le_pow_right₀ (by norm_num only) hc
  have hh :=
    mul_le_mul hpow hvs
      (by
        rw [ht]; norm_num only : (0 : ℚ) ≤ ∏ p ∈ t, v p)
      (pow_nonneg (by norm_num only : (0 : ℚ) ≤ 8) _)
  rw [ht] at hh
  norm_num only at hh
  have hlast := hh.trans hprod
  norm_num only at hlast
  linarith only [hlast]

/-- A positive modulus with at least six prime factors has its fifth power bounded
by the sixth power of its totient. Combine the normalized ratio product with
Euler's product formula and the divisibility of the squarefree prime product.
This is the many-prime-factor case of the LLS Section 4.1 totient estimate. -/
theorem totient_pow_six_ge_pow_five_of_card_ge_six {q : ℕ} (hq : 0 < q)
    (hc : 6 ≤ q.primeFactors.card) : q ^ 5 ≤ q.totient ^ 6 := by
  let f : ℕ → ℚ := fun p ↦ 1 - (p : ℚ)⁻¹
  have hb :=
    prod_totient_power_ratios_ge_one q.primeFactors (fun _ hp ↦ Nat.prime_of_mem_primeFactors hp) hc
  have he :
    (∏ p ∈ q.primeFactors, ((p : ℚ) - 1) ^ 6 / (p : ℚ) ^ 5) =
      (∏ p ∈ q.primeFactors, (p : ℚ)) * (∏ p ∈ q.primeFactors, f p) ^ 6 := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp0 : (0 : ℚ) < p := Nat.cast_pos.mpr (Nat.pos_of_mem_primeFactors hp)
    have hf : f p = ((p : ℚ) - 1) / p := by
      dsimp only [f]
      rw [sub_div, div_self hp0.ne', one_div]
    rw [hf, div_pow, mul_comm, show (p : ℚ) ^ 6 = (p : ℚ) ^ 5 * p from pow_succ _ _,
      div_mul_eq_div_div, div_mul_cancel₀ _ hp0.ne']
  rw [he] at hb
  have hm : (∏ p ∈ q.primeFactors, (p : ℚ)) ≤ q := by
    rw [← Nat.cast_prod]
    exact Nat.cast_le.mpr (Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q))
  have hf0 : (0 : ℚ) ≤ (∏ p ∈ q.primeFactors, f p) ^ 6 := by
    rw [show 6 = 3 * 2 from rfl, pow_mul]
    exact sq_nonneg _
  have hs := hb.trans (mul_le_mul_of_nonneg_right hm hf0)
  have hx := mul_le_mul_of_nonneg_left hs (pow_nonneg (Nat.cast_nonneg q : (0 : ℚ) ≤ q) 5)
  apply (Nat.cast_le (α := ℚ)).mp
  rw [Nat.cast_pow, Nat.cast_pow, Nat.totient_eq_mul_prod_factors, mul_pow]
  change (q : ℚ) ^ 5 ≤ (q : ℚ) ^ 6 * (∏ p ∈ q.primeFactors, f p) ^ 6
  convert hx using 1 <;> ring

/-- For a modulus at least twenty thousand, the fifth power of the modulus is at most
the sixth power of its totient. Split by prime-factor count and combine both product
estimates. This supplies the integer-power form of the LLS fractional totient bound. -/
theorem totient_pow_six_ge_pow_five {q : ℕ} (hq : 20000 ≤ q) : q ^ 5 ≤ q.totient ^ 6 := by
  by_cases hc : q.primeFactors.card ≤ 5
  · exact totient_pow_six_ge_pow_five_of_card_le_five hq hc
  · exact
      totient_pow_six_ge_pow_five_of_card_ge_six (lt_of_lt_of_le (by decide) hq)
        (Nat.le_of_not_lt (fun hh ↦ hc (Nat.le_of_lt_succ hh)))

/-- For a modulus at least twenty thousand, its five-sixths power is at most its totient.
Take the nonnegative sixth-power comparison and use monotonicity of real powers.
This discharges the remaining totient premise in the LLS Section 4.1 comparison. -/
theorem rpow_five_sixths_le_totient {q : ℕ} (hq : 20000 ≤ q) :
    (q : ℝ) ^ (5 / 6 : ℝ) ≤ q.totient := by
  apply
    (Real.rpow_le_rpow_iff (Real.rpow_nonneg (Nat.cast_nonneg q) _) (Nat.cast_nonneg q.totient)
        (by norm_num only : (0 : ℝ) < 6)).mp
  rw [← Real.rpow_mul (Nat.cast_nonneg q)]
  norm_num only at ⊢
  rw [show (5 : ℝ) = (5 : ℕ) by norm_num only, Real.rpow_natCast,
    show (6 : ℝ) = (6 : ℕ) by norm_num only, Real.rpow_natCast]
  exact_mod_cast totient_pow_six_ge_pow_five hq

end PseudoPrime.NumberTheory
