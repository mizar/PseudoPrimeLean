/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Prime-factor powers bounded by a large modulus

Normalize the cube of each prime by 128 and isolate the four small exceptional primes.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- A prime outside two, three, five and seven is at least eleven.
Finite kernel checks exclude every remaining integer below eleven.
This identifies the exceptions in the normalized cube product. -/
private theorem prime_ge_eleven_of_not_small {p : ℕ} (hp : p.Prime)
    (hn : p ∉ ({2, 3, 5, 7} : Finset ℕ)) : 11 ≤ p := by
  by_contra hh
  have hhi : p ≤ 10 := Nat.le_of_lt_succ (Nat.lt_of_not_ge hh)
  have hlo : 2 ≤ p := hp.two_le
  interval_cases p <;>
    first
    | exact hn (by decide)
    | exact (by decide : ¬Nat.Prime _) hp

/-- For at least six distinct primes, the product of their cubes divided by 128
is at least one. Normalize further by ten and isolate two, three, five and seven.
Their fixed product and the cardinality bound control the unrestricted product.
This gives the prime-factor estimate used in LLS Section 4.1. -/
theorem prod_prime_cube_ratios_ge_one (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) (hc : 6 ≤ s.card) :
    (1 : ℚ) ≤ ∏ p ∈ s, ((p : ℚ) ^ 3 / 128) := by
  classical
  let t : Finset ℕ := {2, 3, 5, 7}
  let v : ℕ → ℚ := fun p ↦ if p ∈ t then (p : ℚ) ^ 3 / 128 / 10 else 1
  have hv : ∀ p ∈ t, 0 ≤ v p ∧ v p ≤ 1 := by
    intro p hpt
    have he : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
      simpa only [t, Finset.mem_insert, Finset.mem_singleton] using hpt
    rcases he with rfl | rfl | rfl | rfl <;>
      norm_num only [v, t, Finset.mem_insert, Finset.mem_singleton, ite_true, ite_false, or_true,
        true_or, false_or, or_false, true_and]
  have hv0 : ∀ p, 0 ≤ v p := by
    intro p
    by_cases hpt : p ∈ t
    · exact (hv p hpt).1
    · simp only [v, ite_eq_right hpt, zero_le_one]
  have hpoint : ∀ p ∈ s, (10 : ℚ) * v p ≤ (p : ℚ) ^ 3 / 128 := by
    intro p hps
    by_cases hpt : p ∈ t
    · simp only [v, ite_eq_left hpt]
      ring_nf
      exact le_rfl
    · have hb : (11 : ℚ) ≤ p := Nat.cast_le.mpr (prime_ge_eleven_of_not_small (hp p hps) hpt)
      have hh := pow_le_pow_left₀ (by norm_num only : (0 : ℚ) ≤ 11) hb 3
      simp only [v, ite_eq_right hpt, mul_one]
      norm_num only at hh
      linarith only [hh]
  have hprod :=
    Finset.prod_le_prod₀ (fun p _ ↦ mul_nonneg (by norm_num only : (0 : ℚ) ≤ 10) (hv0 p)) hpoint
  rw [Finset.prod_mul_distrib, Finset.prod_const] at hprod
  have hvt : (∏ p ∈ t, v p) ≤ ∏ p ∈ s ∩ t, v p :=
    Finset.prod_le_prod_of_subset_of_le_one₀ Finset.inter_subset_right (fun p hpt ↦ (hv p hpt).1)
      (fun p hpt _ ↦ (hv p hpt).2)
  have hvs : (∏ p ∈ t, v p) ≤ ∏ p ∈ s, v p := by
    simpa only [v, Finset.prod_ite_mem, Finset.inter_assoc, Finset.inter_self] using hvt
  have ht : (∏ p ∈ t, v p) = (210 : ℚ) ^ 3 / 128 ^ 4 / 10 ^ 4 := by
    norm_num only [v, t, Finset.prod_insert, Finset.prod_singleton, Finset.mem_insert,
      Finset.mem_singleton, ite_true, ite_false, or_true, true_or, false_or, or_false,
      not_false_eq_true]
  have hpow : (10 : ℚ) ^ 6 ≤ (10 : ℚ) ^ s.card := pow_le_pow_right₀ (by norm_num only) hc
  have hh :=
    mul_le_mul hpow hvs
      (by
        rw [ht]; norm_num only : (0 : ℚ) ≤ ∏ p ∈ t, v p)
      (pow_nonneg (by norm_num only : (0 : ℚ) ≤ 10) _)
  rw [ht] at hh
  norm_num only at hh
  exact (by norm_num only : (1 : ℚ) ≤ 28940625 / 8388608).trans (hh.trans hprod)

/-- For a modulus at least twenty thousand, two to seven times its prime-factor count
is at most the cube of the modulus. With at most five factors use the modulus cutoff;
otherwise apply the normalized prime product and its divisibility into the modulus.
This is the integer-power form of the LLS Section 4.1 prime-factor bound. -/
theorem two_pow_seven_card_primeFactors_le_cube {q : ℕ} (hq : 20000 ≤ q) :
    2 ^ (7 * q.primeFactors.card) ≤ q ^ 3 := by
  by_cases hc : q.primeFactors.card ≤ 5
  · exact
      (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (Nat.mul_le_mul_left 7 hc)).trans
        ((by decide : 2 ^ (7 * 5) ≤ 20000 ^ 3).trans
          (pow_le_pow_left₀ (by decide : 0 ≤ (20000 : ℕ)) hq 3))
  · have h6 : 6 ≤ q.primeFactors.card := Nat.le_of_not_lt (fun hh ↦ hc (Nat.le_of_lt_succ hh))
    have hb :=
      prod_prime_cube_ratios_ge_one q.primeFactors (fun _ hp ↦ Nat.prime_of_mem_primeFactors hp) h6
    rw [Finset.prod_div_distrib, Finset.prod_pow, Finset.prod_const] at hb
    have hm := (le_div_iff₀ (pow_pos (by norm_num only : (0 : ℚ) < 128) _)).mp hb
    rw [one_mul, ← Nat.cast_prod] at hm
    have hn : (128 : ℕ) ^ q.primeFactors.card ≤ (∏ p ∈ q.primeFactors, p) ^ 3 := by
      apply (Nat.cast_le (α := ℚ)).mp
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hm
    rw [show (128 : ℕ) = 2 ^ 7 by decide, ← pow_mul] at hn
    exact
      hn.trans
        (pow_le_pow_left₀ (Nat.zero_le _)
          (Nat.le_of_dvd (lt_of_lt_of_le (by decide) hq) (Nat.prod_primeFactors_dvd q)) 3)

/-- A modulus at least twenty thousand satisfies the prime-factor bound
two to its prime-factor count at most the modulus to the power three sevenths.
Use the proved integer seventh-power comparison and monotonicity of nonnegative
real powers. This is the fractional-power estimate used in LLS Section 4.1. -/
theorem two_pow_card_primeFactors_le_rpow {q : ℕ} (hq : 20000 ≤ q) :
    (2 : ℝ) ^ q.primeFactors.card ≤ (q : ℝ) ^ (3 / 7 : ℝ) := by
  apply
    (Real.rpow_le_rpow_iff (pow_nonneg (by norm_num only) _)
        (Real.rpow_nonneg (Nat.cast_nonneg q) _) (by norm_num only : (0 : ℝ) < 7)).mp
  rw [← Real.rpow_mul (Nat.cast_nonneg q)]
  norm_num only at ⊢
  rw [show (3 : ℝ) = (3 : ℕ) by norm_num only, Real.rpow_natCast]
  rw [show (7 : ℝ) = (7 : ℕ) by norm_num only, Real.rpow_natCast, ← pow_mul]
  have hb : (2 : ℝ) ^ (7 * q.primeFactors.card) ≤ (q : ℝ) ^ 3 := by
    exact_mod_cast two_pow_seven_card_primeFactors_le_cube hq
  simpa only [Nat.mul_comm] using hb

end PseudoPrime.NumberTheory
