/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaEulerAnchoredBounds
public import PseudoPrime.Analysis.GammaPrimeEulerIntervals

/-! # Mixed small-prime and reciprocal bounds for the Gamma Euler cost -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: an odd prime below 20. Definition: ten certified millionth-grid intervals.
Output: node data, with an empty fallback outside the supported prime set.
Role: keep exact Euler costs only for the few small primes. -/
def gammaMixedEulerRatios (p : ℕ) : ℚ → ℚ × ℚ :=
  smallSeedRatios
    (match p with
    | 3 => [315516, 282690, 239741, 192450, 138414, 89193, 46138, 17165, 4115, 263]
    | 5 => [184536, 157103, 123406, 89442, 55189, 28991, 11037, 2593, 320, 5]
    | 7 => [129612, 106693, 79684, 53994, 30117, 13828, 4302, 746, 59, 0]
    | 11 => [80637, 63445, 44278, 27410, 13350, 5116, 1213, 140, 6, 0]
    | 13 => [67664, 52355, 35634, 21334, 9883, 3542, 760, 75, 2, 0]
    | 17 => [51053, 38457, 25142, 14266, 6098, 1963, 358, 28, 0, 0]
    | 19 => [45426, 33840, 21758, 12074, 4991, 1537, 262, 18, 0, 0]
    | _ => [])

/-- Input: a prime p>=3. Definition: exact signed node allowance below 20, and the
common 71/(100(p-1)) envelope otherwise. Output: a rational Euler upper allowance.
Role: avoid per-prime node tables for all large primes. -/
def gammaMixedEulerUpper (p : ℕ) : ℚ :=
  if 20 ≤ p then (71 / 100 : ℚ) / ((p : ℚ) - 1)
  else gammaPrimeEulerIntervalUpper (gammaMixedEulerRatios p)

/-- Claim: all odd primes below 20 pass the exact signed Euler interval check.
Proof: kernel power arithmetic. Role: certify the small-prime branch of the mixed envelope. -/
theorem gamma_mixed_small_prime_ratios_check :
    ∀ p ∈ (Finset.Icc 3 19).filter Nat.Prime,
      gammaPrimeEulerIntervalCheck p (gammaMixedEulerRatios p) = true := by
  decide +kernel

/-- Input: a prime p>=3. Claim: the actual signed Euler cost is below the mixed allowance.
Proof: use checked node intervals below 20 and the common analytic envelope otherwise.
Role: discharge every row's separate Euler hypothesis without a large data table. -/
theorem gamma_mixed_euler_upper_sound {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) :
    gammaPrimeEulerCost p ≤ (gammaMixedEulerUpper p : ℝ) := by
  by_cases h20 : 20 ≤ p
  · rw [gammaMixedEulerUpper, ite_eq_left h20]
    have h := gamma_prime_euler_cost_le_of_twenty_le (Nat.cast_le.mpr h20 : (20 : ℝ) ≤ p)
    norm_num only [Rat.cast_div, Rat.cast_sub, Rat.cast_natCast, Rat.cast_ofNat] at h ⊢
    exact h
  · have h19 : p ≤ 19 := Nat.le_of_lt_succ (lt_of_not_ge h20)
    have hm : p ∈ (Finset.Icc 3 19).filter Nat.Prime :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h3, h19⟩, hp⟩
    rw [gammaMixedEulerUpper, ite_eq_right h20]
    have h := (gamma_prime_euler_interval_check_sound (gamma_mixed_small_prime_ratios_check p hm)).2
    norm_num only [Rat.cast_natCast] at h
    exact h

end PseudoPrime.Analysis
