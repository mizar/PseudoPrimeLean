/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.ByContra

/-! # Shared finite prime basis for segmented Chebyshev certificates -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- The precomputed prime bases through one thousand. The increasing
array is shared by the segmented sieve and the higher-power scan. -/
def basePrimes : Array Nat :=
  #[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
    101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
    197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307,
    311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421,
    431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547,
    557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
    661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797,
    809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929,
    937, 941, 947, 953, 967, 971, 977, 983, 991, 997]

/-- Scalar membership query for the shared prime bases. -/
def baseHas (p : ℕ) : Bool :=
  basePrimes.contains p

private def trial (p : ℕ) : Bool :=
  decide (2 ≤ p) && (List.range 32).all fun q ↦ decide (2 ≤ q → q * q ≤ p → ¬q ∣ p)

private theorem trial_iff {p : ℕ} (hu : p < 1001) : trial p = true ↔ p.Prime := by
  simp only [trial, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨hl, ht⟩
    by_contra hc
    have hp := Nat.minFac_prime (show p ≠ 1 by linarith only [hl])
    have hs := Nat.minFac_sq_le_self (Nat.zero_lt_of_lt hl) hc
    rw [pow_two] at hs
    have hq : p.minFac < 32 := by
      by_contra! h
      exact (by decide : ¬32 * 32 < 1001) (((Nat.mul_le_mul h h).trans hs).trans_lt hu)
    exact ht _ hq hp.two_le hs (Nat.minFac_dvd p)
  · intro hp
    refine ⟨hp.two_le, fun q _ hq hs hd ↦ ?_⟩
    rcases (Nat.dvd_prime hp).mp hd with he | he
    · linarith only [he, hq]
    · subst q
      have hh := Nat.mul_le_mul_left p hp.two_le
      linarith only [hh, hs, hp.two_le]

private theorem checked : basePrimes.toList = (List.range 1001).filter trial := by decide +kernel

/-- The stored basis consists exactly of the primes through one thousand. -/
theorem baseHas_iff (p : ℕ) : baseHas p = true ↔ p < 1001 ∧ p.Prime := by
  rw [baseHas, Array.contains_iff_mem, ← Array.mem_toList_iff, checked, List.mem_filter,
    List.mem_range]
  exact and_congr_right fun hu ↦ trial_iff hu

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
