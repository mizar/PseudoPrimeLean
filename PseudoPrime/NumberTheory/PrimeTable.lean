/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.NumberTheory.PrimeIndexing
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.IntervalCases

/-!
# The first 163 primes, certified without `Nat.count`-based `decide` at scale

This file identifies `PseudoPrime.NumberTheory.primeByIndex i` for `i < 163` (primes up to `967`),
needed for the finite count-indexed primorial certificate range `6 ≤ k ≤ 163`
in `PrimorialCertificates.lean`. A single `decide` on `Nat.count Nat.Prime` at that scale
does not terminate in practice (`Nat.count` unfolds via `List.range`). Instead, each prime is
identified incrementally from the previous one. A shared count step avoids unfolding `Nat.count`;
short composite gaps are split into individual `norm_num` certificates rather than kernel reduction
of a bounded universal `decide`. Every generated fact is checked by Lean.

The 100-character line-length convention is waived in this file, matching the numeral-heavy style
needed to state each prime value directly.
-/

set_option linter.style.longLine false

namespace PseudoPrime.NumberTheory

theorem count_eq_of_all_not_prime_of_lt {a b : ℕ} (hab : a ≤ b)
    (hgap : ∀ m ∈ Finset.Ico a b, ¬Nat.Prime m) :
    Nat.count Nat.Prime b = Nat.count Nat.Prime a := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    rw [Nat.count_succ, ite_eq_right (hgap b (Finset.mem_Ico.mpr ⟨hab, Nat.lt_succ_self b⟩)),
      Nat.add_zero,
      ih
        (fun m hm =>
          hgap m
            (Finset.mem_Ico.mpr
              ⟨(Finset.mem_Ico.mp hm).1, (Finset.mem_Ico.mp hm).2.trans (Nat.lt_succ_self b)⟩))]

/-- Count one prime and skip a certified composite gap without evaluating the count. -/
theorem count_prime_step {a b k : ℕ} (hc : Nat.count Nat.Prime a = k) (hp : Nat.Prime a)
    (hab : a + 1 ≤ b) (hgap : ∀ m ∈ Finset.Ico (a + 1) b, ¬Nat.Prime m) :
    Nat.count Nat.Prime b = k + 1 := by
  rw [count_eq_of_all_not_prime_of_lt hab hgap, Nat.count_succ,
    ite_eq_left hp, hc]

theorem count_prime_at_0 : Nat.count Nat.Prime 2 = 0 := by decide

-- BEGIN GENERATED PRIME COUNTS
/-- The number of primes below 3, extending the previous certified prime. -/
theorem count_prime_at_1 : Nat.count Nat.Prime 3 = 1 := by
  apply count_prime_step count_prime_at_0 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  omega

/-- The number of primes below 5, extending the previous certified prime. -/
theorem count_prime_at_2 : Nat.count Nat.Prime 5 = 2 := by
  apply count_prime_step count_prime_at_1 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 7, extending the previous certified prime. -/
theorem count_prime_at_3 : Nat.count Nat.Prime 7 = 3 := by
  apply count_prime_step count_prime_at_2 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 11, extending the previous certified prime. -/
theorem count_prime_at_4 : Nat.count Nat.Prime 11 = 4 := by
  apply count_prime_step count_prime_at_3 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 13, extending the previous certified prime. -/
theorem count_prime_at_5 : Nat.count Nat.Prime 13 = 5 := by
  apply count_prime_step count_prime_at_4 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 17, extending the previous certified prime. -/
theorem count_prime_at_6 : Nat.count Nat.Prime 17 = 6 := by
  apply count_prime_step count_prime_at_5 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 19, extending the previous certified prime. -/
theorem count_prime_at_7 : Nat.count Nat.Prime 19 = 7 := by
  apply count_prime_step count_prime_at_6 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 23, extending the previous certified prime. -/
theorem count_prime_at_8 : Nat.count Nat.Prime 23 = 8 := by
  apply count_prime_step count_prime_at_7 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 29, extending the previous certified prime. -/
theorem count_prime_at_9 : Nat.count Nat.Prime 29 = 9 := by
  apply count_prime_step count_prime_at_8 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 31, extending the previous certified prime. -/
theorem count_prime_at_10 : Nat.count Nat.Prime 31 = 10 := by
  apply count_prime_step count_prime_at_9 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 37, extending the previous certified prime. -/
theorem count_prime_at_11 : Nat.count Nat.Prime 37 = 11 := by
  apply count_prime_step count_prime_at_10 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 41, extending the previous certified prime. -/
theorem count_prime_at_12 : Nat.count Nat.Prime 41 = 12 := by
  apply count_prime_step count_prime_at_11 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 43, extending the previous certified prime. -/
theorem count_prime_at_13 : Nat.count Nat.Prime 43 = 13 := by
  apply count_prime_step count_prime_at_12 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 47, extending the previous certified prime. -/
theorem count_prime_at_14 : Nat.count Nat.Prime 47 = 14 := by
  apply count_prime_step count_prime_at_13 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 53, extending the previous certified prime. -/
theorem count_prime_at_15 : Nat.count Nat.Prime 53 = 15 := by
  apply count_prime_step count_prime_at_14 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 59, extending the previous certified prime. -/
theorem count_prime_at_16 : Nat.count Nat.Prime 59 = 16 := by
  apply count_prime_step count_prime_at_15 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 61, extending the previous certified prime. -/
theorem count_prime_at_17 : Nat.count Nat.Prime 61 = 17 := by
  apply count_prime_step count_prime_at_16 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 67, extending the previous certified prime. -/
theorem count_prime_at_18 : Nat.count Nat.Prime 67 = 18 := by
  apply count_prime_step count_prime_at_17 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 71, extending the previous certified prime. -/
theorem count_prime_at_19 : Nat.count Nat.Prime 71 = 19 := by
  apply count_prime_step count_prime_at_18 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 73, extending the previous certified prime. -/
theorem count_prime_at_20 : Nat.count Nat.Prime 73 = 20 := by
  apply count_prime_step count_prime_at_19 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 79, extending the previous certified prime. -/
theorem count_prime_at_21 : Nat.count Nat.Prime 79 = 21 := by
  apply count_prime_step count_prime_at_20 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 83, extending the previous certified prime. -/
theorem count_prime_at_22 : Nat.count Nat.Prime 83 = 22 := by
  apply count_prime_step count_prime_at_21 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 89, extending the previous certified prime. -/
theorem count_prime_at_23 : Nat.count Nat.Prime 89 = 23 := by
  apply count_prime_step count_prime_at_22 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 97, extending the previous certified prime. -/
theorem count_prime_at_24 : Nat.count Nat.Prime 97 = 24 := by
  apply count_prime_step count_prime_at_23 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 101, extending the previous certified prime. -/
theorem count_prime_at_25 : Nat.count Nat.Prime 101 = 25 := by
  apply count_prime_step count_prime_at_24 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 103, extending the previous certified prime. -/
theorem count_prime_at_26 : Nat.count Nat.Prime 103 = 26 := by
  apply count_prime_step count_prime_at_25 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 107, extending the previous certified prime. -/
theorem count_prime_at_27 : Nat.count Nat.Prime 107 = 27 := by
  apply count_prime_step count_prime_at_26 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 109, extending the previous certified prime. -/
theorem count_prime_at_28 : Nat.count Nat.Prime 109 = 28 := by
  apply count_prime_step count_prime_at_27 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 113, extending the previous certified prime. -/
theorem count_prime_at_29 : Nat.count Nat.Prime 113 = 29 := by
  apply count_prime_step count_prime_at_28 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 127, extending the previous certified prime. -/
theorem count_prime_at_30 : Nat.count Nat.Prime 127 = 30 := by
  apply count_prime_step count_prime_at_29 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 131, extending the previous certified prime. -/
theorem count_prime_at_31 : Nat.count Nat.Prime 131 = 31 := by
  apply count_prime_step count_prime_at_30 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 137, extending the previous certified prime. -/
theorem count_prime_at_32 : Nat.count Nat.Prime 137 = 32 := by
  apply count_prime_step count_prime_at_31 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 139, extending the previous certified prime. -/
theorem count_prime_at_33 : Nat.count Nat.Prime 139 = 33 := by
  apply count_prime_step count_prime_at_32 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 149, extending the previous certified prime. -/
theorem count_prime_at_34 : Nat.count Nat.Prime 149 = 34 := by
  apply count_prime_step count_prime_at_33 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 151, extending the previous certified prime. -/
theorem count_prime_at_35 : Nat.count Nat.Prime 151 = 35 := by
  apply count_prime_step count_prime_at_34 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 157, extending the previous certified prime. -/
theorem count_prime_at_36 : Nat.count Nat.Prime 157 = 36 := by
  apply count_prime_step count_prime_at_35 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 163, extending the previous certified prime. -/
theorem count_prime_at_37 : Nat.count Nat.Prime 163 = 37 := by
  apply count_prime_step count_prime_at_36 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 167, extending the previous certified prime. -/
theorem count_prime_at_38 : Nat.count Nat.Prime 167 = 38 := by
  apply count_prime_step count_prime_at_37 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 173, extending the previous certified prime. -/
theorem count_prime_at_39 : Nat.count Nat.Prime 173 = 39 := by
  apply count_prime_step count_prime_at_38 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 179, extending the previous certified prime. -/
theorem count_prime_at_40 : Nat.count Nat.Prime 179 = 40 := by
  apply count_prime_step count_prime_at_39 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 181, extending the previous certified prime. -/
theorem count_prime_at_41 : Nat.count Nat.Prime 181 = 41 := by
  apply count_prime_step count_prime_at_40 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 191, extending the previous certified prime. -/
theorem count_prime_at_42 : Nat.count Nat.Prime 191 = 42 := by
  apply count_prime_step count_prime_at_41 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 193, extending the previous certified prime. -/
theorem count_prime_at_43 : Nat.count Nat.Prime 193 = 43 := by
  apply count_prime_step count_prime_at_42 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 197, extending the previous certified prime. -/
theorem count_prime_at_44 : Nat.count Nat.Prime 197 = 44 := by
  apply count_prime_step count_prime_at_43 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 199, extending the previous certified prime. -/
theorem count_prime_at_45 : Nat.count Nat.Prime 199 = 45 := by
  apply count_prime_step count_prime_at_44 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 211, extending the previous certified prime. -/
theorem count_prime_at_46 : Nat.count Nat.Prime 211 = 46 := by
  apply count_prime_step count_prime_at_45 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 223, extending the previous certified prime. -/
theorem count_prime_at_47 : Nat.count Nat.Prime 223 = 47 := by
  apply count_prime_step count_prime_at_46 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 227, extending the previous certified prime. -/
theorem count_prime_at_48 : Nat.count Nat.Prime 227 = 48 := by
  apply count_prime_step count_prime_at_47 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 229, extending the previous certified prime. -/
theorem count_prime_at_49 : Nat.count Nat.Prime 229 = 49 := by
  apply count_prime_step count_prime_at_48 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 233, extending the previous certified prime. -/
theorem count_prime_at_50 : Nat.count Nat.Prime 233 = 50 := by
  apply count_prime_step count_prime_at_49 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 239, extending the previous certified prime. -/
theorem count_prime_at_51 : Nat.count Nat.Prime 239 = 51 := by
  apply count_prime_step count_prime_at_50 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 241, extending the previous certified prime. -/
theorem count_prime_at_52 : Nat.count Nat.Prime 241 = 52 := by
  apply count_prime_step count_prime_at_51 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 251, extending the previous certified prime. -/
theorem count_prime_at_53 : Nat.count Nat.Prime 251 = 53 := by
  apply count_prime_step count_prime_at_52 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 257, extending the previous certified prime. -/
theorem count_prime_at_54 : Nat.count Nat.Prime 257 = 54 := by
  apply count_prime_step count_prime_at_53 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 263, extending the previous certified prime. -/
theorem count_prime_at_55 : Nat.count Nat.Prime 263 = 55 := by
  apply count_prime_step count_prime_at_54 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 269, extending the previous certified prime. -/
theorem count_prime_at_56 : Nat.count Nat.Prime 269 = 56 := by
  apply count_prime_step count_prime_at_55 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 271, extending the previous certified prime. -/
theorem count_prime_at_57 : Nat.count Nat.Prime 271 = 57 := by
  apply count_prime_step count_prime_at_56 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 277, extending the previous certified prime. -/
theorem count_prime_at_58 : Nat.count Nat.Prime 277 = 58 := by
  apply count_prime_step count_prime_at_57 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 281, extending the previous certified prime. -/
theorem count_prime_at_59 : Nat.count Nat.Prime 281 = 59 := by
  apply count_prime_step count_prime_at_58 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 283, extending the previous certified prime. -/
theorem count_prime_at_60 : Nat.count Nat.Prime 283 = 60 := by
  apply count_prime_step count_prime_at_59 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 293, extending the previous certified prime. -/
theorem count_prime_at_61 : Nat.count Nat.Prime 293 = 61 := by
  apply count_prime_step count_prime_at_60 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 307, extending the previous certified prime. -/
theorem count_prime_at_62 : Nat.count Nat.Prime 307 = 62 := by
  apply count_prime_step count_prime_at_61 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 311, extending the previous certified prime. -/
theorem count_prime_at_63 : Nat.count Nat.Prime 311 = 63 := by
  apply count_prime_step count_prime_at_62 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 313, extending the previous certified prime. -/
theorem count_prime_at_64 : Nat.count Nat.Prime 313 = 64 := by
  apply count_prime_step count_prime_at_63 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 317, extending the previous certified prime. -/
theorem count_prime_at_65 : Nat.count Nat.Prime 317 = 65 := by
  apply count_prime_step count_prime_at_64 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 331, extending the previous certified prime. -/
theorem count_prime_at_66 : Nat.count Nat.Prime 331 = 66 := by
  apply count_prime_step count_prime_at_65 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 337, extending the previous certified prime. -/
theorem count_prime_at_67 : Nat.count Nat.Prime 337 = 67 := by
  apply count_prime_step count_prime_at_66 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 347, extending the previous certified prime. -/
theorem count_prime_at_68 : Nat.count Nat.Prime 347 = 68 := by
  apply count_prime_step count_prime_at_67 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 349, extending the previous certified prime. -/
theorem count_prime_at_69 : Nat.count Nat.Prime 349 = 69 := by
  apply count_prime_step count_prime_at_68 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 353, extending the previous certified prime. -/
theorem count_prime_at_70 : Nat.count Nat.Prime 353 = 70 := by
  apply count_prime_step count_prime_at_69 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 359, extending the previous certified prime. -/
theorem count_prime_at_71 : Nat.count Nat.Prime 359 = 71 := by
  apply count_prime_step count_prime_at_70 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 367, extending the previous certified prime. -/
theorem count_prime_at_72 : Nat.count Nat.Prime 367 = 72 := by
  apply count_prime_step count_prime_at_71 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 373, extending the previous certified prime. -/
theorem count_prime_at_73 : Nat.count Nat.Prime 373 = 73 := by
  apply count_prime_step count_prime_at_72 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 379, extending the previous certified prime. -/
theorem count_prime_at_74 : Nat.count Nat.Prime 379 = 74 := by
  apply count_prime_step count_prime_at_73 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 383, extending the previous certified prime. -/
theorem count_prime_at_75 : Nat.count Nat.Prime 383 = 75 := by
  apply count_prime_step count_prime_at_74 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 389, extending the previous certified prime. -/
theorem count_prime_at_76 : Nat.count Nat.Prime 389 = 76 := by
  apply count_prime_step count_prime_at_75 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 397, extending the previous certified prime. -/
theorem count_prime_at_77 : Nat.count Nat.Prime 397 = 77 := by
  apply count_prime_step count_prime_at_76 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 401, extending the previous certified prime. -/
theorem count_prime_at_78 : Nat.count Nat.Prime 401 = 78 := by
  apply count_prime_step count_prime_at_77 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 409, extending the previous certified prime. -/
theorem count_prime_at_79 : Nat.count Nat.Prime 409 = 79 := by
  apply count_prime_step count_prime_at_78 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 419, extending the previous certified prime. -/
theorem count_prime_at_80 : Nat.count Nat.Prime 419 = 80 := by
  apply count_prime_step count_prime_at_79 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 421, extending the previous certified prime. -/
theorem count_prime_at_81 : Nat.count Nat.Prime 421 = 81 := by
  apply count_prime_step count_prime_at_80 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 431, extending the previous certified prime. -/
theorem count_prime_at_82 : Nat.count Nat.Prime 431 = 82 := by
  apply count_prime_step count_prime_at_81 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 433, extending the previous certified prime. -/
theorem count_prime_at_83 : Nat.count Nat.Prime 433 = 83 := by
  apply count_prime_step count_prime_at_82 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 439, extending the previous certified prime. -/
theorem count_prime_at_84 : Nat.count Nat.Prime 439 = 84 := by
  apply count_prime_step count_prime_at_83 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 443, extending the previous certified prime. -/
theorem count_prime_at_85 : Nat.count Nat.Prime 443 = 85 := by
  apply count_prime_step count_prime_at_84 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 449, extending the previous certified prime. -/
theorem count_prime_at_86 : Nat.count Nat.Prime 449 = 86 := by
  apply count_prime_step count_prime_at_85 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 457, extending the previous certified prime. -/
theorem count_prime_at_87 : Nat.count Nat.Prime 457 = 87 := by
  apply count_prime_step count_prime_at_86 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 461, extending the previous certified prime. -/
theorem count_prime_at_88 : Nat.count Nat.Prime 461 = 88 := by
  apply count_prime_step count_prime_at_87 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 463, extending the previous certified prime. -/
theorem count_prime_at_89 : Nat.count Nat.Prime 463 = 89 := by
  apply count_prime_step count_prime_at_88 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 467, extending the previous certified prime. -/
theorem count_prime_at_90 : Nat.count Nat.Prime 467 = 90 := by
  apply count_prime_step count_prime_at_89 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 479, extending the previous certified prime. -/
theorem count_prime_at_91 : Nat.count Nat.Prime 479 = 91 := by
  apply count_prime_step count_prime_at_90 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 487, extending the previous certified prime. -/
theorem count_prime_at_92 : Nat.count Nat.Prime 487 = 92 := by
  apply count_prime_step count_prime_at_91 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 491, extending the previous certified prime. -/
theorem count_prime_at_93 : Nat.count Nat.Prime 491 = 93 := by
  apply count_prime_step count_prime_at_92 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 499, extending the previous certified prime. -/
theorem count_prime_at_94 : Nat.count Nat.Prime 499 = 94 := by
  apply count_prime_step count_prime_at_93 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 503, extending the previous certified prime. -/
theorem count_prime_at_95 : Nat.count Nat.Prime 503 = 95 := by
  apply count_prime_step count_prime_at_94 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 509, extending the previous certified prime. -/
theorem count_prime_at_96 : Nat.count Nat.Prime 509 = 96 := by
  apply count_prime_step count_prime_at_95 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 521, extending the previous certified prime. -/
theorem count_prime_at_97 : Nat.count Nat.Prime 521 = 97 := by
  apply count_prime_step count_prime_at_96 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 523, extending the previous certified prime. -/
theorem count_prime_at_98 : Nat.count Nat.Prime 523 = 98 := by
  apply count_prime_step count_prime_at_97 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 541, extending the previous certified prime. -/
theorem count_prime_at_99 : Nat.count Nat.Prime 541 = 99 := by
  apply count_prime_step count_prime_at_98 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 547, extending the previous certified prime. -/
theorem count_prime_at_100 : Nat.count Nat.Prime 547 = 100 := by
  apply count_prime_step count_prime_at_99 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 557, extending the previous certified prime. -/
theorem count_prime_at_101 : Nat.count Nat.Prime 557 = 101 := by
  apply count_prime_step count_prime_at_100 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 563, extending the previous certified prime. -/
theorem count_prime_at_102 : Nat.count Nat.Prime 563 = 102 := by
  apply count_prime_step count_prime_at_101 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 569, extending the previous certified prime. -/
theorem count_prime_at_103 : Nat.count Nat.Prime 569 = 103 := by
  apply count_prime_step count_prime_at_102 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 571, extending the previous certified prime. -/
theorem count_prime_at_104 : Nat.count Nat.Prime 571 = 104 := by
  apply count_prime_step count_prime_at_103 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 577, extending the previous certified prime. -/
theorem count_prime_at_105 : Nat.count Nat.Prime 577 = 105 := by
  apply count_prime_step count_prime_at_104 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 587, extending the previous certified prime. -/
theorem count_prime_at_106 : Nat.count Nat.Prime 587 = 106 := by
  apply count_prime_step count_prime_at_105 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 593, extending the previous certified prime. -/
theorem count_prime_at_107 : Nat.count Nat.Prime 593 = 107 := by
  apply count_prime_step count_prime_at_106 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 599, extending the previous certified prime. -/
theorem count_prime_at_108 : Nat.count Nat.Prime 599 = 108 := by
  apply count_prime_step count_prime_at_107 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 601, extending the previous certified prime. -/
theorem count_prime_at_109 : Nat.count Nat.Prime 601 = 109 := by
  apply count_prime_step count_prime_at_108 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 607, extending the previous certified prime. -/
theorem count_prime_at_110 : Nat.count Nat.Prime 607 = 110 := by
  apply count_prime_step count_prime_at_109 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 613, extending the previous certified prime. -/
theorem count_prime_at_111 : Nat.count Nat.Prime 613 = 111 := by
  apply count_prime_step count_prime_at_110 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 617, extending the previous certified prime. -/
theorem count_prime_at_112 : Nat.count Nat.Prime 617 = 112 := by
  apply count_prime_step count_prime_at_111 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 619, extending the previous certified prime. -/
theorem count_prime_at_113 : Nat.count Nat.Prime 619 = 113 := by
  apply count_prime_step count_prime_at_112 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 631, extending the previous certified prime. -/
theorem count_prime_at_114 : Nat.count Nat.Prime 631 = 114 := by
  apply count_prime_step count_prime_at_113 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 641, extending the previous certified prime. -/
theorem count_prime_at_115 : Nat.count Nat.Prime 641 = 115 := by
  apply count_prime_step count_prime_at_114 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 643, extending the previous certified prime. -/
theorem count_prime_at_116 : Nat.count Nat.Prime 643 = 116 := by
  apply count_prime_step count_prime_at_115 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 647, extending the previous certified prime. -/
theorem count_prime_at_117 : Nat.count Nat.Prime 647 = 117 := by
  apply count_prime_step count_prime_at_116 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 653, extending the previous certified prime. -/
theorem count_prime_at_118 : Nat.count Nat.Prime 653 = 118 := by
  apply count_prime_step count_prime_at_117 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 659, extending the previous certified prime. -/
theorem count_prime_at_119 : Nat.count Nat.Prime 659 = 119 := by
  apply count_prime_step count_prime_at_118 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 661, extending the previous certified prime. -/
theorem count_prime_at_120 : Nat.count Nat.Prime 661 = 120 := by
  apply count_prime_step count_prime_at_119 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 673, extending the previous certified prime. -/
theorem count_prime_at_121 : Nat.count Nat.Prime 673 = 121 := by
  apply count_prime_step count_prime_at_120 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 677, extending the previous certified prime. -/
theorem count_prime_at_122 : Nat.count Nat.Prime 677 = 122 := by
  apply count_prime_step count_prime_at_121 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 683, extending the previous certified prime. -/
theorem count_prime_at_123 : Nat.count Nat.Prime 683 = 123 := by
  apply count_prime_step count_prime_at_122 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 691, extending the previous certified prime. -/
theorem count_prime_at_124 : Nat.count Nat.Prime 691 = 124 := by
  apply count_prime_step count_prime_at_123 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 701, extending the previous certified prime. -/
theorem count_prime_at_125 : Nat.count Nat.Prime 701 = 125 := by
  apply count_prime_step count_prime_at_124 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 709, extending the previous certified prime. -/
theorem count_prime_at_126 : Nat.count Nat.Prime 709 = 126 := by
  apply count_prime_step count_prime_at_125 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 719, extending the previous certified prime. -/
theorem count_prime_at_127 : Nat.count Nat.Prime 719 = 127 := by
  apply count_prime_step count_prime_at_126 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 727, extending the previous certified prime. -/
theorem count_prime_at_128 : Nat.count Nat.Prime 727 = 128 := by
  apply count_prime_step count_prime_at_127 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 733, extending the previous certified prime. -/
theorem count_prime_at_129 : Nat.count Nat.Prime 733 = 129 := by
  apply count_prime_step count_prime_at_128 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 739, extending the previous certified prime. -/
theorem count_prime_at_130 : Nat.count Nat.Prime 739 = 130 := by
  apply count_prime_step count_prime_at_129 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 743, extending the previous certified prime. -/
theorem count_prime_at_131 : Nat.count Nat.Prime 743 = 131 := by
  apply count_prime_step count_prime_at_130 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 751, extending the previous certified prime. -/
theorem count_prime_at_132 : Nat.count Nat.Prime 751 = 132 := by
  apply count_prime_step count_prime_at_131 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 757, extending the previous certified prime. -/
theorem count_prime_at_133 : Nat.count Nat.Prime 757 = 133 := by
  apply count_prime_step count_prime_at_132 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 761, extending the previous certified prime. -/
theorem count_prime_at_134 : Nat.count Nat.Prime 761 = 134 := by
  apply count_prime_step count_prime_at_133 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 769, extending the previous certified prime. -/
theorem count_prime_at_135 : Nat.count Nat.Prime 769 = 135 := by
  apply count_prime_step count_prime_at_134 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 773, extending the previous certified prime. -/
theorem count_prime_at_136 : Nat.count Nat.Prime 773 = 136 := by
  apply count_prime_step count_prime_at_135 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 787, extending the previous certified prime. -/
theorem count_prime_at_137 : Nat.count Nat.Prime 787 = 137 := by
  apply count_prime_step count_prime_at_136 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 797, extending the previous certified prime. -/
theorem count_prime_at_138 : Nat.count Nat.Prime 797 = 138 := by
  apply count_prime_step count_prime_at_137 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 809, extending the previous certified prime. -/
theorem count_prime_at_139 : Nat.count Nat.Prime 809 = 139 := by
  apply count_prime_step count_prime_at_138 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 811, extending the previous certified prime. -/
theorem count_prime_at_140 : Nat.count Nat.Prime 811 = 140 := by
  apply count_prime_step count_prime_at_139 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 821, extending the previous certified prime. -/
theorem count_prime_at_141 : Nat.count Nat.Prime 821 = 141 := by
  apply count_prime_step count_prime_at_140 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 823, extending the previous certified prime. -/
theorem count_prime_at_142 : Nat.count Nat.Prime 823 = 142 := by
  apply count_prime_step count_prime_at_141 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 827, extending the previous certified prime. -/
theorem count_prime_at_143 : Nat.count Nat.Prime 827 = 143 := by
  apply count_prime_step count_prime_at_142 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 829, extending the previous certified prime. -/
theorem count_prime_at_144 : Nat.count Nat.Prime 829 = 144 := by
  apply count_prime_step count_prime_at_143 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 839, extending the previous certified prime. -/
theorem count_prime_at_145 : Nat.count Nat.Prime 839 = 145 := by
  apply count_prime_step count_prime_at_144 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 853, extending the previous certified prime. -/
theorem count_prime_at_146 : Nat.count Nat.Prime 853 = 146 := by
  apply count_prime_step count_prime_at_145 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 857, extending the previous certified prime. -/
theorem count_prime_at_147 : Nat.count Nat.Prime 857 = 147 := by
  apply count_prime_step count_prime_at_146 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 859, extending the previous certified prime. -/
theorem count_prime_at_148 : Nat.count Nat.Prime 859 = 148 := by
  apply count_prime_step count_prime_at_147 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 863, extending the previous certified prime. -/
theorem count_prime_at_149 : Nat.count Nat.Prime 863 = 149 := by
  apply count_prime_step count_prime_at_148 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 877, extending the previous certified prime. -/
theorem count_prime_at_150 : Nat.count Nat.Prime 877 = 150 := by
  apply count_prime_step count_prime_at_149 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 881, extending the previous certified prime. -/
theorem count_prime_at_151 : Nat.count Nat.Prime 881 = 151 := by
  apply count_prime_step count_prime_at_150 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 883, extending the previous certified prime. -/
theorem count_prime_at_152 : Nat.count Nat.Prime 883 = 152 := by
  apply count_prime_step count_prime_at_151 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m
  norm_num

/-- The number of primes below 887, extending the previous certified prime. -/
theorem count_prime_at_153 : Nat.count Nat.Prime 887 = 153 := by
  apply count_prime_step count_prime_at_152 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 907, extending the previous certified prime. -/
theorem count_prime_at_154 : Nat.count Nat.Prime 907 = 154 := by
  apply count_prime_step count_prime_at_153 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 911, extending the previous certified prime. -/
theorem count_prime_at_155 : Nat.count Nat.Prime 911 = 155 := by
  apply count_prime_step count_prime_at_154 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 919, extending the previous certified prime. -/
theorem count_prime_at_156 : Nat.count Nat.Prime 919 = 156 := by
  apply count_prime_step count_prime_at_155 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 929, extending the previous certified prime. -/
theorem count_prime_at_157 : Nat.count Nat.Prime 929 = 157 := by
  apply count_prime_step count_prime_at_156 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 937, extending the previous certified prime. -/
theorem count_prime_at_158 : Nat.count Nat.Prime 937 = 158 := by
  apply count_prime_step count_prime_at_157 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 941, extending the previous certified prime. -/
theorem count_prime_at_159 : Nat.count Nat.Prime 941 = 159 := by
  apply count_prime_step count_prime_at_158 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 947, extending the previous certified prime. -/
theorem count_prime_at_160 : Nat.count Nat.Prime 947 = 160 := by
  apply count_prime_step count_prime_at_159 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 953, extending the previous certified prime. -/
theorem count_prime_at_161 : Nat.count Nat.Prime 953 = 161 := by
  apply count_prime_step count_prime_at_160 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

/-- The number of primes below 967, extending the previous certified prime. -/
theorem count_prime_at_162 : Nat.count Nat.Prime 967 = 162 := by
  apply count_prime_step count_prime_at_161 (by norm_num) (by norm_num)
  intro m hm
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hm
  interval_cases m <;> norm_num

-- END GENERATED PRIME COUNTS

theorem primeByIndex_at_6 : primeByIndex 6 = 17 := by
  have hp : Nat.Prime 17 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_6]

theorem primeByIndex_at_7 : primeByIndex 7 = 19 := by
  have hp : Nat.Prime 19 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_7]

theorem primeByIndex_at_8 : primeByIndex 8 = 23 := by
  have hp : Nat.Prime 23 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_8]

theorem primeByIndex_at_9 : primeByIndex 9 = 29 := by
  have hp : Nat.Prime 29 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_9]

theorem primeByIndex_at_10 : primeByIndex 10 = 31 := by
  have hp : Nat.Prime 31 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_10]

theorem primeByIndex_at_11 : primeByIndex 11 = 37 := by
  have hp : Nat.Prime 37 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_11]

theorem primeByIndex_at_12 : primeByIndex 12 = 41 := by
  have hp : Nat.Prime 41 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_12]

theorem primeByIndex_at_13 : primeByIndex 13 = 43 := by
  have hp : Nat.Prime 43 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_13]

theorem primeByIndex_at_14 : primeByIndex 14 = 47 := by
  have hp : Nat.Prime 47 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_14]

theorem primeByIndex_at_15 : primeByIndex 15 = 53 := by
  have hp : Nat.Prime 53 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_15]

theorem primeByIndex_at_16 : primeByIndex 16 = 59 := by
  have hp : Nat.Prime 59 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_16]

theorem primeByIndex_at_17 : primeByIndex 17 = 61 := by
  have hp : Nat.Prime 61 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_17]

theorem primeByIndex_at_18 : primeByIndex 18 = 67 := by
  have hp : Nat.Prime 67 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_18]

theorem primeByIndex_at_19 : primeByIndex 19 = 71 := by
  have hp : Nat.Prime 71 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_19]

theorem primeByIndex_at_20 : primeByIndex 20 = 73 := by
  have hp : Nat.Prime 73 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_20]

theorem primeByIndex_at_21 : primeByIndex 21 = 79 := by
  have hp : Nat.Prime 79 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_21]

theorem primeByIndex_at_22 : primeByIndex 22 = 83 := by
  have hp : Nat.Prime 83 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_22]

theorem primeByIndex_at_23 : primeByIndex 23 = 89 := by
  have hp : Nat.Prime 89 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_23]

theorem primeByIndex_at_24 : primeByIndex 24 = 97 := by
  have hp : Nat.Prime 97 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_24]

theorem primeByIndex_at_25 : primeByIndex 25 = 101 := by
  have hp : Nat.Prime 101 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_25]

theorem primeByIndex_at_26 : primeByIndex 26 = 103 := by
  have hp : Nat.Prime 103 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_26]

theorem primeByIndex_at_27 : primeByIndex 27 = 107 := by
  have hp : Nat.Prime 107 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_27]

theorem primeByIndex_at_28 : primeByIndex 28 = 109 := by
  have hp : Nat.Prime 109 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_28]

theorem primeByIndex_at_29 : primeByIndex 29 = 113 := by
  have hp : Nat.Prime 113 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_29]

theorem primeByIndex_at_30 : primeByIndex 30 = 127 := by
  have hp : Nat.Prime 127 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_30]

theorem primeByIndex_at_31 : primeByIndex 31 = 131 := by
  have hp : Nat.Prime 131 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_31]

theorem primeByIndex_at_32 : primeByIndex 32 = 137 := by
  have hp : Nat.Prime 137 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_32]

theorem primeByIndex_at_33 : primeByIndex 33 = 139 := by
  have hp : Nat.Prime 139 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_33]

theorem primeByIndex_at_34 : primeByIndex 34 = 149 := by
  have hp : Nat.Prime 149 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_34]

theorem primeByIndex_at_35 : primeByIndex 35 = 151 := by
  have hp : Nat.Prime 151 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_35]

theorem primeByIndex_at_36 : primeByIndex 36 = 157 := by
  have hp : Nat.Prime 157 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_36]

theorem primeByIndex_at_37 : primeByIndex 37 = 163 := by
  have hp : Nat.Prime 163 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_37]

theorem primeByIndex_at_38 : primeByIndex 38 = 167 := by
  have hp : Nat.Prime 167 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_38]

theorem primeByIndex_at_39 : primeByIndex 39 = 173 := by
  have hp : Nat.Prime 173 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_39]

theorem primeByIndex_at_40 : primeByIndex 40 = 179 := by
  have hp : Nat.Prime 179 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_40]

theorem primeByIndex_at_41 : primeByIndex 41 = 181 := by
  have hp : Nat.Prime 181 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_41]

theorem primeByIndex_at_42 : primeByIndex 42 = 191 := by
  have hp : Nat.Prime 191 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_42]

theorem primeByIndex_at_43 : primeByIndex 43 = 193 := by
  have hp : Nat.Prime 193 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_43]

theorem primeByIndex_at_44 : primeByIndex 44 = 197 := by
  have hp : Nat.Prime 197 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_44]

theorem primeByIndex_at_45 : primeByIndex 45 = 199 := by
  have hp : Nat.Prime 199 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_45]

theorem primeByIndex_at_46 : primeByIndex 46 = 211 := by
  have hp : Nat.Prime 211 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_46]

theorem primeByIndex_at_47 : primeByIndex 47 = 223 := by
  have hp : Nat.Prime 223 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_47]

theorem primeByIndex_at_48 : primeByIndex 48 = 227 := by
  have hp : Nat.Prime 227 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_48]

theorem primeByIndex_at_49 : primeByIndex 49 = 229 := by
  have hp : Nat.Prime 229 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_49]

theorem primeByIndex_at_50 : primeByIndex 50 = 233 := by
  have hp : Nat.Prime 233 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_50]

theorem primeByIndex_at_51 : primeByIndex 51 = 239 := by
  have hp : Nat.Prime 239 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_51]

theorem primeByIndex_at_52 : primeByIndex 52 = 241 := by
  have hp : Nat.Prime 241 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_52]

theorem primeByIndex_at_53 : primeByIndex 53 = 251 := by
  have hp : Nat.Prime 251 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_53]

theorem primeByIndex_at_54 : primeByIndex 54 = 257 := by
  have hp : Nat.Prime 257 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_54]

theorem primeByIndex_at_55 : primeByIndex 55 = 263 := by
  have hp : Nat.Prime 263 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_55]

theorem primeByIndex_at_56 : primeByIndex 56 = 269 := by
  have hp : Nat.Prime 269 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_56]

theorem primeByIndex_at_57 : primeByIndex 57 = 271 := by
  have hp : Nat.Prime 271 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_57]

theorem primeByIndex_at_58 : primeByIndex 58 = 277 := by
  have hp : Nat.Prime 277 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_58]

theorem primeByIndex_at_59 : primeByIndex 59 = 281 := by
  have hp : Nat.Prime 281 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_59]

theorem primeByIndex_at_60 : primeByIndex 60 = 283 := by
  have hp : Nat.Prime 283 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_60]

theorem primeByIndex_at_61 : primeByIndex 61 = 293 := by
  have hp : Nat.Prime 293 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_61]

theorem primeByIndex_at_62 : primeByIndex 62 = 307 := by
  have hp : Nat.Prime 307 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_62]

theorem primeByIndex_at_63 : primeByIndex 63 = 311 := by
  have hp : Nat.Prime 311 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_63]

theorem primeByIndex_at_64 : primeByIndex 64 = 313 := by
  have hp : Nat.Prime 313 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_64]

theorem primeByIndex_at_65 : primeByIndex 65 = 317 := by
  have hp : Nat.Prime 317 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_65]

theorem primeByIndex_at_66 : primeByIndex 66 = 331 := by
  have hp : Nat.Prime 331 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_66]

theorem primeByIndex_at_67 : primeByIndex 67 = 337 := by
  have hp : Nat.Prime 337 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_67]

theorem primeByIndex_at_68 : primeByIndex 68 = 347 := by
  have hp : Nat.Prime 347 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_68]

theorem primeByIndex_at_69 : primeByIndex 69 = 349 := by
  have hp : Nat.Prime 349 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_69]

theorem primeByIndex_at_70 : primeByIndex 70 = 353 := by
  have hp : Nat.Prime 353 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_70]

theorem primeByIndex_at_71 : primeByIndex 71 = 359 := by
  have hp : Nat.Prime 359 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_71]

theorem primeByIndex_at_72 : primeByIndex 72 = 367 := by
  have hp : Nat.Prime 367 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_72]

theorem primeByIndex_at_73 : primeByIndex 73 = 373 := by
  have hp : Nat.Prime 373 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_73]

theorem primeByIndex_at_74 : primeByIndex 74 = 379 := by
  have hp : Nat.Prime 379 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_74]

theorem primeByIndex_at_75 : primeByIndex 75 = 383 := by
  have hp : Nat.Prime 383 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_75]

theorem primeByIndex_at_76 : primeByIndex 76 = 389 := by
  have hp : Nat.Prime 389 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_76]

theorem primeByIndex_at_77 : primeByIndex 77 = 397 := by
  have hp : Nat.Prime 397 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_77]

theorem primeByIndex_at_78 : primeByIndex 78 = 401 := by
  have hp : Nat.Prime 401 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_78]

theorem primeByIndex_at_79 : primeByIndex 79 = 409 := by
  have hp : Nat.Prime 409 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_79]

theorem primeByIndex_at_80 : primeByIndex 80 = 419 := by
  have hp : Nat.Prime 419 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_80]

theorem primeByIndex_at_81 : primeByIndex 81 = 421 := by
  have hp : Nat.Prime 421 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_81]

theorem primeByIndex_at_82 : primeByIndex 82 = 431 := by
  have hp : Nat.Prime 431 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_82]

theorem primeByIndex_at_83 : primeByIndex 83 = 433 := by
  have hp : Nat.Prime 433 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_83]

theorem primeByIndex_at_84 : primeByIndex 84 = 439 := by
  have hp : Nat.Prime 439 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_84]

theorem primeByIndex_at_85 : primeByIndex 85 = 443 := by
  have hp : Nat.Prime 443 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_85]

theorem primeByIndex_at_86 : primeByIndex 86 = 449 := by
  have hp : Nat.Prime 449 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_86]

theorem primeByIndex_at_87 : primeByIndex 87 = 457 := by
  have hp : Nat.Prime 457 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_87]

theorem primeByIndex_at_88 : primeByIndex 88 = 461 := by
  have hp : Nat.Prime 461 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_88]

theorem primeByIndex_at_89 : primeByIndex 89 = 463 := by
  have hp : Nat.Prime 463 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_89]

theorem primeByIndex_at_90 : primeByIndex 90 = 467 := by
  have hp : Nat.Prime 467 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_90]

theorem primeByIndex_at_91 : primeByIndex 91 = 479 := by
  have hp : Nat.Prime 479 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_91]

theorem primeByIndex_at_92 : primeByIndex 92 = 487 := by
  have hp : Nat.Prime 487 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_92]

theorem primeByIndex_at_93 : primeByIndex 93 = 491 := by
  have hp : Nat.Prime 491 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_93]

theorem primeByIndex_at_94 : primeByIndex 94 = 499 := by
  have hp : Nat.Prime 499 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_94]

theorem primeByIndex_at_95 : primeByIndex 95 = 503 := by
  have hp : Nat.Prime 503 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_95]

theorem primeByIndex_at_96 : primeByIndex 96 = 509 := by
  have hp : Nat.Prime 509 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_96]

theorem primeByIndex_at_97 : primeByIndex 97 = 521 := by
  have hp : Nat.Prime 521 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_97]

theorem primeByIndex_at_98 : primeByIndex 98 = 523 := by
  have hp : Nat.Prime 523 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_98]

theorem primeByIndex_at_99 : primeByIndex 99 = 541 := by
  have hp : Nat.Prime 541 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_99]

theorem primeByIndex_at_100 : primeByIndex 100 = 547 := by
  have hp : Nat.Prime 547 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_100]

theorem primeByIndex_at_101 : primeByIndex 101 = 557 := by
  have hp : Nat.Prime 557 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_101]

theorem primeByIndex_at_102 : primeByIndex 102 = 563 := by
  have hp : Nat.Prime 563 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_102]

theorem primeByIndex_at_103 : primeByIndex 103 = 569 := by
  have hp : Nat.Prime 569 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_103]

theorem primeByIndex_at_104 : primeByIndex 104 = 571 := by
  have hp : Nat.Prime 571 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_104]

theorem primeByIndex_at_105 : primeByIndex 105 = 577 := by
  have hp : Nat.Prime 577 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_105]

theorem primeByIndex_at_106 : primeByIndex 106 = 587 := by
  have hp : Nat.Prime 587 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_106]

theorem primeByIndex_at_107 : primeByIndex 107 = 593 := by
  have hp : Nat.Prime 593 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_107]

theorem primeByIndex_at_108 : primeByIndex 108 = 599 := by
  have hp : Nat.Prime 599 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_108]

theorem primeByIndex_at_109 : primeByIndex 109 = 601 := by
  have hp : Nat.Prime 601 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_109]

theorem primeByIndex_at_110 : primeByIndex 110 = 607 := by
  have hp : Nat.Prime 607 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_110]

theorem primeByIndex_at_111 : primeByIndex 111 = 613 := by
  have hp : Nat.Prime 613 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_111]

theorem primeByIndex_at_112 : primeByIndex 112 = 617 := by
  have hp : Nat.Prime 617 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_112]

theorem primeByIndex_at_113 : primeByIndex 113 = 619 := by
  have hp : Nat.Prime 619 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_113]

theorem primeByIndex_at_114 : primeByIndex 114 = 631 := by
  have hp : Nat.Prime 631 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_114]

theorem primeByIndex_at_115 : primeByIndex 115 = 641 := by
  have hp : Nat.Prime 641 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_115]

theorem primeByIndex_at_116 : primeByIndex 116 = 643 := by
  have hp : Nat.Prime 643 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_116]

theorem primeByIndex_at_117 : primeByIndex 117 = 647 := by
  have hp : Nat.Prime 647 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_117]

theorem primeByIndex_at_118 : primeByIndex 118 = 653 := by
  have hp : Nat.Prime 653 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_118]

theorem primeByIndex_at_119 : primeByIndex 119 = 659 := by
  have hp : Nat.Prime 659 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_119]

theorem primeByIndex_at_120 : primeByIndex 120 = 661 := by
  have hp : Nat.Prime 661 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_120]

theorem primeByIndex_at_121 : primeByIndex 121 = 673 := by
  have hp : Nat.Prime 673 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_121]

theorem primeByIndex_at_122 : primeByIndex 122 = 677 := by
  have hp : Nat.Prime 677 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_122]

theorem primeByIndex_at_123 : primeByIndex 123 = 683 := by
  have hp : Nat.Prime 683 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_123]

theorem primeByIndex_at_124 : primeByIndex 124 = 691 := by
  have hp : Nat.Prime 691 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_124]

theorem primeByIndex_at_125 : primeByIndex 125 = 701 := by
  have hp : Nat.Prime 701 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_125]

theorem primeByIndex_at_126 : primeByIndex 126 = 709 := by
  have hp : Nat.Prime 709 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_126]

theorem primeByIndex_at_127 : primeByIndex 127 = 719 := by
  have hp : Nat.Prime 719 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_127]

theorem primeByIndex_at_128 : primeByIndex 128 = 727 := by
  have hp : Nat.Prime 727 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_128]

theorem primeByIndex_at_129 : primeByIndex 129 = 733 := by
  have hp : Nat.Prime 733 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_129]

theorem primeByIndex_at_130 : primeByIndex 130 = 739 := by
  have hp : Nat.Prime 739 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_130]

theorem primeByIndex_at_131 : primeByIndex 131 = 743 := by
  have hp : Nat.Prime 743 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_131]

theorem primeByIndex_at_132 : primeByIndex 132 = 751 := by
  have hp : Nat.Prime 751 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_132]

theorem primeByIndex_at_133 : primeByIndex 133 = 757 := by
  have hp : Nat.Prime 757 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_133]

theorem primeByIndex_at_134 : primeByIndex 134 = 761 := by
  have hp : Nat.Prime 761 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_134]

theorem primeByIndex_at_135 : primeByIndex 135 = 769 := by
  have hp : Nat.Prime 769 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_135]

theorem primeByIndex_at_136 : primeByIndex 136 = 773 := by
  have hp : Nat.Prime 773 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_136]

theorem primeByIndex_at_137 : primeByIndex 137 = 787 := by
  have hp : Nat.Prime 787 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_137]

theorem primeByIndex_at_138 : primeByIndex 138 = 797 := by
  have hp : Nat.Prime 797 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_138]

theorem primeByIndex_at_139 : primeByIndex 139 = 809 := by
  have hp : Nat.Prime 809 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_139]

theorem primeByIndex_at_140 : primeByIndex 140 = 811 := by
  have hp : Nat.Prime 811 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_140]

theorem primeByIndex_at_141 : primeByIndex 141 = 821 := by
  have hp : Nat.Prime 821 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_141]

theorem primeByIndex_at_142 : primeByIndex 142 = 823 := by
  have hp : Nat.Prime 823 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_142]

theorem primeByIndex_at_143 : primeByIndex 143 = 827 := by
  have hp : Nat.Prime 827 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_143]

theorem primeByIndex_at_144 : primeByIndex 144 = 829 := by
  have hp : Nat.Prime 829 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_144]

theorem primeByIndex_at_145 : primeByIndex 145 = 839 := by
  have hp : Nat.Prime 839 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_145]

theorem primeByIndex_at_146 : primeByIndex 146 = 853 := by
  have hp : Nat.Prime 853 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_146]

theorem primeByIndex_at_147 : primeByIndex 147 = 857 := by
  have hp : Nat.Prime 857 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_147]

theorem primeByIndex_at_148 : primeByIndex 148 = 859 := by
  have hp : Nat.Prime 859 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_148]

theorem primeByIndex_at_149 : primeByIndex 149 = 863 := by
  have hp : Nat.Prime 863 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_149]

theorem primeByIndex_at_150 : primeByIndex 150 = 877 := by
  have hp : Nat.Prime 877 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_150]

theorem primeByIndex_at_151 : primeByIndex 151 = 881 := by
  have hp : Nat.Prime 881 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_151]

theorem primeByIndex_at_152 : primeByIndex 152 = 883 := by
  have hp : Nat.Prime 883 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_152]

theorem primeByIndex_at_153 : primeByIndex 153 = 887 := by
  have hp : Nat.Prime 887 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_153]

theorem primeByIndex_at_154 : primeByIndex 154 = 907 := by
  have hp : Nat.Prime 907 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_154]

theorem primeByIndex_at_155 : primeByIndex 155 = 911 := by
  have hp : Nat.Prime 911 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_155]

theorem primeByIndex_at_156 : primeByIndex 156 = 919 := by
  have hp : Nat.Prime 919 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_156]

theorem primeByIndex_at_157 : primeByIndex 157 = 929 := by
  have hp : Nat.Prime 929 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_157]

theorem primeByIndex_at_158 : primeByIndex 158 = 937 := by
  have hp : Nat.Prime 937 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_158]

theorem primeByIndex_at_159 : primeByIndex 159 = 941 := by
  have hp : Nat.Prime 941 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_159]

theorem primeByIndex_at_160 : primeByIndex 160 = 947 := by
  have hp : Nat.Prime 947 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_160]

theorem primeByIndex_at_161 : primeByIndex 161 = 953 := by
  have hp : Nat.Prime 953 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_161]

theorem primeByIndex_at_162 : primeByIndex 162 = 967 := by
  have hp : Nat.Prime 967 := by norm_num only
  rw [primeByIndex, ← Nat.nth_count hp,
    count_prime_at_162]

end PseudoPrime.NumberTheory
