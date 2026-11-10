/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquareFirst
public import PseudoPrime.PrimeTestBounds.MillerRabin.SignedPrimeProductTransfer
public import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeSmallFactor

/-! # Signed-product counting for the first quarter-bound semiprime cell -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The six-prime weighted family contains 73 products through budget 49.
The checked recurrence supplies the count for the extended first cell. -/
theorem quarterFirst_family_card49 :
    (weightedPrimeFamily quarterFirstPrimes.toFinset primeSeed19Weight 49).card = 73 := by
  have h :=
    (weightedPrimeCount_weights_eq_card primeSeed19Weight 49 quarterFirstPrimes quarterFirstWeights
          quarterFirst_labels.1 quarterFirst_labels.2.2 quarterFirst_labels.2.1).symm.trans
      ((weightedPrimeTableCheck_sound 49 quarterFirstWeights quarterFirstRow quarterFirstTail
          quarterFirst_checked 49 (by decide)).symm)
  change (weightedPrimeFamily quarterFirstPrimes.toFinset primeSeed19Weight 49).card = 73 at h
  exact h

/-- On `8 ≤ log n ≤ 10.649`, a semiprime has a quarter-square witness once
its branch `log q ≤ 5.666` is supplied. For larger `q`, the 73 checked products
and their negatives exceed the local Fermat-kernel bound. -/
theorem quarter_semiprime_first_of_local {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hprod : n = p * q) (hL : (8 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 10649 / 1000)
    (hlocal :
      Real.log q ≤ (2833 / 500 : ℝ) →
        ∃ r : ℕ,
          r.Prime ∧
            (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
            ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := quarterFirstPrimes.toFinset
  let w := primeSeed19Weight
  let F := weightedPrimeFamily S w 49
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
    (prime_seed19_prime_supply r (List.mem_of_mem_take (List.mem_toFinset.mp hr))).1
  have hbound : ∀ r ∈ S, r ≤ 13 := by
    intro r hr
    have hm : r ∈ quarterFirstPrimes := List.mem_toFinset.mp hr
    simp only [quarterFirstPrimes, primeSeed19Primes, List.take_succ_cons, List.take_zero,
      List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h <;> subst r <;> decide
  have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
    prime_seed19_weight_bounds r (List.mem_of_mem_take (List.mem_toFinset.mp hr))
  have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦ quarterFirst_labels.2.2 r (List.mem_toFinset.mp hr)
  have hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S := fun T hT ↦
    ((mem_weightedPrimeFamily S w 49 hwpos T).mp hT).1
  have hcost : ∀ T ∈ F, (T.map w).sum ≤ 49 := fun T hT ↦
    ((mem_weightedPrimeFamily S w 49 hwpos T).mp hT).2
  have hc : F.card = 73 := quarterFirst_family_card49
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 146 8 32 (4983 / 1000) 6 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hD : (4983 / 1000 : ℝ) ≤ Real.log ((2 * F.card : ℕ) : ℝ) := by
    rw [hc]
    norm_num only
    exact hlog
  have hA : Real.log 2 + (49 : ℝ) / 10 ≤ 2833 / 500 := by linarith only [Real.log_two_lt_d9]
  have hB : (13 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  apply
    exists_prime_reject_signed_cell hn ho hp hq hprod S F 13 49 w 10 (by norm_num only) hsub hprime
      hbound hw hcost hA hD hB
  intro hqsmall
  apply hlocal
  have hmax : max (2833 / 500 : ℝ) (Real.log n - 4983 / 1000) ≤ 2833 / 500 := by
    apply max_le le_rfl
    linarith only [hU]
  exact hqsmall.trans hmax

/-- For a product of distinct ordered primes with `log q ≤ 5.666`, one of the
primes at most 13 rejects the input. Otherwise the proper local Fermat kernel
contains `-1` and all such primes, contradicting small-prime generation. -/
theorem quarter_semiprime_first_local {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q) (hL : (8 : ℝ) ≤ Real.log n)
    (hqsmall : Real.log q ≤ 2833 / 500) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 289 9 64 (28331 / 5000) 6 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hqR : (q : ℝ) < 289 :=
    (Real.log_lt_log_iff (Nat.cast_pos.mpr hq.pos) (by norm_num only : (0 : ℝ) < 289)).mp
      (by linarith only [hqsmall, hcert])
  have hsize : q < (16 + 1) ^ 2 := by
    norm_num only
    exact_mod_cast hqR
  obtain ⟨r, hr, hrB, hf⟩ :=
    semiprime_small_factor_witness hn ho hp hq hpq hprod (by decide : 0 < 16) hsize
  have h16 : (16 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  exact ⟨r, hr, (Nat.cast_le.mpr hrB).trans h16, hf⟩

/-- Every odd product of two distinct primes in the first logarithmic cell
has an unconditional quarter-square rejecting prime. Small local moduli are
handled by small-prime generation, and large ones by signed product counting. -/
theorem quarter_semiprime_first {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hL : (8 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 10649 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    quarter_semiprime_first_of_local hn ho hp hq hprod hL hU
      (quarter_semiprime_first_local hn ho hp hq hpq hprod hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
