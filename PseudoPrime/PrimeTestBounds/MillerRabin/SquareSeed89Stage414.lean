/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed89Count358
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeCountExtend
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedCountWitness

/-! # Weighted square-divisor supply and factor bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 32768 in
/-- The checked tail at budget 358 and nine possible powers of the first
prime yield a lower count at budget 414 without another large table. -/
theorem primeSeed89_count414_lower : 2087485596 ≤ weightedPrimeCount id primeSeed89Weights 414 := by
  have hc := primeSeed89_checked358
  change
    (weightedPrimeRowCheck 7 358 (primeSeed89Tail358.headD #[]) primeSeed89Row358 &&
        weightedPrimeTableCheck 358 (primeSeed89Weights.drop 1)
          (primeSeed89Tail358.headD #[] :: primeSeed89Tail358.drop 1)) =
      true at hc
  have ht := (Bool.and_eq_true _ _).mp hc
  have hs :=
    weightedPrimeTableCheck_sound 358 (primeSeed89Weights.drop 1) (primeSeed89Tail358.headD #[])
      (primeSeed89Tail358.drop 1) ht.2 358 (by decide)
  have heq : weightedPrimeCount id (primeSeed89Weights.drop 1) 358 = 231942844 := by
    rw [← hs]
    rfl
  have hl := weightedPrimeCount_repeat_lower 7 358 8 (primeSeed89Weights.drop 1) (by decide)
  change
    9 * weightedPrimeCount id (primeSeed89Weights.drop 1) 358 ≤
      weightedPrimeCount id primeSeed89Weights 414 at hl
  rw [heq] at hl
  exact hl

/-- A prime-square divisor at scale at most 42.5 has base at most
2087485596, by a rational logarithm certificate. -/
theorem square_factor_le_2087485596 {n p : ℕ} (hn : 1 < n) (hdiv : p ^ 2 ∣ n)
    (hU : Real.log n ≤ (85 / 2 : ℝ)) : p ≤ 2087485596 := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 4357596113507475216 62 32 (85 / 2) 44 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hnle : n ≤ 4357596113507475216 := by
    have hlog : Real.log (n : ℝ) ≤ Real.log (4357596113507475216 : ℝ) := hU.trans hcert
    exact_mod_cast
      (Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
            (by norm_num only : (0 : ℝ) < 4357596113507475216)).mp
        hlog
  have hpsq : p ^ 2 ≤ 4357596113507475216 := (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv).trans hnle
  nlinarith only [hpsq]

/-- The square of an integer at least 1054033526 has logarithm strictly
above the budget 414/10. -/
theorem square_factor_budget_414 {p : ℕ} (hbig : 1054033526 ≤ p) :
    (414 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1054033526 30 32 (2075 / 100) 22 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 1054033526) (Nat.cast_le.mpr hbig)
  rw [Nat.cast_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [h, hl]

/-- The lower count at budget 414 yields an original-input rejecting prime
when the square divisor is within its count and exceeds its cost. -/
theorem exists_prime_reject_square_seed89_414 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hbound : p ≤ 2087485596)
    (hbudget : (414 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ 89 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  let : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  let H := (powMonoidHom (n - 1) : (ZMod (p ^ 2))ˣ →* (ZMod (p ^ 2))ˣ).ker
  have hcard : Nat.card H < weightedPrimeCount id primeSeed89Weights 414 := by
    change Nat.card (powMonoidHom (n - 1) : (ZMod (p ^ 2))ˣ →* (ZMod (p ^ 2))ˣ).ker < _
    rw [NumberTheory.card_local_fermat_kernel_prime_pow hn hp hp2 (by decide : 0 < 2) hdiv]
    exact
      (Nat.gcd_le_left (n - 1) (Nat.sub_pos_of_lt hp.one_lt)).trans_lt
        ((Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le (hbound.trans primeSeed89_count414_lower))
  exact
    exists_prime_reject_of_weight_list H primeSeed89Primes primeSeed89Weights 89 414
      primeSeed89Weight 10 (by norm_num only) (pow_pos hp.pos 2) primeSeed89_labels.1
      (fun r hr ↦ (primeSeed89_prime_supply r hr).1) (fun r hr ↦ (primeSeed89_prime_supply r hr).2)
      primeSeed89_labels.2.2 primeSeed89_weight_bounds primeSeed89_labels.2.1 hbudget hcard
      (fun r hr ↦ PrimeTest.strongMR_local_divisorKernel hn ho hdiv hr)

end PseudoPrime.PrimeTestBounds.MillerRabin
