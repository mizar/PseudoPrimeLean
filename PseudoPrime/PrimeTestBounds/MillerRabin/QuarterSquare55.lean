/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed373Count
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquareCommon
import PseudoPrime.PrimeTestBounds.MillerRabin.SquareSeed89Stage414

/-! # Square-factor witnesses on logarithmic scales 42.5 to 55 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A square divisor of an input with logarithm at most 55 has base at most one trillion.
A rational logarithm certificate bounds the square and hence its base. -/
private theorem bound55 {n p : ℕ} (hn : 1 < n) (hdiv : p ^ 2 ∣ n) (hU : Real.log n ≤ (55 : ℝ)) :
    p ≤ 1000000000000 := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1000000000000000000000000 80 32 55 57 = true by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hcert
  have hnle : n ≤ 1000000000000000000000000 := by
    have hlog : Real.log (n : ℝ) ≤ Real.log (1000000000000000000000000 : ℝ) := hU.trans hcert
    exact_mod_cast
      (Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
            (by norm_num only : (0 : ℝ) < 1000000000000000000000000)).mp
        hlog
  have hpsq : p ^ 2 ≤ 1000000000000000000000000 :=
    (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv).trans hnle
  nlinarith only [hpsq]

/-- A prime-square divisor whose base is within the checked count and whose logarithm
exceeds the budget has a rejecting prime at most 373. The weighted count exceeds the kernel. -/
private theorem square373 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hdiv : p ^ 2 ∣ n)
    (hbound : p ≤ 1000000000000) (hbudget : (414 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ 373 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  let : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  let H := (powMonoidHom (n - 1) : (ZMod (p ^ 2))ˣ →* (ZMod (p ^ 2))ˣ).ker
  have hcount : 1000000000000 ≤ weightedPrimeCount id primeSeed373Weights 414 := by
    have h := primeSeed373_count_lower 414 (by decide)
    rw [show primeSeed373Row14.getD 414 0 = 1488482619460 by decide +kernel] at h
    exact (by norm_num only : 1000000000000 ≤ 1488482619460).trans h
  have hcard : Nat.card H < weightedPrimeCount id primeSeed373Weights 414 := by
    change Nat.card (powMonoidHom (n - 1) : (ZMod (p ^ 2))ˣ →* (ZMod (p ^ 2))ˣ).ker < _
    rw [NumberTheory.card_local_fermat_kernel_prime_pow hn hp hp2 (by decide : 0 < 2) hdiv]
    exact
      (Nat.gcd_le_left (n - 1) (Nat.sub_pos_of_lt hp.one_lt)).trans_lt
        ((Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le (hbound.trans hcount))
  exact
    exists_prime_reject_of_weight_list H primeSeed373Primes primeSeed373Weights 373 414
      primeSeed373Weight 10 (by norm_num only) (pow_pos hp.pos 2) primeSeed373_labels.1
      (fun r hr ↦ (primeSeed373_prime_supply r hr).1)
      (fun r hr ↦ (primeSeed373_prime_supply r hr).2) primeSeed373_labels.2.2
      primeSeed373_weight_bounds primeSeed373_labels.2.1 hbudget hcard
      (fun r hr ↦ PrimeTest.strongMR_local_divisorKernel hn ho hdiv hr)

/-- An odd integer with a prime-square divisor and logarithm between 42.5
and 55 has a rejecting prime below one quarter of its squared logarithm.
Direct divisors and existing weighted-product stages supply primes at most 373. -/
theorem quarter_square_425_55 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hdiv : p ^ 2 ∣ n)
    (hL : (85 / 2 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 55) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hB : (373 : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  by_cases h : p ≤ 1054033525
  · obtain ⟨r, hr, hb, hf⟩ := square_reject_le1054 hn ho hp hdiv h
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans ((by norm_num only : (89 : ℝ) ≤ 373).trans hB), hf⟩
  · obtain ⟨r, hr, hb, hf⟩ :=
      square373 hn ho hp hdiv (bound55 hn hdiv hU)
        (square_factor_budget_414 (Nat.succ_le_of_lt (Nat.lt_of_not_ge h)))
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
