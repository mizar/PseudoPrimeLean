/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquareCommon
import PseudoPrime.PrimeTestBounds.MillerRabin.SquareSeed89Stage414
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed373Count
import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeCountExtend

/-! # Square-factor witnesses on logarithmic scales 55 to 63 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A square divisor of an input of logarithmic scale at most 63 has base at most
60000000000000. A rational logarithm certificate bounds its square. -/
private theorem bound63 {n p : ℕ} (hn : 1 < n) (hdiv : p ^ 2 ∣ n) (hU : Real.log n ≤ (63 : ℝ)) :
    p ≤ 60000000000000 := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 3600000000000000000000000000 92 32 63 65 = true by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hcert
  have hnle : n ≤ 3600000000000000000000000000 := by
    have hlog : Real.log (n : ℝ) ≤ Real.log (3600000000000000000000000000 : ℝ) := hU.trans hcert
    exact_mod_cast
      (Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
            (by norm_num only : (0 : ℝ) < 3600000000000000000000000000)).mp
        hlog
  have hpsq : p ^ 2 ≤ 3600000000000000000000000000 :=
    (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv).trans hnle
  nlinarith only [hpsq]

/-- A base at least 1000000000001 has square logarithm above budget 552/10.
A rational logarithm certificate supplies the strict margin. -/
private theorem budget552 {p : ℕ} (hbig : 1000000000001 ≤ p) :
    (552 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1000000000001 40 32 (2761 / 100) 29 = true by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 1000000000001) (Nat.cast_le.mpr hbig)
  rw [Nat.cast_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [h, hl]

/-- A checked weighted count exceeding the square kernel yields a rejecting prime
at most 373. The budget ensures that the counted products are distinct modulo the square. -/
private theorem square373_count {n p H : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hcount : p - 1 < weightedPrimeCount id primeSeed373Weights H)
    (hbudget : (H : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ 373 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  let : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  let K := (powMonoidHom (n - 1) : (ZMod (p ^ 2))ˣ →* (ZMod (p ^ 2))ˣ).ker
  have hcard : Nat.card K < weightedPrimeCount id primeSeed373Weights H := by
    change Nat.card (powMonoidHom (n - 1) : (ZMod (p ^ 2))ˣ →* (ZMod (p ^ 2))ˣ).ker < _
    rw [NumberTheory.card_local_fermat_kernel_prime_pow hn hp hp2 (by decide : 0 < 2) hdiv]
    exact (Nat.gcd_le_left (n - 1) (Nat.sub_pos_of_lt hp.one_lt)).trans_lt hcount
  exact
    exists_prime_reject_of_weight_list K primeSeed373Primes primeSeed373Weights 373 H
      primeSeed373Weight 10 (by norm_num only) (pow_pos hp.pos 2) primeSeed373_labels.1
      (fun r hr ↦ (primeSeed373_prime_supply r hr).1)
      (fun r hr ↦ (primeSeed373_prime_supply r hr).2) primeSeed373_labels.2.2
      primeSeed373_weight_bounds primeSeed373_labels.2.1 hbudget hcard
      (fun r hr ↦ PrimeTest.strongMR_local_divisorKernel hn ho hdiv hr)

/-- An odd input with a prime-square divisor and logarithm between 55 and 63 has
a quarter-square rejecting prime. Independent count stages cover the divisor sizes. -/
theorem quarter_square_55_63 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hdiv : p ^ 2 ∣ n)
    (hL : (55 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 63) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hB : (373 : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  by_cases hlow : p ≤ 1054033525
  · obtain ⟨r, hr, hb, hf⟩ := square_reject_le1054 hn ho hp hdiv hlow
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans ((by norm_num only : (89 : ℝ) ≤ 373).trans hB), hf⟩
  by_cases hmid : p ≤ 1000000000000
  · have hc := primeSeed373_count_lower 414 (by decide)
    rw [show primeSeed373Row14.getD 414 0 = 1488482619460 by decide +kernel] at hc
    have hcount : p - 1 < weightedPrimeCount id primeSeed373Weights 414 :=
      (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le
        (hmid.trans ((by norm_num only : 1000000000000 ≤ 1488482619460).trans hc))
    obtain ⟨r, hr, hb, hf⟩ :=
      square373_count hn ho hp hdiv hcount
        (square_factor_budget_414 (Nat.succ_le_of_lt (Nat.lt_of_not_ge hlow)))
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩
  · have hc := primeSeed373_count_lower 500 (by decide)
    rw [show primeSeed373Row14.getD 500 0 = 68854718408873 by decide +kernel] at hc
    have hc' := hc.trans (weightedPrimeCount_mono id primeSeed373Weights (show 500 ≤ 552 by decide))
    have hcount : p - 1 < weightedPrimeCount id primeSeed373Weights 552 :=
      (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le
        ((bound63 hn hdiv hU).trans
          ((by norm_num only : 60000000000000 ≤ 68854718408873).trans hc'))
    obtain ⟨r, hr, hb, hf⟩ :=
      square373_count hn ho hp hdiv hcount (budget552 (Nat.succ_le_of_lt (Nat.lt_of_not_ge hmid)))
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
