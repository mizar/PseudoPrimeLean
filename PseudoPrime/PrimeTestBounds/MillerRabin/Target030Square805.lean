/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Square394
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeCountExtend
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030SquareMiddle

/-! # Square-divisor coverage through logarithmic scale 80.5 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 32768 in
/-- The checked tail at budget 358 and nine possible powers of the first
prime yield a lower count at budget 414 without another large table. -/
theorem target030Seed89_count414_lower :
    2087485596 ≤ weightedPrimeCount id target030Seed89Weights 414 := by
  have hc := target030Seed89_checked358
  change
    (weightedPrimeRowCheck 7 358 (target030Seed89Tail358.headD #[]) target030Seed89Row358 &&
        weightedPrimeTableCheck 358 (target030Seed89Weights.drop 1)
          (target030Seed89Tail358.headD #[] :: target030Seed89Tail358.drop 1)) =
      true at hc
  have ht := (Bool.and_eq_true _ _).mp hc
  have hs :=
    weightedPrimeTableCheck_sound 358 (target030Seed89Weights.drop 1)
      (target030Seed89Tail358.headD #[]) (target030Seed89Tail358.drop 1) ht.2 358 (by decide)
  have heq : weightedPrimeCount id (target030Seed89Weights.drop 1) 358 = 231942844 := by
    rw [← hs]
    rfl
  have hl := weightedPrimeCount_repeat_lower 7 358 8 (target030Seed89Weights.drop 1) (by decide)
  change
    9 * weightedPrimeCount id (target030Seed89Weights.drop 1) 358 ≤
      weightedPrimeCount id target030Seed89Weights 414 at hl
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
  have hcard : Nat.card H < weightedPrimeCount id target030Seed89Weights 414 := by
    change Nat.card (powMonoidHom (n - 1) : (ZMod (p ^ 2))ˣ →* (ZMod (p ^ 2))ˣ).ker < _
    rw [NumberTheory.card_local_fermat_kernel_prime_pow hn hp hp2 (by decide : 0 < 2) hdiv]
    exact
      (Nat.gcd_le_left (n - 1) (Nat.sub_pos_of_lt hp.one_lt)).trans_lt
        ((Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le
          (hbound.trans target030Seed89_count414_lower))
  exact
    exists_prime_reject_of_weight_list H target030Seed89Primes target030Seed89Weights 89 414
      target030Seed89Weight 10 (by norm_num only) (pow_pos hp.pos 2) target030Seed89_labels.1
      (fun r hr ↦ (target030Seed89_prime_supply r hr).1)
      (fun r hr ↦ (target030Seed89_prime_supply r hr).2) target030Seed89_labels.2.2
      target030Seed89_weight_bounds target030Seed89_labels.2.1 hbudget hcard
      (fun r hr ↦ PrimeTest.strongMR_local_divisorKernel hn ho hdiv hr)

/-- Under RH, every odd input with a prime-square divisor has a 0.30
rejecting prime through logarithmic scale 42.5. -/
theorem exists_prime_reject_03_square_8_to_425 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hRH : RiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 85 / 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h28 : Real.log n ≤ 28
  · exact exists_prime_reject_03_square_8_to_28 hn ho hp hdiv hRH hL h28
  · have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
    have hB : (89 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by nlinarith only [h28]
    by_cases hsmall : p ≤ 43
    · exact
        ⟨p, hp, (Nat.cast_le.mpr hsmall).trans ((by norm_num only : (43 : ℝ) ≤ 89).trans hB),
          PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hpn⟩
    · by_cases hmedium : p ≤ 809
      · obtain ⟨r, hr, hb, hf⟩ :=
          exists_prime_reject_square_seed43 hn ho hp hdiv hmedium
            (square_factor_budget_77 (prime_ge_47_of_gt_43 hp (Nat.lt_of_not_ge hsmall)))
        exact ⟨r, hr, (Nat.cast_le.mpr hb).trans ((by norm_num only : (43 : ℝ) ≤ 89).trans hB), hf⟩
      · by_cases hnext : p ≤ 19639
        · have hp810 : 810 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge hmedium)
          obtain ⟨r, hr, hb, hf⟩ :=
            exists_prime_reject_square_seed43_133 hn ho hp hdiv hnext
              (square_factor_budget_133 hp810)
          exact
            ⟨r, hr, (Nat.cast_le.mpr hb).trans ((by norm_num only : (43 : ℝ) ≤ 89).trans hB), hf⟩
        · by_cases hthird : p ≤ 1372508
          · have hp19640 : 19640 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge hnext)
            obtain ⟨r, hr, hb, hf⟩ :=
              exists_prime_reject_square_seed89_197 hn ho hp hdiv hthird
                (square_factor_budget_197 hp19640)
            exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩
          · by_cases hfourth : p ≤ 59789534
            · have hbig : 1372509 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge hthird)
              obtain ⟨r, hr, hb, hf⟩ :=
                exists_prime_reject_square_seed89_282 hn ho hp hdiv hfourth
                  (square_factor_budget_282 hbig)
              exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩
            · by_cases hfifth : p ≤ 1054033525
              · have hbig : 59789535 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge hfourth)
                obtain ⟨r, hr, hb, hf⟩ :=
                  exists_prime_reject_square_seed89_358 hn ho hp hdiv hfifth
                    (square_factor_budget_358 hbig)
                exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩
              · have hbig : 1054033526 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge hfifth)
                obtain ⟨r, hr, hb, hf⟩ :=
                  exists_prime_reject_square_seed89_414 hn ho hp hdiv
                    (square_factor_le_2087485596 hn hdiv hU) (square_factor_budget_414 hbig)
                exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

/-- Under RH, the extended count and three existing coverage rows yield a
0.30 rejecting prime for a square divisor throughout `[8, 80.5]`. -/
theorem exists_prime_reject_03_square_8_to_805 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hRH : RiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 161 / 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h : Real.log n ≤ 85 / 2
  · exact exists_prime_reject_03_square_8_to_425 hn ho hp hdiv hRH hL h
  · exact exists_prime_reject_03_square_mid hn ho hp hdiv hRH (le_of_not_ge h) hU

end PseudoPrime.PrimeTestBounds.MillerRabin
