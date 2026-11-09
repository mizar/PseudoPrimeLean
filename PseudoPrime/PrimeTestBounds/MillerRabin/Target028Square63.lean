/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Square100

/-! # Coefficient 0.28 for square divisors through scale 63 -/

@[expose] public section

-- The checked weighted-count row requires deeper reduction.
set_option maxRecDepth 32768

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The checked supply through 373 covers square factors at scales between
42.5 and 63. The two budgets cover the large factors, and the smaller supply
handles the remaining factors. -/
theorem exists_prime_reject_028_square_425_63 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hL : (85 / 2 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 63) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hbudget : (373 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  have hpmax : p ≤ 68854718408873 := by
    have hlog :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 68854718408873 46 32 (63 / 2) 33 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
    apply square_factor_le_of_log_bound hn hp hdiv (W := 68854718408873) (by decide)
    norm_num only [Nat.cast_ofNat]
    linarith only [hU, hlog]
  by_cases h0 : p ≤ 2087485596
  · exact exists_prime_reject_028_square_small_factor hn ho hp hdiv (by linarith only [hL]) h0
  · have hbig0 : 2087485597 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge h0)
    have hcost0 : (414 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
      apply square_factor_budget_of_log (H := 414) (W := 2087485597) (by decide) hbig0
      norm_num only [Nat.cast_ofNat]
      nlinarith only [square_factor_stage_log0]
    by_cases h1 : p ≤ 1488482619460
    · have hc : p ≤ primeSeed373Row14.getD 414 0 := by
        change p ≤ 1488482619460
        exact h1
      obtain ⟨r, hr, hb, hf⟩ :=
        exists_prime_reject_square_seed373 hn ho hp hdiv 414 (by decide) hc hcost0
      exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hbudget, hf⟩
    · have hbig1 : 1488482619461 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge h1)
      have hcost1 : (500 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
        apply square_factor_budget_of_log (H := 500) (W := 1488482619461) (by decide) hbig1
        norm_num only [Nat.cast_ofNat]
        nlinarith only [square_factor_stage_log1]
      have hc : p ≤ primeSeed373Row14.getD 500 0 := by
        change p ≤ 68854718408873
        exact hpmax
      obtain ⟨r, hr, hb, hf⟩ :=
        exists_prime_reject_square_seed373 hn ho hp hdiv 500 (by decide) hc hcost1
      exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hbudget, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
