/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareGroupedSupply
public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareFactorStageLogs
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028SquareSmallFactor

/-! # Coefficient 0.28 for large square divisors -/

@[expose] public section

set_option maxRecDepth 32768

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For logarithm between 81.3 and 106, the weighted and grouped counts cover
all square factors with prime cutoffs bounded by the coefficient 0.28 target. -/
theorem exists_prime_reject_028_square_813_106 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hL : (813 / 10 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 106) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hbudget : (1849 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  have hpmax : p ≤ 245687718964671651701166 := by
    have hlog :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 245687718964671651701166 78 32 53 55 = true from
            by decide +kernel)).1
    norm_num only [Rat.cast_ofNat] at hlog
    apply square_factor_le_of_log_bound hn hp hdiv (W := 245687718964671651701166) (by decide)
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
      exact
        ⟨r, hr, (Nat.cast_le.mpr hb).trans ((by norm_num only : (373 : ℝ) ≤ 1849).trans hbudget),
          hf⟩
    · have hbig1 : 1488482619461 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge h1)
      have hcost1 : (500 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
        apply square_factor_budget_of_log (H := 500) (W := 1488482619461) (by decide) hbig1
        norm_num only [Nat.cast_ofNat]
        nlinarith only [square_factor_stage_log1]
      by_cases h2 : p ≤ 68854718408873
      · have hc : p ≤ primeSeed373Row14.getD 500 0 := by
          change p ≤ 68854718408873
          exact h2
        obtain ⟨r, hr, hb, hf⟩ :=
          exists_prime_reject_square_seed373 hn ho hp hdiv 500 (by decide) hc hcost1
        exact
          ⟨r, hr, (Nat.cast_le.mpr hb).trans ((by norm_num only : (373 : ℝ) ≤ 1849).trans hbudget),
            hf⟩
      · have hbig2 : 68854718408874 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge h2)
        have hcost2 : (576 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
          apply square_factor_budget_of_log (H := 576) (W := 68854718408874) (by decide) hbig2
          norm_num only [Nat.cast_ofNat]
          nlinarith only [square_factor_stage_log2]
        by_cases h3 : p ≤ 14459490865863330
        · have hc : p ≤ Nat.choose (209 + 1) 1 * primeSeed373Row14.getD 500 0 := by
            change p ≤ 14459490865863330
            exact h3
          obtain ⟨r, hr, hb, hf⟩ :=
            exists_prime_reject_square_seed1849 hn ho hp hdiv 500 1 (by decide) hc hcost2
          exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hbudget, hf⟩
        · have hbig3 : 14459490865863331 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge h3)
          have hcost3 : (652 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
            apply square_factor_budget_of_log (H := 652) (W := 14459490865863331) (by decide) hbig3
            norm_num only [Nat.cast_ofNat]
            nlinarith only [square_factor_stage_log3]
          by_cases h4 : p ≤ 1525476286348581315
          · have hc : p ≤ Nat.choose (209 + 2) 2 * primeSeed373Row14.getD 500 0 := by
              change p ≤ 1525476286348581315
              exact h4
            obtain ⟨r, hr, hb, hf⟩ :=
              exists_prime_reject_square_seed1849 hn ho hp hdiv 500 2 (by decide) hc hcost3
            exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hbudget, hf⟩
          · have hbig4 : 1525476286348581316 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge h4)
            have hcost4 : (728 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
              apply
                square_factor_budget_of_log (H := 728) (W := 1525476286348581316) (by decide) hbig4
              norm_num only [Nat.cast_ofNat]
              nlinarith only [square_factor_stage_log4]
            by_cases h5 : p ≤ 107800324235299746260
            · have hc : p ≤ Nat.choose (209 + 3) 3 * primeSeed373Row14.getD 500 0 := by
                change p ≤ 107800324235299746260
                exact h5
              obtain ⟨r, hr, hb, hf⟩ :=
                exists_prime_reject_square_seed1849 hn ho hp hdiv 500 3 (by decide) hc hcost4
              exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hbudget, hf⟩
            · have hbig5 : 107800324235299746261 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge h5)
              have hcost5 : (804 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
                apply
                  square_factor_budget_of_log (H := 804) (W := 107800324235299746261) (by decide)
                    hbig5
                norm_num only [Nat.cast_ofNat]
                nlinarith only [square_factor_stage_log5]
              by_cases h6 : p ≤ 5740367265529711488345
              · have hc : p ≤ Nat.choose (209 + 4) 4 * primeSeed373Row14.getD 500 0 := by
                  change p ≤ 5740367265529711488345
                  exact h6
                obtain ⟨r, hr, hb, hf⟩ :=
                  exists_prime_reject_square_seed1849 hn ho hp hdiv 500 4 (by decide) hc hcost5
                exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hbudget, hf⟩
              · have hbig6 : 5740367265529711488346 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge h6)
                have hcost6 : (880 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
                  apply
                    square_factor_budget_of_log (H := 880) (W := 5740367265529711488345) (by decide)
                      (le_trans (by decide) hbig6)
                  norm_num only [Nat.cast_ofNat]
                  nlinarith only [square_factor_stage_log6]
                have hc : p ≤ Nat.choose (209 + 5) 5 * primeSeed373Row14.getD 500 0 := by
                  change p ≤ 245687718964671651701166
                  exact hpmax
                obtain ⟨r, hr, hb, hf⟩ :=
                  exists_prime_reject_square_seed1849 hn ho hp hdiv 500 5 (by decide) hc hcost6
                exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hbudget, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
