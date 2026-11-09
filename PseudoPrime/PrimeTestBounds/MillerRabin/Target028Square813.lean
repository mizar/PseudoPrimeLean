/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Square100
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Seed1801

/-! # Square-divisor bridge near logarithmic scale 81 -/

@[expose] public section

set_option maxRecDepth 32768

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The reduced prime supply gives a square-divisor witness at most 1801 when
its grouped count exceeds the local kernel and the product cost fits. -/
theorem exists_prime_reject_square_seed1801 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (A k : ℕ) (hA : A ≤ 500)
    (hpC : p ≤ Nat.choose (205 + k) k * primeSeed373Row14.getD A 0)
    (hbudget : ((A + k * 76 : ℕ) : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ 1801 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  have hc : p - 1 < Nat.choose (205 + k) k * primeSeed373Row14.getD A 0 :=
    (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le hpC
  exact
    exists_prime_reject_prime_pow_count hn ho hp hp2 (by decide : 0 < 2) hdiv
      target028Seed1801Primes target028Seed1801Weights 1801 (A + k * 76)
      (Nat.choose (205 + k) k * primeSeed373Row14.getD A 0) primeSeed1849Weight 10
      (by norm_num only) target028Seed1801_labels.1 (fun r hr ↦ (target028Seed1801_supply r hr).1)
      (fun r hr ↦ (target028Seed1801_supply r hr).2) target028Seed1801_labels.2.2
      (fun r hr ↦ primeSeed1849_weight_bounds r (target028Seed1801_subset r hr))
      target028Seed1801_labels.2.1 hbudget hc (target028Seed1801_count A k hA)

/-- Under the logarithmic bounds 80.5 and 81.3, the reduced supply fits the
0.28 cutoff and its grouped counts cover all remaining square factors. -/
theorem exists_prime_reject_028_square_805_813 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hL : (161 / 2 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 813 / 10) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hbudget : (1801 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  have hpmax : p ≤ 1468051451195581233 := by
    have hlog :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 1468051451195581233 61 32 41 43 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat] at hlog
    apply square_factor_le_of_log_bound hn hp hdiv (W := 1468051451195581233) (by decide)
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
        ⟨r, hr, (Nat.cast_le.mpr hb).trans ((by norm_num only : (373 : ℝ) ≤ 1801).trans hbudget),
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
          ⟨r, hr, (Nat.cast_le.mpr hb).trans ((by norm_num only : (373 : ℝ) ≤ 1801).trans hbudget),
            hf⟩
      · have hbig2 : 68854718408874 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge h2)
        have hcost2 : (576 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
          apply square_factor_budget_of_log (H := 576) (W := 68854718408874) (by decide) hbig2
          norm_num only [Nat.cast_ofNat]
          nlinarith only [square_factor_stage_log2]
        by_cases h3 : p ≤ 14184071992227838
        · have hc : p ≤ Nat.choose (205 + 1) 1 * primeSeed373Row14.getD 500 0 := by
            change p ≤ 14184071992227838
            exact h3
          obtain ⟨r, hr, hb, hf⟩ :=
            exists_prime_reject_square_seed1801 hn ho hp hdiv 500 1 (by decide) hc hcost2
          exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hbudget, hf⟩
        · have hbig3 : 14184071992227839 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge h3)
          have hcost3 : (652 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
            have hlog :=
              (Analysis.rationalLogIntervalCheck_sound
                  (show Analysis.rationalLogIntervalCheck 14184071992227839 54 32 33 39 = true from
                    by decide +kernel)).1
            norm_num only [Rat.cast_ofNat] at hlog
            apply square_factor_budget_of_log (H := 652) (W := 14184071992227839) (by decide) hbig3
            norm_num only [Nat.cast_ofNat]
            nlinarith only [hlog]
          have hc : p ≤ Nat.choose (205 + 2) 2 * primeSeed373Row14.getD 500 0 := by
            change p ≤ 1468051451195581233
            exact hpmax
          obtain ⟨r, hr, hb, hf⟩ :=
            exists_prime_reject_square_seed1801 hn ho hp hdiv 500 2 (by decide) hc hcost3
          exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hbudget, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
