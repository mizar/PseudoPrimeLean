/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeEleventhsBridge
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import PseudoPrime.PrimeTestBounds.MillerRabin.LogNineComparison

/-! # Base-nine Miller–Rabin criterion -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The base-nine cutoff lies below the squared natural logarithm. A lower
bound on `log 9` gives the comparison used for prime acceptance. -/
private theorem log_nine_cutoff_le (x : ℝ) : 2 * (Real.logb 9 x) ^ 2 ≤ (Real.log x) ^ 2 := by
  have hlog : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hlow : (219 / 100 : ℝ) < Real.log 9 := by linarith only [hlog, Real.log_three_gt_d9]
  have hsquare : (2 : ℝ) ≤ (Real.log 9) ^ 2 := by
    nlinarith only [hlow, sq_nonneg (Real.log 9 - 219 / 100)]
  change 2 * (Real.log x / Real.log 9) ^ 2 ≤ _
  rw [div_pow, ← mul_div_assoc]
  apply (div_le_iff₀ (sq_pos_of_pos (lt_trans (by norm_num only) hlow))).2
  have hmul := mul_nonneg (sub_nonneg.mpr hsquare) (sq_nonneg (Real.log x))
  nlinarith only [hmul]

/-- Under GRH, prime-base tests up to the base-nine cutoff characterize odd primes above one.
The 3/11 criterion gives the composite direction via cutoff comparison; prime acceptance
follows from the log-square bound. Odd inputs below nine are checked separately. -/
theorem prime_millerRabin_log_nine_criterion
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1)
    (∀ p : ℕ,
        Nat.Prime p →
          (p : ℝ) ≤ 2 * (Real.logb 9 n) ^ 2 →
          ((p : ZMod n) ^ d = 1 ∨ ∃ j : ℕ, j < s ∧ (p : ZMod n) ^ (2 ^ j * d) = -1)) ↔
      Nat.Prime n := by
  constructor
  · intro hpass
    by_cases h9 : 9 ≤ n
    · apply (prime_millerRabin_027_criterion hGRH hn ho).mp
      intro p hp hb
      have hcoef : (3 / 11 : ℝ) ≤ 7 / 25 := by norm_num only
      have hcut : max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ≤ max 2 ((7 / 25 : ℝ) * Real.log n ^ 2) :=
        max_le_max le_rfl (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))
      exact hpass p hp (hb.trans (hcut.trans (max_028_le_logb_nine_sq (Nat.cast_le.mpr h9))))
    · have hsmall : ∀ k : Fin 9, 1 < k.val → Odd k.val → k.val.Prime := by decide +kernel
      exact hsmall ⟨n, Nat.lt_of_not_ge h9⟩ hn ho
  · intro hp p hprime hb
    by_contra hnot
    have hbound : (p : ℝ) ≤ Real.log n ^ 2 := hb.trans (log_nine_cutoff_le n)
    exact
      no_prime_millerRabin_witness_le_log_sq_of_prime ho hp
        ⟨p, hprime, hbound, PrimeTest.not_strongMillerRabinPass_iff.mp hnot⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
