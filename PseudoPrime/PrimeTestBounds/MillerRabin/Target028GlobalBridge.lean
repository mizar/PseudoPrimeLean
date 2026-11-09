/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028SmallInputs
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeLogSquareBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Log8
public import PseudoPrime.PrimeTestBounds.MillerRabin.LogNineComparison
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Global maximum cutoff from the logarithmic-scale witness -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A 0.28 witness theorem for all odd composites of logarithmic scale at
least 8 implies the global maximum-cutoff theorem. The remaining inputs are
covered by the certified small-input classification. -/
theorem exists_prime_reject_028_global_of_log8
    (hlog :
      ∀ n : ℕ,
        1 < n →
          Odd n →
          ¬n.Prime →
          (8 : ℝ) ≤ Real.log n →
          ∃ p : ℕ,
            p.Prime ∧
              (p : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
              ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n))
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((7 / 25 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hN : n < 3000
  · exact exists_prime_reject_028_small hn ho hc hN
  have hn3000 : 3000 ≤ n := Nat.le_of_not_gt hN
  have hlog3000 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 3000 12 12 8 (801 / 100) = true by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hlog3000
  have ht := Real.log_le_log (by norm_num only : (0 : ℝ) < 3000) (Nat.cast_le.mpr hn3000)
  have h8 : (8 : ℝ) ≤ Real.log n := hlog3000.trans ht
  obtain ⟨p, hp, hb, hf⟩ := hlog n hn ho hc h8
  exact ⟨p, hp, hb.trans (le_max_right _ _), hf⟩

/-- Under GRH, every odd composite above one has a rejecting prime within
`max 2 ((7/25) * log n ^ 2)`. The small-input classification and the
logarithmic-scale witness together give the global bound. -/
theorem exists_prime_reject_028_global
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((7 / 25 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply exists_prime_reject_028_global_of_log8 ?_ hn ho hc
  intro m hm hodd hcomposite hscale
  exact exists_prime_reject_028_log8 hm hodd hcomposite hGRH hscale

/-- A 0.28 rejecting-prime theorem at logarithmic scale at least 8 gives the
global prime-base criterion. Small inputs use the certified finite bound, and
prime acceptance follows from the base-two and log-square results. -/
theorem prime_millerRabin_028_of_log8
    (hlog :
      ∀ n : ℕ,
        1 < n →
          Odd n →
          ¬n.Prime →
          (8 : ℝ) ≤ Real.log n →
          ∃ p : ℕ,
            p.Prime ∧
              (p : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
              ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n))
    {n : ℕ} (hn : 1 < n) (ho : Odd n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1)
    (∀ p : ℕ,
        Nat.Prime p →
          (p : ℝ) ≤ max 2 ((7 / 25 : ℝ) * Real.log n ^ 2) →
          ((p : ZMod n) ^ d = 1 ∨ ∃ j : ℕ, j < s ∧ (p : ZMod n) ^ (2 ^ j * d) = -1)) ↔
      Nat.Prime n := by
  constructor
  · intro hpass
    by_contra hc
    obtain ⟨p, hp, hb, hf⟩ := exists_prime_reject_028_global_of_log8 hlog hn ho hc
    exact hf (hpass p hp hb)
  · intro hp p hprime hb
    rcases (le_max_iff.mp hb) with htwo | hlarge
    · have hp2 : p = 2 := Nat.le_antisymm (by exact_mod_cast htwo) hprime.two_le
      subst p
      exact
        PrimeTest.strongMillerRabinWithBase_eq_true_iff_pass.mp
          (PrimeTest.strongMillerRabinBase2_of_prime_of_ne_two hp (ho.ne_two_of_dvd_nat dvd_rfl))
    · by_contra hnot
      have hbound : (p : ℝ) ≤ Real.log n ^ 2 := by nlinarith only [hlarge, sq_nonneg (Real.log n)]
      exact
        no_prime_millerRabin_witness_le_log_sq_of_prime ho hp
          ⟨p, hprime, hbound, PrimeTest.not_strongMillerRabinPass_iff.mp hnot⟩

/-- Under GRH, the global 0.28 prime-base test characterizes odd primes above
one. The logarithmic-scale witness supplies the composite direction and the
base-two and log-square results supply the prime direction. -/
theorem prime_millerRabin_028_criterion
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1)
    (∀ p : ℕ,
        Nat.Prime p →
          (p : ℝ) ≤ max 2 ((7 / 25 : ℝ) * Real.log n ^ 2) →
          ((p : ZMod n) ^ d = 1 ∨ ∃ j : ℕ, j < s ∧ (p : ZMod n) ^ (2 ^ j * d) = -1)) ↔
      Nat.Prime n := by
  apply prime_millerRabin_028_of_log8 ?_ hn ho
  intro m hm hodd hcomposite hscale
  exact exists_prime_reject_028_log8 hm hodd hcomposite hGRH hscale

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
The 0.28 criterion gives the composite direction via cutoff comparison; prime acceptance
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
    · apply (prime_millerRabin_028_criterion hGRH hn ho).mp
      intro p hp hb
      exact hpass p hp (hb.trans (max_028_le_logb_nine_sq (Nat.cast_le.mpr h9)))
    · have hsmall : ∀ k : Fin 9, 1 < k.val → Odd k.val → k.val.Prime := by decide +kernel
      exact hsmall ⟨n, Nat.lt_of_not_ge h9⟩ hn ho
  · intro hp p hprime hb
    by_contra hnot
    have hbound : (p : ℝ) ≤ Real.log n ^ 2 := hb.trans (log_nine_cutoff_le n)
    exact
      no_prime_millerRabin_witness_le_log_sq_of_prime ho hp
        ⟨p, hprime, hbound, PrimeTest.not_strongMillerRabinPass_iff.mp hnot⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
