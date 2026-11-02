/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsFiniteWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.SmallPointwiseBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointFiniteTuned

/-! # Global four-ninths witness bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH every odd composite above one has a prime Miller--Rabin witness
at most four ninths of the squared logarithm. Use the existing small-input and
fixed-prime certificates below the entrance, and the finite and high proofs above. -/
theorem exists_prime_witness_four_ninths {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases hlarge : (83 / 10 : ℝ) ≤ Real.log n
  · exact exists_prime_witness_four_ninths_log_ge hn ho hc hGRH hlarge
  by_cases hN : n < 3000
  · have hn9 : 9 ≤ n := by
      by_contra h9
      have hp : ∀ k : Fin 9, 1 < k.val → Odd k.val → k.val.Prime := by decide +kernel
      exact hc (hp ⟨n, Nat.lt_of_not_ge h9⟩ hn ho)
    have hlog9 :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 9 3 12 (219 / 100) (23 / 10) = true by
            decide +kernel)).1
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog9
    have hlogn := Real.log_le_log (by norm_num only : (0 : ℝ) < 9) (Nat.cast_le.mpr hn9)
    have hlog : (219 / 100 : ℝ) ≤ Real.log n := hlog9.trans hlogn
    have hs := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 219 / 100) hlog 2
    obtain ⟨r, hr, hb, hf⟩ := exists_prime_smallInterval hn ho hc hN
    refine ⟨r, hr, hb.trans ?_, hf⟩
    by_cases h : n < 2047
    · rw [smallIntervalBound, ite_eq_left h]
      nlinarith only [hs]
    · rw [smallIntervalBound, ite_eq_right h]
      have hn2047 : 2047 ≤ n := Nat.le_of_not_gt h
      have hlog2047 :=
        (Analysis.rationalLogIntervalCheck_sound
            (show Analysis.rationalLogIntervalCheck 2047 11 12 7 8 = true by decide +kernel)).1
      norm_num only [Rat.cast_ofNat] at hlog2047
      have ht := Real.log_le_log (by norm_num only : (0 : ℝ) < 2047) (Nat.cast_le.mpr hn2047)
      have h7 : (7 : ℝ) ≤ Real.log n := hlog2047.trans ht
      have hs7 := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 7) h7 2
      nlinarith only [hs7]
  have hn3000 : 3000 ≤ n := Nat.le_of_not_gt hN
  have hlog3000 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 3000 12 12 8 (801 / 100) = true by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hlog3000
  have ht := Real.log_le_log (by norm_num only : (0 : ℝ) < 3000) (Nat.cast_le.mpr hn3000)
  have h8 : (8 : ℝ) ≤ Real.log n := hlog3000.trans ht
  by_cases h23 : Real.log n ≤ (80901 / 10000 : ℝ)
  · have hcap : Real.log n ≤ (Analysis.FinitePrimeProfile.p23.tunedCap : ℝ) := by
      norm_num only [Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
      exact h23
    obtain ⟨r, hr, hb, hf⟩ := exists_prime_finiteTuned .p23 hn ho hc hGRH hcap
    have hs := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 8) h8 2
    refine ⟨r, hr, ?_, hf⟩
    norm_num only [Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] at hb
    nlinarith only [hb, hs]
  · have hcap : Real.log n ≤ (Analysis.FinitePrimeProfile.p29.tunedCap : ℝ) := by
      norm_num only [Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
      linarith only [hlarge]
    obtain ⟨r, hr, hb, hf⟩ := exists_prime_finiteTuned .p29 hn ho hc hGRH hcap
    have hL := (lt_of_not_ge h23).le
    have hs := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 80901 / 10000) hL 2
    refine ⟨r, hr, ?_, hf⟩
    norm_num only [Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] at hb
    nlinarith only [hb, hs]

/-- The least prime MR witness obeys the same global four-ninths bound.
Extract the least rejecting prime from the preceding actual witness. -/
theorem exists_least_witness_four_ninths {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact
    exists_least_prime_reject_of_exists_prime_reject
      (exists_prime_witness_four_ninths hn ho hc hGRH)

end PseudoPrime.PrimeTestBounds.MillerRabin
