/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed89Count197
import PseudoPrime.PrimeTestBounds.MillerRabin.SignedWeightedCell
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprimeLocal

/-! # Semiprime witnesses on logarithmic scales 20 to 24.7 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The existing weighted prime supply through 89 has 35109 products at budget 129. -/
private theorem card89 :
    (weightedPrimeFamily primeSeed89Primes.toFinset primeSeed89Weight 129).card = 35109 := by
  have h :=
    (weightedPrimeCount_weights_eq_card primeSeed89Weight 129 primeSeed89Primes primeSeed89Weights
          primeSeed89_labels.1 primeSeed89_labels.2.2 primeSeed89_labels.2.1).symm.trans
      ((weightedPrimeTableCheck_sound 197 primeSeed89Weights primeSeed89Row197 primeSeed89Tail197
          primeSeed89_checked197 129 (by decide)).symm)
  rw [show primeSeed89Row197.getD 129 0 = 35109 by decide +kernel] at h
  exact h

/-- Under GRH, an odd product of ordered distinct primes with logarithm
between 20 and 24.7 has a rejecting prime below one quarter of its squared
logarithm. A weighted-product count and the radius-ten local anchor cover both cases. -/
theorem quarter_semiprime_20_247 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (20 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 247 / 10) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := primeSeed89Primes.toFinset
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
    (primeSeed89_prime_supply r (List.mem_toFinset.mp hr)).1
  have hbound : ∀ r ∈ S, r ≤ 97 := fun r hr ↦
    ((primeSeed89_prime_supply r (List.mem_toFinset.mp hr)).2).trans (by decide)
  have hw : ∀ r ∈ S, Real.log r ≤ (primeSeed89Weight r : ℝ) / 10 := fun r hr ↦
    primeSeed89_weight_bounds r (List.mem_toFinset.mp hr)
  have hwpos : ∀ r ∈ S, 1 ≤ primeSeed89Weight r := fun r hr ↦
    primeSeed89_labels.2.2 r (List.mem_toFinset.mp hr)
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 70218 17 32 (111 / 10) 12 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hD :
    (111 / 10 : ℝ) ≤
      Real.log ((2 * (weightedPrimeFamily S primeSeed89Weight 129).card : ℕ) : ℝ) := by
    change
      (111 / 10 : ℝ) ≤
        Real.log
          ((2 * (weightedPrimeFamily primeSeed89Primes.toFinset primeSeed89Weight 129).card : ℕ) :
            ℝ)
    rw [card89]
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    exact hlog
  have hA : Real.log 2 + (129 : ℝ) / 10 ≤ 68 / 5 := by linarith only [Real.log_two_lt_d9]
  have hB : (97 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  apply
    exists_prime_reject_weighted_cell hn ho hp hq hprod S primeSeed89Weight 129 97 10
      (by norm_num only) hwpos hprime hbound hw hA hD hB
  intro hqsmall
  have hmax : max (68 / 5 : ℝ) (Real.log n - 111 / 10) ≤ 68 / 5 := by
    apply max_le le_rfl
    linarith only [hU]
  obtain ⟨r, hr, hrB, hf⟩ :=
    semiprime_local_anchor97 hn ho hp hq hpq hprod hGRH (hqsmall.trans hmax)
  exact ⟨r, hr, (Nat.cast_le.mpr hrB).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
