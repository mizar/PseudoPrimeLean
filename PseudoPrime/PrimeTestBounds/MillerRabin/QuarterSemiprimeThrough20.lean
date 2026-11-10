/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed61
import PseudoPrime.PrimeTestBounds.MillerRabin.SignedWeightedCell
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprimeLocal

/-! # Semiprime witnesses through logarithmic scale 20 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The existing weighted prime supply through 61 has 3376 products at budget 96. -/
private theorem card61 :
    (weightedPrimeFamily primeSeed61Primes.toFinset primeSeed61Weight 96).card = 3376 := by
  have h :=
    (weightedPrimeCount_weights_eq_card primeSeed61Weight 96 primeSeed61Primes primeSeed61Weights
          primeSeed61_labels.1 primeSeed61_labels.2.2 primeSeed61_labels.2.1).symm.trans
      ((weightedPrimeTableCheck_sound 96 primeSeed61Weights primeSeed61Row primeSeed61Tail
          primeSeed61_checked 96 (by decide)).symm)
  exact h

/-- Under GRH, an odd product of ordered distinct primes with logarithm
between 15.63 and 20 has a rejecting prime below one quarter of its squared
logarithm. A weighted-product count and a local anchor cover the two cases. -/
theorem quarter_semiprime_through20 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1563 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 20) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := primeSeed61Primes.toFinset
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
    (primeSeed61_prime_supply r (List.mem_toFinset.mp hr)).1
  have hbound : ∀ r ∈ S, r ≤ 61 := fun r hr ↦
    (primeSeed61_prime_supply r (List.mem_toFinset.mp hr)).2
  have hw : ∀ r ∈ S, Real.log r ≤ (primeSeed61Weight r : ℝ) / 10 := fun r hr ↦
    primeSeed61_weight_bounds r (List.mem_toFinset.mp hr)
  have hwpos : ∀ r ∈ S, 1 ≤ primeSeed61Weight r := fun r hr ↦
    primeSeed61_labels.2.2 r (List.mem_toFinset.mp hr)
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 6752 12 32 (881 / 100) 9 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hD :
    (881 / 100 : ℝ) ≤
      Real.log ((2 * (weightedPrimeFamily S primeSeed61Weight 96).card : ℕ) : ℝ) := by
    change
      (881 / 100 : ℝ) ≤
        Real.log
          ((2 * (weightedPrimeFamily primeSeed61Primes.toFinset primeSeed61Weight 96).card : ℕ) : ℝ)
    rw [card61]
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    exact hlog
  have hA : Real.log 2 + (96 : ℝ) / 10 ≤ 11249 / 1000 := by linarith only [Real.log_two_lt_d9]
  have hB : (61 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  apply
    exists_prime_reject_weighted_cell hn ho hp hq hprod S primeSeed61Weight 96 61 10
      (by norm_num only) hwpos hprime hbound hw hA hD hB
  intro hqsmall
  have hmax : max (11249 / 1000 : ℝ) (Real.log n - 881 / 100) ≤ 11249 / 1000 := by
    apply max_le le_rfl
    linarith only [hU]
  obtain ⟨r, hr, hrB, hf⟩ :=
    semiprime_local_anchor61 hn ho hp hq hpq hprod hGRH (hqsmall.trans hmax)
  exact ⟨r, hr, (Nat.cast_le.mpr hrB).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
