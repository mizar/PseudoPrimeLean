/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeSmallFactor
import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine47Count
import PseudoPrime.PrimeTestBounds.MillerRabin.SignedWeightedCell

/-! # An independent semiprime interval -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A checked fifteen-prime count reduces a semiprime witness to a local
logarithmic case. The weighted-family count gives the signed-product bound. -/
private theorem quarter_fine47_cell {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hprod : n = p * q) (H B : ℕ) (hH : H ≤ 180) (h47 : 47 ≤ B) {A D X : ℝ}
    (hA : Real.log 2 + (H : ℝ) / 20 ≤ A)
    (hD : D ≤ Real.log ((2 * target028Fine47Row.getD H 0 : ℕ) : ℝ)) (hB : (B : ℝ) ≤ X)
    (hlocal :
      Real.log q ≤ max A (Real.log n - D) →
        ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n)) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := target028FifteenPrimes.toFinset
  let w := target028Fine47Weight
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
    (target028_fine47_supply r (List.mem_toFinset.mp hr)).1
  have hbound : ∀ r ∈ S, r ≤ B := fun r hr ↦
    ((target028_fine47_supply r (List.mem_toFinset.mp hr)).2.1).trans h47
  have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 20 := fun r hr ↦
    (target028_fine47_supply r (List.mem_toFinset.mp hr)).2.2
  have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦
    target028_fine47_labels.2.2 r (List.mem_toFinset.mp hr)
  have hDF : D ≤ Real.log ((2 * (weightedPrimeFamily S w H).card : ℕ) : ℝ) := by
    rw [target028_fine47_card H hH]
    exact hD
  exact
    exists_prime_reject_weighted_cell hn ho hp hq hprod S w H B 20 (by norm_num only) hwpos hprime
      hbound hw hA hDF hB hlocal

/-- An odd product of distinct ordered primes with logarithm between 1529 / 100
and 1537 / 100 has an unconditional quarter-square rejecting prime. For small
local moduli, primes through 57 generate the local group; for larger moduli,
706 checked weighted products and their negatives exceed the local kernel. -/
theorem quarter_semiprime_eleventh {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q) (hL : (1529 / 100 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 1537 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1412 11 32 (725 / 100) 8 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hD : (725 / 100 : ℝ) ≤ Real.log ((2 * target028Fine47Row.getD 147 0 : ℕ) : ℝ) := by
    rw [show target028Fine47Row.getD 147 0 = 706 by decide +kernel]
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    exact hlog
  have hA : Real.log 2 + (147 : ℝ) / 20 ≤ 812 / 100 := by linarith only [Real.log_two_lt_d9]
  have hB : (57 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  apply quarter_fine47_cell hn ho hp hq hprod 147 57 (by decide) (by decide) hA hD hB
  intro hqsmall
  have hmax : max (812 / 100 : ℝ) (Real.log n - 725 / 100) ≤ 812 / 100 := by
    apply max_le le_rfl
    linarith only [hU]
  have hqlog : Real.log q ≤ (812 / 100 : ℝ) := hqsmall.trans hmax
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 3364 11 32 (81205 / 10000) 9 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hqR : (q : ℝ) < 3364 :=
    (Real.log_lt_log_iff (Nat.cast_pos.mpr hq.pos) (by norm_num only : (0 : ℝ) < 3364)).mp
      (by linarith only [hqlog, hcert])
  have hsize : q < (57 + 1) ^ 2 := by
    norm_num only
    exact_mod_cast hqR
  obtain ⟨r, hr, hrB, hf⟩ :=
    semiprime_small_factor_witness hn ho hp hq hpq hprod (by decide : 0 < 57) hsize
  exact ⟨r, hr, (Nat.cast_le.mpr hrB).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
