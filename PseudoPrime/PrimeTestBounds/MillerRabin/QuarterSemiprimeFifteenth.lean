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

/-! # Seventeen-prime semiprime interval -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The fifteen-prime supply extended by 53 and 59. -/
private def primes17 : List ℕ :=
  53 :: 59 :: target028FifteenPrimes

/-- Integer logarithm weights in twentieths for the extended supply. -/
private def weight17 (p : ℕ) : ℕ :=
  if p = 53 then 80 else if p = 59 then 82 else target028Fine47Weight p

/-- The weight list of the extended prime supply. -/
private def weights17 : List ℕ :=
  80 :: 82 :: target028Fine47Weights

/-- The extended prime labels are distinct and have positive weights. -/
private theorem labels17 :
    primes17.Nodup ∧ primes17.map weight17 = weights17 ∧ ∀ p ∈ primes17, 0 < weight17 p := by
  decide +kernel

/-- Each extended label is prime, at most 60, and has a certified log weight. -/
private theorem supply17 (p : ℕ) (hp : p ∈ primes17) :
    p.Prime ∧ p ≤ 60 ∧ Real.log p ≤ (weight17 p : ℝ) / 20 := by
  simp only [primes17, List.mem_cons] at hp
  rcases hp with rfl | rfl | hp
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 53 5 32 0 4 = true from by decide +kernel)).2
    norm_num only [Rat.cast_zero, Rat.cast_ofNat] at h
    refine ⟨by decide +kernel, by decide, ?_⟩
    change Real.log 53 ≤ 80 / 20
    norm_num only
    exact h
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 59 5 64 0 (41 / 10) = true from by
            decide +kernel)).2
    norm_num only [Rat.cast_zero, Rat.cast_ofNat, Rat.cast_div] at h
    refine ⟨by decide +kernel, by decide, ?_⟩
    change Real.log 59 ≤ 82 / 20
    linarith only [h]
  · have hb := target028_fine47_supply p hp
    have h53 : p ≠ 53 := fun h ↦ (by decide : ¬53 ≤ 47) (h ▸ hb.2.1)
    have h59 : p ≠ 59 := fun h ↦ (by decide : ¬59 ≤ 47) (h ▸ hb.2.1)
    refine ⟨hb.1, Nat.le_trans hb.2.1 (by decide), ?_⟩
    simpa only [weight17, h53, h59, ↓reduceIte] using hb.2.2

/-- The weighted recurrence counts 845 products through budget 150. -/
private theorem count17 : weightedPrimeCount id weights17 150 = 845 := by
  change weightedPrimeCount id (80 :: 82 :: target028Fine47Weights) 150 = 845
  have h150 : weightedPrimeCount id target028Fine47Weights 150 = 783 := by
    rw [weightedPrimeCount_weights_eq_card target028Fine47Weight 150 target028FifteenPrimes
        target028Fine47Weights target028_fine47_labels.1 target028_fine47_labels.2.2
        target028_fine47_labels.2.1,
      target028_fine47_card 150 (by decide)]
    decide +kernel
  have h70 : weightedPrimeCount id target028Fine47Weights 70 = 33 := by
    rw [weightedPrimeCount_weights_eq_card target028Fine47Weight 70 target028FifteenPrimes
        target028Fine47Weights target028_fine47_labels.1 target028_fine47_labels.2.2
        target028_fine47_labels.2.1,
      target028_fine47_card 70 (by decide)]
    decide +kernel
  have h68 : weightedPrimeCount id target028Fine47Weights 68 = 29 := by
    rw [weightedPrimeCount_weights_eq_card target028Fine47Weight 68 target028FifteenPrimes
        target028Fine47Weights target028_fine47_labels.1 target028_fine47_labels.2.2
        target028_fine47_labels.2.1,
      target028_fine47_card 68 (by decide)]
    decide +kernel
  conv_lhs => rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, dite_true, Nat.reduceSub]
  conv_lhs =>
    lhs; rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, dite_true, Nat.reduceSub]
  conv_lhs =>
    rhs; rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, dite_false]
  conv_lhs =>
    rhs; rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, dite_false]
  have h68tail : weightedPrimeCount id (82 :: target028Fine47Weights) 68 = 29 := by
    rw [weightedPrimeCount.eq_def]
    norm_num only [id_eq, dite_true, dite_false]
    exact h68
  simp only [dite_true, h150, h68tail, h70, Nat.reduceAdd]

/-- The extended weighted family has 845 elements. -/
private theorem card17 : (weightedPrimeFamily primes17.toFinset weight17 150).card = 845 := by
  have h :=
    weightedPrimeCount_weights_eq_card weight17 150 primes17 weights17 labels17.1 labels17.2.2
      labels17.2.1
  rw [count17] at h
  exact h.symm

/-- An odd product of two ordered distinct primes with logarithm between
15.57 and 15.63 has a rejecting prime below one quarter of its squared
logarithm. The existing weighted count is extended by the primes 53 and 59. -/
theorem quarter_semiprime_fifteenth {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q) (hL : (1557 / 100 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 1563 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := primes17.toFinset
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦ (supply17 r (List.mem_toFinset.mp hr)).1
  have hbound : ∀ r ∈ S, r ≤ 60 := fun r hr ↦ (supply17 r (List.mem_toFinset.mp hr)).2.1
  have hw : ∀ r ∈ S, Real.log r ≤ (weight17 r : ℝ) / 20 := fun r hr ↦
    (supply17 r (List.mem_toFinset.mp hr)).2.2
  have hwpos : ∀ r ∈ S, 1 ≤ weight17 r := fun r hr ↦ labels17.2.2 r (List.mem_toFinset.mp hr)
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1690 11 64 (743 / 100) 8 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hD :
    (743 / 100 : ℝ) ≤ Real.log ((2 * (weightedPrimeFamily S weight17 150).card : ℕ) : ℝ) := by
    change
      (743 / 100 : ℝ) ≤
        Real.log ((2 * (weightedPrimeFamily primes17.toFinset weight17 150).card : ℕ) : ℝ)
    rw [card17]
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    exact hlog
  have hA : Real.log 2 + (150 : ℝ) / 20 ≤ 41 / 5 := by linarith only [Real.log_two_lt_d9]
  have hB : (60 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  apply
    exists_prime_reject_weighted_cell hn ho hp hq hprod S weight17 150 60 20 (by norm_num only)
      hwpos hprime hbound hw hA hD hB
  intro hqsmall
  have hmax : max (41 / 5 : ℝ) (Real.log n - 743 / 100) ≤ 41 / 5 := by
    apply max_le le_rfl
    linarith only [hU]
  have hqlog : Real.log q ≤ (41 / 5 : ℝ) := hqsmall.trans hmax
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 3721 11 64 (821 / 100) 9 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hqR : (q : ℝ) < 3721 :=
    (Real.log_lt_log_iff (Nat.cast_pos.mpr hq.pos) (by norm_num only : (0 : ℝ) < 3721)).mp
      (by linarith only [hqlog, hcert])
  have hsize : q < (60 + 1) ^ 2 := by
    norm_num only
    exact_mod_cast hqR
  obtain ⟨r, hr, hrB, hf⟩ :=
    semiprime_small_factor_witness hn ho hp hq hpq hprod (by decide : 0 < 60) hsize
  exact ⟨r, hr, (Nat.cast_le.mpr hrB).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
