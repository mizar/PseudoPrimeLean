/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import PseudoPrime.PrimeTest.Selfridge.FirstStop

/-!
# Coincidence of Selfridge stopping rules for PrimeTest

This file independently relates the pure `-1` stopping rule to the
factor-detecting `≠ 1` rule for a common candidate predicate.
-/

namespace PseudoPrime.PrimeTest

/-- A pure `-1` stopping candidate also detects neither a factor nor Jacobi `1`. -/
theorem FirstStopNegOneSet.subset_firstStopNeOneSet {C : ℕ → Prop} {n : ℕ} (hn : 1 < n) :
    FirstStopNegOneSet C n ⊆ FirstStopNeOneSet C n := by
  intro i hi
  refine ⟨hi.1, ?_, ?_⟩
  · intro hndvd
    have hnatdvd : n ∣ (selfridgeD i).natAbs := by
      rw [selfridgeD_natAbs]
      exact hndvd
    have hgcdvd : n ∣ (selfridgeD i).gcd n := by
      rw [Int.gcd_eq_natAbs]
      exact Nat.dvd_gcd hnatdvd (dvd_refl n)
    have hgcdne : (selfridgeD i).gcd n ≠ 1 := by
      intro hgcd
      rw [hgcd] at hgcdvd
      have hnle : n ≤ 1 := Nat.le_of_dvd Nat.one_pos hgcdvd
      omega
    let _ : NeZero n := ⟨by omega⟩
    have hzero : jacobiSym (selfridgeD i) n = 0 := jacobiSym.eq_zero_iff_not_coprime.mpr hgcdne
    rw [hi.2] at hzero
    omega
  · intro hone
    rw [hi.2] at hone
    omega

/-- A nonempty pure `-1` stopping set yields a nonempty factor-detecting set. -/
theorem firstStopNeOneSet_nonempty_of_negOne {C : ℕ → Prop} {n : ℕ} (hn : 1 < n)
    (hneg : (FirstStopNegOneSet C n).Nonempty) : (FirstStopNeOneSet C n).Nonempty :=
  hneg.mono (FirstStopNegOneSet.subset_firstStopNeOneSet hn)

/-- For common candidates, the factor-detecting first-stop is no later. -/
theorem firstStopNeOne_le_firstStopNegOne_same_candidates {C : ℕ → Prop} {n : ℕ} (hn : 1 < n)
    (hneg : (FirstStopNegOneSet C n).Nonempty) :
    firstStopNeOne C n (firstStopNeOneSet_nonempty_of_negOne hn hneg) ≤
      firstStopNegOne C n hneg := by
  apply firstStopNeOne_le C n (firstStopNeOneSet_nonempty_of_negOne hn hneg)
  exact FirstStopNegOneSet.subset_firstStopNeOneSet hn (firstStopNegOne_mem C n hneg)

/-- For a prime modulus below the first pure stop, the two first-stops coincide. -/
theorem firstStopNeOne_eq_firstStopNegOne_of_prime {C : ℕ → Prop} {n : ℕ} (hnprime : Nat.Prime n)
    (hneg : (FirstStopNegOneSet C n).Nonempty) (hne : (FirstStopNeOneSet C n).Nonempty) :
    firstStopNeOne C n hne = firstStopNegOne C n hneg := by
  have hn1 : 1 < n := hnprime.one_lt
  apply Nat.le_antisymm
  · exact
      firstStopNeOne_le C n hne
        (FirstStopNegOneSet.subset_firstStopNeOneSet hn1 (firstStopNegOne_mem C n hneg))
  · apply firstStopNegOne_le C n hneg
    have hstop := firstStopNeOne_mem C n hne
    have hcopNat : (selfridgeD (firstStopNeOne C n hne)).natAbs.Coprime n := by
      rw [selfridgeD_natAbs]
      exact (hnprime.coprime_iff_not_dvd.mpr hstop.2.1).symm
    have hcop : (selfridgeD (firstStopNeOne C n hne)).gcd n = 1 := by
      rw [Int.gcd_eq_natAbs]
      exact hcopNat.gcd_eq_one
    refine ⟨hstop.1, ?_⟩
    rcases jacobiSym.eq_one_or_neg_one hcop with hone | hnegone
    · exact False.elim (hstop.2.2 hone)
    · exact hnegone

/-- A pure `-1` first-stop cannot equal a prime input. -/
theorem firstStopNegOne_ne_input_of_prime {C : ℕ → Prop} {n : ℕ} (hnprime : Nat.Prime n)
    (hneg : (FirstStopNegOneSet C n).Nonempty) : firstStopNegOne C n hneg ≠ n := by
  intro heq
  have hstop := firstStopNegOne_mem C n hneg
  have hnatdvd : n ∣ (selfridgeD (firstStopNegOne C n hneg)).natAbs := by
    rw [selfridgeD_natAbs, heq]
  have hgcdvd : n ∣ (selfridgeD (firstStopNegOne C n hneg)).gcd n := by
    rw [Int.gcd_eq_natAbs]
    exact Nat.dvd_gcd hnatdvd (dvd_refl n)
  have hgcdne : (selfridgeD (firstStopNegOne C n hneg)).gcd n ≠ 1 := by
    intro hgcd
    rw [hgcd] at hgcdvd
    have hnle : n ≤ 1 := Nat.le_of_dvd Nat.one_pos hgcdvd
    exact (not_le_of_gt hnprime.two_le) hnle
  let _ : NeZero n := ⟨hnprime.ne_zero⟩
  have hzero : jacobiSym (selfridgeD (firstStopNegOne C n hneg)) n = 0 :=
    jacobiSym.eq_zero_iff_not_coprime.mpr hgcdne
  rw [hstop.2] at hzero
  omega

/-- Mutual inclusion of stopping sets implies equality of their pure `-1` first-stops. -/
theorem firstStopNegOne_eq_of_mutual_subset {C₁ C₂ : ℕ → Prop} {n : ℕ}
    (h₁ : (FirstStopNegOneSet C₁ n).Nonempty) (h₂ : (FirstStopNegOneSet C₂ n).Nonempty)
    (h12 : FirstStopNegOneSet C₁ n ⊆ FirstStopNegOneSet C₂ n)
    (h21 : FirstStopNegOneSet C₂ n ⊆ FirstStopNegOneSet C₁ n) :
    firstStopNegOne C₁ n h₁ = firstStopNegOne C₂ n h₂ := by
  apply Nat.le_antisymm
  · exact firstStopNegOne_le C₁ n h₁ (h21 (firstStopNegOne_mem C₂ n h₂))
  · exact firstStopNegOne_le C₂ n h₂ (h12 (firstStopNegOne_mem C₁ n h₁))

/-- Mutual inclusion of stopping sets implies equality of their factor-detecting first-stops. -/
theorem firstStopNeOne_eq_of_mutual_subset {C₁ C₂ : ℕ → Prop} {n : ℕ}
    (h₁ : (FirstStopNeOneSet C₁ n).Nonempty) (h₂ : (FirstStopNeOneSet C₂ n).Nonempty)
    (h12 : FirstStopNeOneSet C₁ n ⊆ FirstStopNeOneSet C₂ n)
    (h21 : FirstStopNeOneSet C₂ n ⊆ FirstStopNeOneSet C₁ n) :
    firstStopNeOne C₁ n h₁ = firstStopNeOne C₂ n h₂ := by
  apply Nat.le_antisymm
  · exact firstStopNeOne_le C₁ n h₁ (h21 (firstStopNeOne_mem C₂ n h₂))
  · exact firstStopNeOne_le C₂ n h₂ (h12 (firstStopNeOne_mem C₁ n h₁))

end PseudoPrime.PrimeTest
