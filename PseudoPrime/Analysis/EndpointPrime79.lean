/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.EndpointFiniteSums
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveComparison
public import PseudoPrime.Analysis.PointwiseReciprocalLowerBound

/-! # Fixed-79 principal bounds from the unchanged thirty prime-power atoms -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The rational radius for the fixed rejecting-prime cutoff 79. -/
def prime79Radius : ℚ :=
  5694 / 625

/-- The certified lower radius-log endpoint. -/
def prime79LogLo : ℚ :=
  2209416 / 1000000

/-- The certified upper radius-log endpoint. -/
def prime79LogHi : ℚ :=
  2209417 / 1000000

/-- The reciprocal credit retained by the thirty existing prime-power atoms. -/
def prime79CreditR : ℚ :=
  3135 / 1000000

/-- The smoothed credit retained by the thirty existing prime-power atoms. -/
def prime79CreditS : ℚ :=
  667896 / 1000000

/-- The logarithmic entrance cap for the fixed prime cutoff 79. -/
def prime79Cap : ℚ :=
  126409 / 10000

/-- One Taylor-eight certificate encloses the new radius logarithm. -/
theorem prime79_log_bounds :
    (prime79LogLo : ℝ) ≤ Real.log (prime79Radius : ℝ) ∧
      Real.log (prime79Radius : ℝ) ≤ (prime79LogHi : ℝ) := by
  exact
    rationalLogIntervalCheck_sound
      (by decide +kernel :
        rationalLogIntervalCheck prime79Radius 3 8 prime79LogLo prime79LogHi = true)

/-- The new radius exceeds two and its square precedes the next prime 83. -/
theorem prime79_radius_bounds : (2 : ℝ) ≤ prime79Radius ∧ (prime79Radius : ℝ) ^ 2 < 83 := by
  norm_num only [prime79Radius, Rat.cast_div, Rat.cast_ofNat, and_self]

/-- The unchanged thirty atoms remain valid at the enlarged radius and logarithm. -/
theorem prime79_atom_data :
    ∀ m ∈ FinitePrimeProfile.p73.atoms,
      0 < m ∧
        m.minFac ∈ finitePrincipalPrimes ∧
        m.minFac.Prime ∧
        principalAtomExp m ≠ 0 ∧
        m = m.minFac ^ principalAtomExp m ∧
        (m : ℚ) ≤ prime79Radius ^ 2 ∧
        0 ≤ principalLogLo m.minFac ∧
        0 ≤ 2 * prime79LogLo - principalAtomExp m * principalLogHi m.minFac := by
  decide +kernel

/-- The reciprocal lower sum uses exactly the existing thirty prime powers. -/
def prime79ReciprocalLower : ℚ :=
  ∑ m ∈ FinitePrimeProfile.p73.atoms, principalLogLo m.minFac / m * (1 - m / prime79Radius ^ 2)

/-- The smoothed lower sum uses exactly the existing thirty prime powers. -/
def prime79SmoothedLower : ℚ :=
  ∑ m ∈ FinitePrimeProfile.p73.atoms,
    principalLogLo m.minFac * (2 * prime79LogLo - principalAtomExp m * principalLogHi m.minFac)

/-- The pointwise reciprocal loss at the new rational radius. -/
def prime79ReciprocalLoss : ℚ :=
  78861 / 50000 + (231 / 5000) / prime79Radius - (16033 / 9000) / prime79Radius ^ 2

/-- The reciprocal finite certificate covers the fixed-79 target. -/
theorem prime79_rec_check :
    2 * prime79LogHi - prime79ReciprocalLoss + prime79CreditR ≤ prime79ReciprocalLower := by
  decide +kernel

/-- The smoothed finite certificate covers the fixed-79 target. -/
theorem prime79_log_check :
    prime79Radius ^ 2 - prime79Radius / 20 - (1839 / 500 : ℚ) * prime79LogLo - 21 / 20 +
        prime79CreditS ≤
      prime79SmoothedLower := by
  decide +kernel

/-- Embed every distinct selected positive prime power in the original finite sum. -/
theorem prime79_atoms_subset :
    FinitePrimeProfile.p73.atoms ⊆ Finset.Ioc 0 ⌊(prime79Radius : ℝ) ^ 2⌋₊ := by
  intro m hm
  rcases prime79_atom_data m hm with ⟨hm0, _, _, _, _, hmx, _, _⟩
  exact Finset.mem_Ioc.mpr ⟨hm0, Nat.le_floor (by exact_mod_cast hmx)⟩

/-- The rational reciprocal payload is below the actual principal reciprocal sum. -/
theorem prime79_rec_sum :
    (prime79ReciprocalLower : ℝ) ≤
      AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum ((prime79Radius : ℝ) ^ 2) := by
  have hy : (0 : ℝ) < prime79Radius := lt_of_lt_of_le (by norm_num only) prime79_radius_bounds.1
  have hp :
    (prime79ReciprocalLower : ℝ) ≤
      ∑ m ∈ FinitePrimeProfile.p73.atoms,
        AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm ((prime79Radius : ℝ) ^ 2)
          m := by
    simp only [prime79ReciprocalLower, Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_sub, Rat.cast_one, Rat.cast_pow]
    apply Finset.sum_le_sum
    intro m hm
    rcases prime79_atom_data m hm with ⟨hm0, hpm, hprime, hk, heq, hmx, _, _⟩
    have hmxR : (m : ℝ) ≤ (prime79Radius : ℝ) ^ 2 := by exact_mod_cast hmx
    have ht :=
      finitePrincipal_rec_atom hprime hk (sq_pos_of_pos hy)
        (by simpa only [← Nat.cast_pow, ← heq] using hmxR) (principalLog_bounds hpm).1
    simpa only [← Nat.cast_pow, ← heq] using ht
  apply hp.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg (prime79_atoms_subset)
  intro m hm _
  exact
    AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm_nonneg (sq_pos_of_pos hy)
      (Finset.mem_Ioc.mp hm).1 (Finset.mem_Ioc.mp hm).2

/-- The rational smoothed payload is below the actual principal smoothed sum. -/
theorem prime79_log_sum :
    (prime79SmoothedLower : ℝ) ≤
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum ((prime79Radius : ℝ) ^ 2) := by
  have hy : (0 : ℝ) < prime79Radius := lt_of_lt_of_le (by norm_num only) prime79_radius_bounds.1
  have hp :
    (prime79SmoothedLower : ℝ) ≤
      ∑ m ∈ FinitePrimeProfile.p73.atoms,
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm ((prime79Radius : ℝ) ^ 2) m := by
    simp only [prime79SmoothedLower, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, Rat.cast_sub,
      Rat.cast_ofNat]
    apply Finset.sum_le_sum
    intro m hm
    rcases prime79_atom_data m hm with ⟨_, hpm, hprime, hk, heq, _, _, hw⟩
    have hwR : (0 : ℝ) ≤ 2 * prime79LogLo - principalAtomExp m * principalLogHi m.minFac := by
      exact_mod_cast hw
    have ht :=
      finitePrincipal_log_atom hprime hk hy (principalLog_bounds hpm).1 (principalLog_bounds hpm).2
        prime79_log_bounds.1 hwR
    simpa only [← heq] using ht
  apply hp.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg (prime79_atoms_subset)
  intro m hm _
  exact
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm_nonneg (sq_pos_of_pos hy)
      (Finset.mem_Ioc.mp hm).1 (Finset.mem_Ioc.mp hm).2

/-- The actual reciprocal principal sum satisfies the strengthened pointwise lower bound. -/
theorem prime79_reciprocal :
    2 * Real.log (prime79Radius : ℝ) - pointwiseReciprocalLoss prime79Radius + prime79CreditR ≤
      AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum ((prime79Radius : ℝ) ^ 2) := by
  have hc := (Rat.cast_le (K := ℝ)).mpr (prime79_rec_check)
  simp only [prime79ReciprocalLoss, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
    Rat.cast_ofNat, Rat.cast_pow] at hc
  dsimp only [pointwiseReciprocalLoss]
  linarith only [hc, prime79_rec_sum, prime79_log_bounds.2]

/-- The actual smoothed principal sum satisfies the strengthened pointwise lower bound. -/
theorem prime79_smoothed :
    (prime79Radius : ℝ) ^ 2 - prime79Radius / 20 - (1839 / 500 : ℝ) * Real.log prime79Radius -
          21 / 20 +
        prime79CreditS ≤
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum ((prime79Radius : ℝ) ^ 2) := by
  have hc := (Rat.cast_le (K := ℝ)).mpr (prime79_log_check)
  simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_pow] at hc
  linarith only [hc, prime79_log_sum, prime79_log_bounds.1]

end PseudoPrime.Analysis
