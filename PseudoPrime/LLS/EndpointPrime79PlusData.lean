/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.EndpointPrime79
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveComparison
public import PseudoPrime.Analysis.PointwiseReciprocalLowerBound

/-! # Fixed-79 principal bounds from the thirty-two distinct prime-power atoms -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The old thirty prime powers together with 79 and 81 form the new payload.
The finite set removes repetitions; the checked cardinality below is exactly 32. -/
def prime79PlusAtoms : Finset ℕ :=
  insert 79 (insert 81 Analysis.FinitePrimeProfile.p73.atoms)

/-- Add the single new prime base 79 to the existing logarithm-certificate support. -/
def prime79PlusPrimes : Finset ℕ :=
  insert 79 Analysis.finitePrincipalPrimes

/-- The prime-log lower endpoint extends the old data only at the new prime 79. -/
def prime79PlusPrimeLogLo (p : ℕ) : ℚ :=
  if p = 79 then 4369444 / 1000000 else Analysis.principalLogLo p

/-- The prime-log upper endpoint extends the old data only at the new prime 79. -/
def prime79PlusPrimeLogHi (p : ℕ) : ℚ :=
  if p = 79 then 4369451 / 1000000 else Analysis.principalLogHi p

/-- The selected prime-power exponent corrects the old default specifically at 81 = 3^4.
The new atom 79 retains the existing prime exponent one. -/
def prime79PlusAtomExp (m : ℕ) : ℕ :=
  if m = 81 then 4 else Analysis.principalAtomExp m

/-- The new support contains 32 distinct atoms, and both added atoms were absent before.
These kernel checks also verify the explicitly required decomposition 81 = 3^4. -/
theorem prime79Plus_atom_count :
    prime79PlusAtoms.card = 32 ∧
      79 ∉ Analysis.FinitePrimeProfile.p73.atoms ∧
      81 ∉ Analysis.FinitePrimeProfile.p73.atoms ∧ (81 : ℕ) = 3 ^ 4 := by
  decide +kernel

/-- A single Taylor-eight certificate encloses log 79 at scale six. -/
theorem prime79Plus_log79 :
    (4369444 / 1000000 : ℝ) ≤ Real.log (79 : ℝ) ∧ Real.log (79 : ℝ) ≤ (4369451 / 1000000 : ℝ) := by
  have h :=
    Analysis.rationalLogIntervalCheck_sound
      (by decide +kernel :
        Analysis.rationalLogIntervalCheck (79 : ℚ) 6 8 (4369444 / 1000000) (4369451 / 1000000) =
          true)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

/-- Every prime base in the enlarged support has the stated real logarithm interval.
Use the new certificate at 79 and the unchanged existing certificates everywhere else. -/
theorem prime79Plus_prime_log_bounds {p : ℕ} (hp : p ∈ prime79PlusPrimes) :
    (prime79PlusPrimeLogLo p : ℝ) ≤ Real.log p ∧ Real.log p ≤ (prime79PlusPrimeLogHi p : ℝ) := by
  by_cases h79 : p = 79
  · subst p
    simpa only [prime79PlusPrimeLogLo, prime79PlusPrimeLogHi, ite_true, Rat.cast_div,
      Rat.cast_ofNat, Nat.cast_ofNat] using prime79Plus_log79
  · have hm : p ∈ Analysis.finitePrincipalPrimes := (Finset.mem_insert.mp hp).resolve_left h79
    simpa only [prime79PlusPrimeLogLo, prime79PlusPrimeLogHi, ite_eq_right h79] using
      Analysis.principalLog_bounds hm

/-- The rational radius for the fixed rejecting-prime cutoff 79. -/
def prime79PlusRadius : ℚ :=
  5694 / 625

/-- The certified lower radius-log endpoint. -/
def prime79PlusLogLo : ℚ :=
  2209416 / 1000000

/-- The certified upper radius-log endpoint. -/
def prime79PlusLogHi : ℚ :=
  2209417 / 1000000

/-- The reciprocal credit retained by the thirty-two selected prime-power atoms. -/
def prime79PlusCreditR : ℚ :=
  153 / 25000

/-- The smoothed credit retained by the thirty-two selected prime-power atoms. -/
def prime79PlusCreditS : ℚ :=
  91 / 100

/-- The logarithmic entrance cap for the fixed prime cutoff 79. -/
def prime79PlusCap : ℚ :=
  12659 / 1000

/-- Reuse the existing logarithm interval for the unchanged rational radius. -/
theorem prime79Plus_log_bounds :
    (prime79PlusLogLo : ℝ) ≤ Real.log (prime79PlusRadius : ℝ) ∧
      Real.log (prime79PlusRadius : ℝ) ≤ (prime79PlusLogHi : ℝ) := by
  exact Analysis.prime79_log_bounds

/-- The unchanged radius exceeds two and its square precedes the next prime 83. -/
theorem prime79Plus_radius_bounds :
    (2 : ℝ) ≤ prime79PlusRadius ∧ (prime79PlusRadius : ℝ) ^ 2 < 83 := by
  norm_num only [prime79PlusRadius, Rat.cast_div, Rat.cast_ofNat, and_self]

/-- The thirty-two atoms remain valid at the enlarged radius and logarithm. -/
theorem prime79Plus_atom_data :
    ∀ m ∈ prime79PlusAtoms,
      0 < m ∧
        m.minFac ∈ prime79PlusPrimes ∧
        m.minFac.Prime ∧
        prime79PlusAtomExp m ≠ 0 ∧
        m = m.minFac ^ prime79PlusAtomExp m ∧
        (m : ℚ) ≤ prime79PlusRadius ^ 2 ∧
        0 ≤ prime79PlusPrimeLogLo m.minFac ∧
        0 ≤ 2 * prime79PlusLogLo - prime79PlusAtomExp m * prime79PlusPrimeLogHi m.minFac := by
  decide +kernel

/-- The reciprocal lower sum uses exactly the thirty-two selected prime powers. -/
def prime79PlusReciprocalLower : ℚ :=
  ∑ m ∈ prime79PlusAtoms, prime79PlusPrimeLogLo m.minFac / m * (1 - m / prime79PlusRadius ^ 2)

/-- The smoothed lower sum uses exactly the thirty-two selected prime powers. -/
def prime79PlusSmoothedLower : ℚ :=
  ∑ m ∈ prime79PlusAtoms,
    prime79PlusPrimeLogLo m.minFac *
      (2 * prime79PlusLogLo - prime79PlusAtomExp m * prime79PlusPrimeLogHi m.minFac)

/-- The pointwise reciprocal loss at the new rational radius. -/
def prime79PlusReciprocalLoss : ℚ :=
  78861 / 50000 + (231 / 5000) / prime79PlusRadius - (16033 / 9000) / prime79PlusRadius ^ 2

/-- The reciprocal finite certificate covers the fixed-79 target. -/
theorem prime79Plus_rec_check :
    2 * prime79PlusLogHi - prime79PlusReciprocalLoss + prime79PlusCreditR ≤
      prime79PlusReciprocalLower := by
  decide +kernel

/-- The smoothed finite certificate covers the fixed-79 target. -/
theorem prime79Plus_log_check :
    prime79PlusRadius ^ 2 - prime79PlusRadius / 20 - (1839 / 500 : ℚ) * prime79PlusLogLo - 21 / 20 +
        prime79PlusCreditS ≤
      prime79PlusSmoothedLower := by
  decide +kernel

/-- Embed every distinct selected positive prime power in the original finite sum. -/
theorem prime79Plus_atoms_subset :
    prime79PlusAtoms ⊆ Finset.Ioc 0 ⌊(prime79PlusRadius : ℝ) ^ 2⌋₊ := by
  intro m hm
  rcases prime79Plus_atom_data m hm with ⟨hm0, _, _, _, _, hmx, _, _⟩
  have hmxR : (m : ℝ) ≤ (prime79PlusRadius : ℝ) ^ 2 := by
    simpa only [Rat.cast_natCast, Rat.cast_pow] using (Rat.cast_le (K := ℝ)).mpr hmx
  exact Finset.mem_Ioc.mpr ⟨hm0, Nat.le_floor hmxR⟩

/-- The rational reciprocal payload is below the actual principal reciprocal sum. -/
theorem prime79Plus_rec_sum :
    (prime79PlusReciprocalLower : ℝ) ≤
      AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum
        ((prime79PlusRadius : ℝ) ^ 2) := by
  have hy : (0 : ℝ) < prime79PlusRadius :=
    lt_of_lt_of_le (by norm_num only) prime79Plus_radius_bounds.1
  have hp :
    (prime79PlusReciprocalLower : ℝ) ≤
      ∑ m ∈ prime79PlusAtoms,
        AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm ((prime79PlusRadius : ℝ) ^ 2)
          m := by
    simp only [prime79PlusReciprocalLower, Rat.cast_sum, Rat.cast_mul, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_sub, Rat.cast_one, Rat.cast_pow]
    apply Finset.sum_le_sum
    intro m hm
    rcases prime79Plus_atom_data m hm with ⟨hm0, hpm, hprime, hk, heq, hmx, _, _⟩
    have hmxR : (m : ℝ) ≤ (prime79PlusRadius : ℝ) ^ 2 := by
      simpa only [Rat.cast_natCast, Rat.cast_pow] using (Rat.cast_le (K := ℝ)).mpr hmx
    have ht :=
      Analysis.finitePrincipal_rec_atom hprime hk (sq_pos_of_pos hy)
        (by simpa only [← Nat.cast_pow, ← heq] using hmxR) (prime79Plus_prime_log_bounds hpm).1
    simpa only [← Nat.cast_pow, ← heq] using ht
  apply hp.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg (prime79Plus_atoms_subset)
  intro m hm _
  exact
    AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm_nonneg (sq_pos_of_pos hy)
      (Finset.mem_Ioc.mp hm).1 (Finset.mem_Ioc.mp hm).2

/-- The rational smoothed payload is below the actual principal smoothed sum. -/
theorem prime79Plus_log_sum :
    (prime79PlusSmoothedLower : ℝ) ≤
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum ((prime79PlusRadius : ℝ) ^ 2) := by
  have hy : (0 : ℝ) < prime79PlusRadius :=
    lt_of_lt_of_le (by norm_num only) prime79Plus_radius_bounds.1
  have hp :
    (prime79PlusSmoothedLower : ℝ) ≤
      ∑ m ∈ prime79PlusAtoms,
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm ((prime79PlusRadius : ℝ) ^ 2)
          m := by
    simp only [prime79PlusSmoothedLower, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, Rat.cast_sub,
      Rat.cast_ofNat]
    apply Finset.sum_le_sum
    intro m hm
    rcases prime79Plus_atom_data m hm with ⟨_, hpm, hprime, hk, heq, _, _, hw⟩
    have hwR :
      (0 : ℝ) ≤ 2 * prime79PlusLogLo - prime79PlusAtomExp m * prime79PlusPrimeLogHi m.minFac := by
      simpa only [Rat.cast_zero, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using
        (Rat.cast_le (K := ℝ)).mpr hw
    have ht :=
      Analysis.finitePrincipal_log_atom hprime hk hy (prime79Plus_prime_log_bounds hpm).1
        (prime79Plus_prime_log_bounds hpm).2 prime79Plus_log_bounds.1 hwR
    simpa only [← heq] using ht
  apply hp.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg (prime79Plus_atoms_subset)
  intro m hm _
  exact
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm_nonneg (sq_pos_of_pos hy)
      (Finset.mem_Ioc.mp hm).1 (Finset.mem_Ioc.mp hm).2

/-- The actual reciprocal principal sum satisfies the strengthened pointwise lower bound. -/
theorem prime79Plus_reciprocal :
    2 * Real.log (prime79PlusRadius : ℝ) - Analysis.pointwiseReciprocalLoss prime79PlusRadius +
        prime79PlusCreditR ≤
      AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum
        ((prime79PlusRadius : ℝ) ^ 2) := by
  have hc := (Rat.cast_le (K := ℝ)).mpr (prime79Plus_rec_check)
  simp only [prime79PlusReciprocalLoss, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
    Rat.cast_ofNat, Rat.cast_pow] at hc
  dsimp only [Analysis.pointwiseReciprocalLoss]
  linarith only [hc, prime79Plus_rec_sum, prime79Plus_log_bounds.2]

/-- The actual smoothed principal sum satisfies the strengthened pointwise lower bound. -/
theorem prime79Plus_smoothed :
    (prime79PlusRadius : ℝ) ^ 2 - prime79PlusRadius / 20 -
          (1839 / 500 : ℝ) * Real.log prime79PlusRadius -
          21 / 20 +
        prime79PlusCreditS ≤
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum ((prime79PlusRadius : ℝ) ^ 2) := by
  have hc := (Rat.cast_le (K := ℝ)).mpr (prime79Plus_log_check)
  simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_pow] at hc
  linarith only [hc, prime79Plus_log_sum, prime79Plus_log_bounds.1]

end PseudoPrime.LLS.PaperStatements
