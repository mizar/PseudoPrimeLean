/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.EndpointFiniteData
public import PseudoPrime.Analysis.EndpointFiniteAtoms

/-! # Internal finite principal endpoint sums -/

public section

namespace PseudoPrime.Analysis

/-- Embed every distinct selected positive prime power in the original finite sum. -/
theorem finitePrincipal_atoms_subset (f : FinitePrimeProfile) :
    f.atoms ⊆ Finset.Ioc 0 ⌊(f.radius : ℝ) ^ 2⌋₊ := by
  intro m hm
  rcases principalAtom_data f m hm with ⟨hm0, _, _, _, _, hmx, _, _⟩
  exact Finset.mem_Ioc.mpr ⟨hm0, Nat.le_floor (by exact_mod_cast hmx)⟩

/-- The rational reciprocal payload is below the actual principal reciprocal sum. -/
theorem finitePrincipal_rec_sum (f : FinitePrimeProfile) :
    (f.reciprocalLower : ℝ) ≤
      AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum ((f.radius : ℝ) ^ 2) := by
  have hy : (0 : ℝ) < f.radius :=
    lt_of_lt_of_le (by norm_num only) (finitePrincipal_radius_bounds f).1
  have hp :
    (f.reciprocalLower : ℝ) ≤
      ∑ m ∈ f.atoms,
        AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm ((f.radius : ℝ) ^ 2) m := by
    simp only [FinitePrimeProfile.reciprocalLower, Rat.cast_sum, Rat.cast_mul, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_sub, Rat.cast_one, Rat.cast_pow]
    apply Finset.sum_le_sum
    intro m hm
    rcases principalAtom_data f m hm with ⟨hm0, hpm, hprime, hk, heq, hmx, _, _⟩
    have hmxR : (m : ℝ) ≤ (f.radius : ℝ) ^ 2 := by exact_mod_cast hmx
    have ht :=
      finitePrincipal_rec_atom hprime hk (sq_pos_of_pos hy)
        (by simpa only [← Nat.cast_pow, ← heq] using hmxR) (principalLog_bounds hpm).1
    simpa only [← Nat.cast_pow, ← heq] using ht
  apply hp.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg (finitePrincipal_atoms_subset f)
  intro m hm _
  exact
    AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm_nonneg (sq_pos_of_pos hy)
      (Finset.mem_Ioc.mp hm).1 (Finset.mem_Ioc.mp hm).2

/-- The rational smoothed payload is below the actual principal smoothed sum. -/
theorem finitePrincipal_log_sum (f : FinitePrimeProfile) :
    (f.smoothedLower : ℝ) ≤
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum ((f.radius : ℝ) ^ 2) := by
  have hy : (0 : ℝ) < f.radius :=
    lt_of_lt_of_le (by norm_num only) (finitePrincipal_radius_bounds f).1
  have hp :
    (f.smoothedLower : ℝ) ≤
      ∑ m ∈ f.atoms,
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm ((f.radius : ℝ) ^ 2) m := by
    simp only [FinitePrimeProfile.smoothedLower, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast,
      Rat.cast_sub, Rat.cast_ofNat]
    apply Finset.sum_le_sum
    intro m hm
    rcases principalAtom_data f m hm with ⟨_, hpm, hprime, hk, heq, _, _, hw⟩
    have hwR : (0 : ℝ) ≤ 2 * f.logLo - principalAtomExp m * principalLogHi m.minFac := by
      exact_mod_cast hw
    have ht :=
      finitePrincipal_log_atom hprime hk hy (principalLog_bounds hpm).1 (principalLog_bounds hpm).2
        (finitePrincipal_log_bounds f).1 hwR
    simpa only [← heq] using ht
  apply hp.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg (finitePrincipal_atoms_subset f)
  intro m hm _
  exact
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm_nonneg (sq_pos_of_pos hy)
      (Finset.mem_Ioc.mp hm).1 (Finset.mem_Ioc.mp hm).2

end PseudoPrime.Analysis
