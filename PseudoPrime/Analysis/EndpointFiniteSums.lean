/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.EndpointFiniteData
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveComparison
public import PseudoPrime.Analysis.PointwiseReciprocalLowerBound

/-! # Actual principal lower bounds from small prime-power payloads -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A certified lower prime logarithm bounds a reciprocal prime-power term. -/
theorem finitePrincipal_rec_atom {x a : ℝ} {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) (hx : 0 < x)
    (hnx : (p : ℝ) ^ k ≤ x) (hlog : a ≤ Real.log p) :
    a / (p : ℝ) ^ k * (1 - (p : ℝ) ^ k / x) ≤
      AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm x (p ^ k) := by
  rw [AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm_prime_pow hp hk]
  exact
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hlog (pow_nonneg (Nat.cast_nonneg p) k))
      (sub_nonneg.mpr ((div_le_one hx).mpr hnx))

/-- Certified prime and radius logarithms bound a smoothed prime-power term. -/
theorem finitePrincipal_log_atom {y a b z : ℝ} {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) (hy : 0 < y)
    (ha : a ≤ Real.log p) (hb : Real.log p ≤ b) (hz : z ≤ Real.log y) (hw : 0 ≤ 2 * z - k * b) :
    a * (2 * z - k * b) ≤
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm (y ^ 2) (p ^ k) := by
  rw [AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm_prime_pow
      (ne_of_gt (sq_pos_of_pos hy)) hp hk,
    Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  have hm := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  exact mul_le_mul ha (by linarith only [hz, hm]) hw (Real.log_nonneg (by exact_mod_cast hp.one_le))

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

/-- The actual reciprocal principal sum satisfies the strengthened pointwise lower bound. -/
theorem finitePrincipal_reciprocal (f : FinitePrimeProfile) :
    2 * Real.log (f.radius : ℝ) - pointwiseReciprocalLoss f.radius + f.deltaR ≤
      AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum ((f.radius : ℝ) ^ 2) := by
  have hc := (Rat.cast_le (K := ℝ)).mpr (finitePrincipal_rec_check f)
  simp only [FinitePrimeProfile.reciprocalLoss, Rat.cast_add, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] at hc
  dsimp only [pointwiseReciprocalLoss]
  linarith only [hc, finitePrincipal_rec_sum f, (finitePrincipal_log_bounds f).2]

/-- The actual smoothed principal sum satisfies the strengthened pointwise lower bound. -/
theorem finitePrincipal_smoothed (f : FinitePrimeProfile) :
    (f.radius : ℝ) ^ 2 - f.radius / 20 - (1839 / 500 : ℝ) * Real.log f.radius - 21 / 20 + f.deltaS ≤
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum ((f.radius : ℝ) ^ 2) := by
  have hc := (Rat.cast_le (K := ℝ)).mpr (finitePrincipal_log_check f)
  simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_pow] at hc
  linarith only [hc, finitePrincipal_log_sum f, (finitePrincipal_log_bounds f).1]

end PseudoPrime.Analysis
