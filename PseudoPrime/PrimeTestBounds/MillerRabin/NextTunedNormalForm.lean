/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSurplusComparison

/-! # Equivalent MR selection formulas without dominated Gaussian branches

The canonical functions keep their established API. These normal forms have exactly the same
values while removing the four directly added tuned Gaussian profiles and two tuned seeded
profiles. At the common closed entrance 63, their surplus replacements dominate them.
The small branch, fixed-79 guard and independent triangular guards remain unchanged.
This is an equality of formulas, not an additional improvement or a build-cost claim.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Evaluate the canonical witness cutoff without its six dominated tuned Gaussian branches.
Below 3000 keep the exact small branch. Below log scale 63 use the finite/fixed-79 selection;
above it intersect the guarded high minimum, seeded surplus family and candidate A. -/
noncomputable def nextTunedNormalEnvelope (n : ℕ) : ℝ :=
  if n < 3000 then smallIntervalBound n
  else
    if 63 ≤ Real.log n then
      min (tunedHighMin (Real.log n) (tunedFiniteWitness n))
        (min (gaussianSeededSurplusFamily (Real.log n)) (gaussianTightBound (Real.log n)))
    else
      min (tunedFiniteWitness n)
        (if Real.log n ≤ LLS.PaperStatements.prime79PlusCap then 79 else tunedFiniteWitness n)

/-- The selected normal formula uses the same guards and surviving candidates.
Replace only the finite witness expression by its exact selected form.
The equality theorem connects this numerical expression to the canonical selected API. -/
noncomputable def nextTunedNormalSelected (n : ℕ) : ℝ :=
  if n < 3000 then smallIntervalBound n
  else
    if 63 ≤ Real.log n then
      min (tunedHighMin (Real.log n) (tunedFiniteSelected n))
        (min (gaussianSeededSurplusFamily (Real.log n)) (gaussianTightBound (Real.log n)))
    else
      min (tunedFiniteSelected n)
        (if Real.log n ≤ LLS.PaperStatements.prime79PlusCap then 79 else tunedFiniteSelected n)

/-- Remove two dominated intermediate terms from an intersected scalar minimum.
A retained high term covers the base, while the final candidate covers both old terms.
This local order identity proves the exact six-branch pruning. -/
private theorem nextTuned_prune_min {B G S H P : ℝ} (hB : H ≤ B) (hG : P ≤ G) (hS : P ≤ S) :
    min (min B (min G (min S H))) P = min H P := by
  have hx : min B (min G (min S H)) ≤ H :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  exact
    le_antisymm (le_min ((min_le_left _ _).trans hx) (min_le_right _ _))
      (le_min
        (le_min ((min_le_left _ _).trans hB)
          (le_min ((min_le_right _ _).trans hG)
            (le_min ((min_le_right _ _).trans hS) (min_le_left _ _))))
        (min_le_right _ _))

/-- Above the small natural branch but below log scale 63, the tuned cutoff is its finite base.
Both analytic guards are inactive and all triangular entrances lie above this range. -/
private theorem tunedWitness_eq_finite_low {n : ℕ} (hN : 3000 ≤ n) (hL : Real.log n < 63) :
    tunedWitnessEnvelope n = tunedFiniteWitness n := by
  rw [tunedWitnessEnvelope, ite_eq_right (not_lt.mpr hN), sharpGuardMin,
    ite_eq_right (not_le.mpr hL), ite_eq_right (not_le.mpr hL),
    tunedHigh_eq_base (by linarith only [hL])]
  simp only [min_self]

/-- At the closed log entrance 63 and above, the canonical cutoff has the pruned three-part form.
Candidate A dominates the old four-profile family; the seeded surplus family dominates
both old seeded profiles. Remove the redundant terms by exact minimum identities. -/
theorem nextTuned_eq_normal_high {n : ℕ} (hL : 63 ≤ Real.log n) :
    nextTunedWitnessEnvelope n =
      min (tunedHighMin (Real.log n) (tunedFiniteWitness n))
        (min (gaussianSeededSurplusFamily (Real.log n)) (gaussianTightBound (Real.log n))) := by
  have hN := large_of_log63 hL
  have h79 : ¬Real.log n ≤ LLS.PaperStatements.prime79PlusCap := by
    norm_num only [LLS.PaperStatements.prime79PlusCap, Rat.cast_div, Rat.cast_ofNat]
    linarith only [hL]
  rw [nextTunedWitnessEnvelope, ite_eq_right (not_lt.mpr hN), ite_eq_right h79, ite_eq_left hL,
    ite_eq_left hL, ← min_assoc, min_self]
  rw [tunedWitnessEnvelope, ite_eq_right (not_lt.mpr hN), sharpGuardMin, ite_eq_left hL,
    ite_eq_left hL]
  apply nextTuned_prune_min
  · exact min_le_left _ _
  · exact
      (min_le_right _ _).trans ((gaussianTight_le_surplus _).trans (gaussianSurplus_le_family _))
  · exact
      (min_le_left _ _).trans
        (min_le_min (seededSurplus_le_tuned false _) (seededSurplus_le_tuned true _))

/-- At every natural input, the pruned normal formula equals the canonical witness cutoff.
Resolve the small branch and scale-63 guard. No GRH or public-envelope monotonicity is needed. -/
theorem nextTuned_eq_normal (n : ℕ) : nextTunedWitnessEnvelope n = nextTunedNormalEnvelope n := by
  by_cases hN : n < 3000
  · rw [nextTuned_eq_small hN, nextTunedNormalEnvelope, ite_eq_left hN]
  · by_cases hL : 63 ≤ Real.log n
    · rw [nextTuned_eq_normal_high hL, nextTunedNormalEnvelope, ite_eq_right hN, ite_eq_left hL]
    · have ht := tunedWitness_eq_finite_low (le_of_not_gt hN) (lt_of_not_ge hL)
      simp only [nextTunedWitnessEnvelope, nextTunedNormalEnvelope, ite_eq_right hN,
        ite_eq_right hL, ht, min_self, min_assoc, min_comm]
      rw [← min_assoc, min_self]

/-- At every natural input, the pruned selected formula equals the canonical selected cutoff.
Keep the small branch exactly; above it use equality of finite witness and selected expressions. -/
theorem nextTunedSelected_eq_normal (n : ℕ) :
    nextTunedSelectedEnvelope n = nextTunedNormalSelected n := by
  by_cases hN : n < 3000
  · simp only [nextTunedSelectedEnvelope, nextTunedNormalSelected, ite_eq_left hN]
  · have hn : 1 < n := (by norm_num only : 1 < 3000).trans_le (le_of_not_gt hN)
    rw [← nextTuned_eq_selected hn, nextTuned_eq_normal]
    simp only [nextTunedNormalEnvelope, nextTunedNormalSelected, tunedFinite_eq_selected hn]

/-- At every natural input, prime rounding of the pruned witness formula is canonical rounding.
Apply primeRound to the proved real equality; rounding does not create another candidate. -/
theorem nextTunedPrime_eq_normal (n : ℕ) :
    nextTunedPrimeEnvelope n = primeRound (nextTunedNormalEnvelope n) := by
  exact congrArg primeRound (nextTuned_eq_normal n)

/-- From log scale 63, the canonical cutoff is at most candidate A.
Project the surviving Gaussian term from the proved high-scale normal form. -/
theorem nextTuned_le_tight {n : ℕ} (hL : 63 ≤ Real.log n) :
    nextTunedWitnessEnvelope n ≤ gaussianTightBound (Real.log n) := by
  rw [nextTuned_eq_normal_high hL]
  exact (min_le_right _ _).trans (min_le_right _ _)

end PseudoPrime.PrimeTestBounds.MillerRabin
