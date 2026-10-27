/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianSignedResolventWeight
public import PseudoPrime.Analysis.GammaSignedResolventWeight
public import PseudoPrime.Analysis.SignedExponentialMoments

/-! # Gaussian and Gamma Euler-weight comparison -/

@[expose] public section

set_option maxRecDepth 32768

namespace PseudoPrime.Analysis

/-- The leading node of the Gaussian-minus-17/20-Gamma resolvent combination.
Combining the shared node avoids duplicating its coefficient in the moment certificate. -/
def gaussianGammaDifferenceHead : ℚ × ℚ :=
  (11 / 20, 284090057 / 2000000000)

/-- The remaining nodes of the Gaussian-minus-17/20-Gamma resolvent combination.
Derive both tails from their source coefficient lists so later edits stay synchronized. -/
def gaussianGammaDifferenceTail : List (ℚ × ℚ) :=
  gaussianResolventCoefficients.tail ++
    gammaResolventCoefficients.tail.map (fun ab ↦ (ab.1, -(17 / 20) * ab.2))

/-- All nodes of the Gaussian-minus-17/20-Gamma resolvent combination. -/
def gaussianGammaDifferenceCoefficients : List (ℚ × ℚ) :=
  gaussianGammaDifferenceHead :: gaussianGammaDifferenceTail

/-- The exact rational reflected moment of the combined Gaussian and Gamma coefficients. -/
def gaussianGammaDifferenceMoment (n : ℕ) : ℚ :=
  (gaussianGammaDifferenceCoefficients.map (fun ab ↦ ab.2 * ((7 : ℚ) - ab.1) ^ n)).sum

/-- Casting a list of rational node terms to reals commutes with its finite sum.
Input: a finite list of Gaussian/Gamma resolvent nodes and a moment order.
Claim: the real reflected moment is the cast of its exact rational counterpart.
Proof: induct on the list and cast each term with exact ring-hom identities.
Role: transfer the finite rational moment checks to the real exponential certificate. -/
theorem list_real_sum_eq_cast_rat_sum (l : List (ℚ × ℚ)) (n : ℕ) :
    (l.map (fun ab ↦ (ab.2 : ℝ) * (7 - (ab.1 : ℝ)) ^ n)).sum =
      ((l.map (fun ab ↦ ab.2 * ((7 : ℚ) - ab.1) ^ n)).sum : ℝ) := by
  induction l with
  | nil => norm_num only [List.map_nil, List.sum_nil, Rat.cast_zero]
  | cons ab l ih =>
    simp only [List.map_cons, List.sum_cons, Rat.cast_add]
    have hterm : (ab.2 : ℝ) * (7 - (ab.1 : ℝ)) ^ n = ((ab.2 * ((7 : ℚ) - ab.1) ^ n : ℚ) : ℝ) := by
      norm_num only [Rat.cast_mul, Rat.cast_sub, Rat.cast_pow, Rat.cast_ofNat]
    rw [hterm, ih]

/-- The first 64 reflected moments are nonnegative by exact rational arithmetic. -/
theorem gaussianGammaDifference_small_moments :
    ∀ n ∈ Finset.range 64, 0 ≤ gaussianGammaDifferenceMoment n := by decide +kernel

/-- Every reflected tail scale lies between zero and the leading reflected scale. -/
theorem gaussianGammaDifference_tail_range :
    gaussianGammaDifferenceTail.Forall
      (fun ab ↦ (0 : ℚ) ≤ 7 - ab.1 ∧ 7 - ab.1 ≤ 7 - gaussianGammaDifferenceHead.1) := by
  decide +kernel

/-- At degree 64 the positive leading coefficient dominates all negative tail terms. -/
theorem gaussianGammaDifference_anchor_dominates :
    (gaussianGammaDifferenceTail.map (fun ab ↦ max 0 (-(ab.2 : ℝ)) * (7 - (ab.1 : ℝ)) ^ 64)).sum ≤
      (gaussianGammaDifferenceHead.2 : ℝ) * (7 - (gaussianGammaDifferenceHead.1 : ℝ)) ^ 64 := by
  simp only [gaussianGammaDifferenceTail, gaussianResolventCoefficients, gammaResolventCoefficients,
    List.tail_cons]
  norm_num only [gaussianGammaDifferenceHead, List.map_cons, List.map_nil, List.map_append,
    List.sum_cons, List.sum_nil, List.sum_append, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg,
    Rat.cast_mul, Rat.cast_sub, max_def, ite_true, ite_false]

/-- The rational moment casts to the corresponding real sum.
Input: a natural moment order.
Claim: the combined real moment equals the cast rational moment.
Proof: cast the leading term and use the list-sum cast lemma on the derived tail.
Role: supply the finite-prefix hypotheses for the all-orders positivity theorem. -/
theorem gaussianGammaDifference_moment_cast (n : ℕ) :
    ((gaussianGammaDifferenceHead :: gaussianGammaDifferenceTail).map
          (fun ab ↦ (ab.2 : ℝ) * (7 - (ab.1 : ℝ)) ^ n)).sum =
      (gaussianGammaDifferenceMoment n : ℝ) := by
  simp only [List.map_cons, List.sum_cons]
  have hhead :
    (gaussianGammaDifferenceHead.2 : ℝ) * (7 - (gaussianGammaDifferenceHead.1 : ℝ)) ^ n =
      ((gaussianGammaDifferenceHead.2 * ((7 : ℚ) - gaussianGammaDifferenceHead.1) ^ n : ℚ) :
        ℝ) := by
    norm_num only [Rat.cast_mul, Rat.cast_pow, Rat.cast_sub, Rat.cast_ofNat]
  have htail := list_real_sum_eq_cast_rat_sum gaussianGammaDifferenceTail n
  rw [hhead, htail]
  norm_num only [gaussianGammaDifferenceMoment, gaussianGammaDifferenceCoefficients, List.map_cons,
    List.sum_cons, Rat.cast_add]

/-- Every real reflected moment of the combined coefficients is nonnegative.
Proof: the first 64 moments are exact, then the degree-64 anchor controls the tail.
Role: imply positivity of the Gaussian Euler weight minus 17/20 of the Gamma weight. -/
theorem gaussianGammaDifference_all_moments_nonneg :
    ∀ n : ℕ,
      0 ≤
        (gaussianGammaDifferenceCoefficients.map
            (fun ab ↦ (ab.2 : ℝ) * (7 - (ab.1 : ℝ)) ^ n)).sum := by
  apply
    list_moments_nonneg_of_finite_certificate (N := 64) (a := gaussianGammaDifferenceHead) (l :=
      gaussianGammaDifferenceTail)
  · norm_num only [gaussianGammaDifferenceHead]
  · intro ab hab
    have hq := List.forall_iff_forall_mem.mp gaussianGammaDifference_tail_range ab hab
    exact_mod_cast hq
  · intro n hn
    rw [gaussianGammaDifference_moment_cast]
    exact Rat.cast_nonneg.mpr (gaussianGammaDifference_small_moments n (Finset.mem_range.mpr hn))
  · simpa only [gaussianGammaDifferenceHead] using gaussianGammaDifference_anchor_dominates

/-- The exponential combination of the derived coefficients is the Gaussian sum
minus seventeen twentieths of the Gamma sum. -/
theorem gaussianGammaDifferenceExpSum_eq_sub (t : ℝ) :
    (gaussianGammaDifferenceCoefficients.map
          (fun ab ↦ (ab.2 : ℝ) * Real.exp ((7 - (ab.1 : ℝ)) * t))).sum =
      (gaussianResolventCoefficients.map
            (fun ab ↦ (ab.2 : ℝ) * Real.exp ((7 - (ab.1 : ℝ)) * t))).sum -
        (17 / 20 : ℝ) *
          (gammaResolventCoefficients.map
              (fun ab ↦ (ab.2 : ℝ) * Real.exp ((7 - (ab.1 : ℝ)) * t))).sum := by
  simp only [gaussianGammaDifferenceCoefficients, gaussianGammaDifferenceHead,
    gaussianGammaDifferenceTail, gaussianResolventCoefficients, gammaResolventCoefficients]
  simp only [List.tail_cons]
  simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append, List.map_nil,
    List.sum_nil, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_mul]
  ring_nf

/-- The Gamma Euler weight factors into a positive exponential and its reflected
exponential sum, matching the Gaussian factorization. -/
theorem gammaResolventEulerWeight_eq_exp_moments {m : ℝ} (hm : 0 < m) :
    gammaResolventEulerWeight m =
      Real.exp (-(15 / 2 : ℝ) * Real.log m) *
        (gammaResolventCoefficients.map
            (fun ab ↦ (ab.2 : ℝ) * Real.exp ((7 - (ab.1 : ℝ)) * Real.log m))).sum := by
  unfold gammaResolventEulerWeight
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab _
  rw [Real.rpow_def_of_pos hm]
  have he :
    Real.log m * (-(1 / 2 + (ab.1 : ℝ))) =
      -(15 / 2 : ℝ) * Real.log m + (7 - (ab.1 : ℝ)) * Real.log m := by
    ring
  rw [he, Real.exp_add]
  ring

/-- At every real base at least one, the Gaussian Euler weight dominates
seventeen twentieths of the Gamma Euler weight. -/
theorem gaussianGamma_weight_difference_nonneg {m : ℝ} (hm : 1 ≤ m) :
    0 ≤ gaussianResolventEulerWeight m - (17 / 20 : ℝ) * gammaResolventEulerWeight m := by
  rw [gaussianResolventEulerWeight_eq_exp_moments (zero_lt_one.trans_le hm)]
  rw [gammaResolventEulerWeight_eq_exp_moments (zero_lt_one.trans_le hm)]
  let gaussianSum :=
    (gaussianResolventCoefficients.map
        (fun ab ↦ (ab.2 : ℝ) * Real.exp ((7 - (ab.1 : ℝ)) * Real.log m))).sum
  let gammaSum :=
    (gammaResolventCoefficients.map
        (fun ab ↦ (ab.2 : ℝ) * Real.exp ((7 - (ab.1 : ℝ)) * Real.log m))).sum
  have hfactor :
    Real.exp (-(15 / 2 : ℝ) * Real.log m) * gaussianSum -
        (17 / 20 : ℝ) * (Real.exp (-(15 / 2 : ℝ) * Real.log m) * gammaSum) =
      Real.exp (-(15 / 2 : ℝ) * Real.log m) * (gaussianSum - (17 / 20 : ℝ) * gammaSum) := by
    ring
  rw [hfactor, ← gaussianGammaDifferenceExpSum_eq_sub]
  have hsum :=
    list_exp_nonneg_of_moments gaussianGammaDifferenceCoefficients (fun ab ↦ (ab.2 : ℝ))
      (fun ab ↦ 7 - (ab.1 : ℝ)) gaussianGammaDifference_all_moments_nonneg (Real.log_nonneg hm)
  exact mul_nonneg (Real.exp_pos _).le hsum

end PseudoPrime.Analysis
