/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.EndpointFiniteProfile
public import PseudoPrime.Analysis.EndpointFiniteAtoms
import PseudoPrime.Analysis.EndpointFiniteSumsInternal

/-! # Table-free finite principal endpoint bounds -/

public section

namespace PseudoPrime.Analysis

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
