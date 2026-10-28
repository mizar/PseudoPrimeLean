/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalPowerBounds
public import PseudoPrime.Analysis.LogTaylorBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedMangoldtBounds
public import PseudoPrime.Analysis.TruncatedEulerCertificates

/-! # Rational certificates for finite Dirichlet prefixes and Euler bounds -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For r>0,N>=3, a numerator cap a, positive denominator floor b and a<=cap*b
bound the full Euler series by cap. Compare positive ratios and the truncated bound.
This removes infinite sums from scalar certification. -/
theorem tsum_vonMangoldt_le_of_truncated_bounds {r a b cap : ℝ} (hr : 0 < r) {N : ℕ} (hN : 3 ≤ N)
    (ha : Analysis.truncatedLogDirichletUpper r N ≤ a)
    (hb : b ≤ Analysis.truncatedPowerDirichletLower r N) (hb0 : 0 < b) (hc : a ≤ cap * b) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r)) ≤ cap := by
  have ha0 := (Analysis.truncatedLogDirichletUpper_nonneg hr N).trans ha
  have hcap :=
    (div_le_div_of_nonneg_right ha (Analysis.truncatedPowerDirichletLower_pos hr N).le).trans
      (div_le_div_of_nonneg_left ha0 hb0 hb)
  exact (tsum_vonMangoldt_le_truncatedEuler hr hN).trans (hcap.trans ((div_le_iff₀ hb0).mpr hc))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
