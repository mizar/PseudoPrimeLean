/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.TriangularLargeIndexNumerics
public import PseudoPrime.LLS.TriangularLargeFactorComparison

/-! # Certified alpha-18 large-index prime witness -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, for log q >= 10^20 and subgroup index at least 10^9,
there is a prime through (283/1000)log(q)^2 dividing q or outside the subgroup.
Apply the certified numerical gap; no additional arithmetic-factor or analytic budget premise
      remains. -/
theorem exists_prime_factor_or_outside_triangular18_large_index {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hi : 1000000000 ≤ H.index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlog : (100000000000000000000 : ℝ) ≤ Real.log q) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (283 / 1000 : ℝ) * (Real.log q) ^ 2 ∧ (p ∣ q ∨ ¬residueInSubgroup q H p) := by
  have hx := (Analysis.triangular18_large_scale_bounds hlog).1
  have hh : (1000000000 : ℝ) ≤ (H.index : ℝ) := by exact_mod_cast hi
  exact
    exists_prime_factor_or_outside_of_triangular18_gap H hGRH hx
      (Analysis.triangular18_large_index_gap hlog hh)

end PseudoPrime.LLS.PaperStatements
