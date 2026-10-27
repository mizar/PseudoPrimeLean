/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.TriangularSignedLargeIndexNumerics
public import PseudoPrime.LLS.TriangularSignedLargeFactorComparison

/-! # Signed large-index triangular witness at logarithmic scale 22 trillion -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, for nonzero level, subgroup index at least 10^9 and
logarithmic scale at least 22 trillion, there is a prime at most (282924/1000000)log(q)^2
dividing q or outside the subgroup. Apply the certified signed gap.
No additional scalar-gap or arithmetic-family premise remains. -/
theorem exists_prime_factor_or_outside_triangular18_signed_large_index {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hi : 1000000000 ≤ H.index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlog : (22000000000000 : ℝ) ≤ Real.log q) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (282924 / 1000000 : ℝ) * (Real.log q) ^ 2 ∧
        (p ∣ q ∨ ¬residueInSubgroup q H p) := by
  have hx := (Analysis.triangular18_signed_large_scale_bounds hlog).1
  have hh : (1000000000 : ℝ) ≤ (H.index : ℝ) := by exact_mod_cast hi
  exact
    exists_prime_factor_or_outside_of_triangular18_signed_gap H hGRH hx
      (Analysis.triangular18_signed_large_index_gap hlog hh)

end PseudoPrime.LLS.PaperStatements
