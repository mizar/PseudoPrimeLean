/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevWalkSound

/-! # Composable fixed-point psi interval statements -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A segment carries a valid starting state to a valid ending state and proves
an unconditional four-fifths square-root psi bound on the half-open interval
between their indices. No certificate entries occur in this proposition. -/
def PsiSqrtSegment (S : ℕ) (s t : PsiWalkState) : Prop :=
  PsiWalkValid S s →
    PsiWalkValid S t ∧
      ∀ x : ℝ, (s.n : ℝ) ≤ x → x < t.n → |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x

/-- Adjacent segment statements compose. Their certificate files can be built
independently, and the resulting composition can be organized as a balanced tree. -/
theorem psi_sqrt_segment_comp {S : ℕ} {a b c : PsiWalkState} (hab : PsiSqrtSegment S a b)
    (hbc : PsiSqrtSegment S b c) : PsiSqrtSegment S a c := by
  intro ha
  have hb := hab ha
  have hc := hbc hb.1
  refine ⟨hc.1, ?_⟩
  intro x hax hxc
  by_cases hxb : x < (b.n : ℝ)
  · exact hb.2 x hax hxb
  · exact hc.2 x (le_of_not_gt hxb) hxc

end PseudoPrime.AnalyticNumberTheory.Arithmetic
