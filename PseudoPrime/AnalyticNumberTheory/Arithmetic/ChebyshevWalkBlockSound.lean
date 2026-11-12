/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevWalkBlockCheck
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevWalkSound
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtChecker
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtCrossCell

/-! # Soundness of fixed-point psi walk crossing guards -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Valid endpoint states and a successful integer guard give the four-fifths
square-root estimate throughout the corresponding half-open real interval.
The integer guards provide the two cross-endpoint inequalities. -/
theorem psi_walk_block_guard_sound {S : ℕ} {s t : PsiWalkState} {ca cb : ℕ} {x : ℝ}
    (hs : PsiWalkValid S s) (ht : PsiWalkValid S t) (hg : psiWalkBlockGuard S s t ca cb = true)
    (hax : (s.n : ℝ) ≤ x) (hxb : x < (t.n + 1 : ℕ)) :
    |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x := by
  have hc :
    0 < S ∧
      25 * ca ^ 2 ≤ 16000000 * s.n ∧
      25 * cb ^ 2 ≤ 16000000 * (t.n + 1) ∧
      1000 * S * (t.n + 1) ≤ 1000 * s.psiLo + S * cb ∧ 1000 * t.psiHi ≤ 1000 * S * s.n + S * ca :=
    of_decide_eq_true hg
  have hS0 : (0 : ℝ) < S := Nat.cast_pos.mpr hc.1
  have hleft : (s.psiLo : ℝ) / S ≤ Chebyshev.psi s.n := by
    apply (div_le_iff₀ hS0).2
    simpa only [mul_comm] using hs.2.2.2.1
  have hright : Chebyshev.psi t.n ≤ (t.psiHi : ℝ) / S := by
    apply (le_div_iff₀ hS0).2
    simpa only [mul_comm] using ht.2.2.2.2
  have hta : (1 : ℝ) ≤ s.n := by exact_mod_cast hs.1
  have ht' : Chebyshev.psi ((t.n + 1) - 1 : ℕ) ≤ (t.psiHi : ℝ) / S := by
    simpa only [Nat.add_sub_cancel] using hright
  have hl' : (1000 : ℝ) * S * (t.n + 1) ≤ 1000 * s.psiLo + S * cb := by exact_mod_cast hc.2.2.2.1
  have hu' : (1000 : ℝ) * t.psiHi ≤ 1000 * S * s.n + S * ca := by exact_mod_cast hc.2.2.2.2
  have hl : ((t.n + 1 : ℕ) : ℝ) ≤ (s.psiLo : ℝ) / S + (cb : ℝ) / 1000 := by
    have h : ((t.n + 1 : ℕ) : ℝ) - (cb : ℝ) / 1000 ≤ (s.psiLo : ℝ) / S := by
      apply (le_div_iff₀ hS0).2
      norm_num only [Nat.cast_add, Nat.cast_one]
      nlinarith only [hl']
    linarith only [h]
  have hu : (t.psiHi : ℝ) / S ≤ (s.n : ℝ) + (ca : ℝ) / 1000 := by
    apply (div_le_iff₀ hS0).2
    nlinarith only [hu']
  exact
    psi_four_fifths_cross_cell hta hax hxb hleft ht' (scaled_sqrt_lower hc.2.1)
      (scaled_sqrt_lower hc.2.2.1) hl hu

end PseudoPrime.AnalyticNumberTheory.Arithmetic
