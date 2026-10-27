/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroClassification

/-! # Existence of zeta trivial zeros and classification outside the critical strip -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For every natural n, zeta vanishes at -2(n+1). This is the negative-even
zero theorem of mathlib and supplies the modulus-one classification branch. -/
theorem zeta_trivial_zero_exists (n : ℕ) : riemannZeta (-2 * ((n : ℂ) + 1)) = 0 := by
  exact riemannZeta_neg_two_mul_nat_add_one n

/-- A zeta zero outside the closed critical strip is a negative even integer.
Use unconditional right-half-plane nonvanishing and the existing negative
half-plane classification. This includes zeta separately from nonprincipal L. -/
theorem zeta_trivial_of_zero_outside_strip {s : ℂ} (hz : riemannZeta s = 0)
    (hout : ¬(0 ≤ s.re ∧ s.re ≤ 1)) : ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
  have hr : s.re < 1 := lt_of_not_ge fun h ↦ riemannZeta_ne_zero_of_one_le_re h hz
  have hl : s.re < 0 := lt_of_not_ge fun h ↦ hout ⟨h, hr.le⟩
  exact exists_nat_eq_neg_two_mul_add_one_of_riemannZeta_zero_re_neg hl hz

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
