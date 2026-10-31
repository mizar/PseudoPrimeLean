/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPolePrimeTrivialNumerics
public import PseudoPrime.LLS.GammaNonOneComparison

/-! # Odd non-one witnesses with the prime-two cost retained -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a nonprincipal character under GRH, bound the primitive Gamma arithmetic
sum by the empty-prefix two-pole budget at any larger ambient level and scale at
least one. Retain max(20000,A) for the pole and enlarge the conductor only in
nonnegative factors. This lets one scale control every admissible input below B. -/
theorem gamma_primitiveCharacter_sum_re_le_twoPole_ambient {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    (∑' n : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x n).re ≤
      twoPolePrimeTrivialUpper A ∅ x := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hp := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmA := (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level).trans hqA
  have hC :=
    gamma_primitive_sum_re_le_twoPole (le_max_left 20000 A) hm (hmA.trans (le_max_right 20000 A))
      hGRH hp hnp (inv_ne_one.mpr hnp) hx ∅ ∅
  simp only [Finset.sum_empty, mul_zero, sub_zero] at hC
  have hlog : Real.log χ.conductor ≤ Real.log A :=
    Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero χ.conductor_ne_zero))
      (Nat.cast_le.mpr hmA)
  have hm :=
    mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg (zero_lt_one.trans_le hx).le (-9 / 16 : ℝ))
  dsimp only [twoPolePrimeTrivialUpper]
  simp only [Finset.sum_empty, mul_zero, sub_zero]
  nlinarith only [hC, hlog, hm]

end PseudoPrime.LLS.PaperStatements
