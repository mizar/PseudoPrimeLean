/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.AbstractFuncEq
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! Elementary norm estimates for the Riemann zeta function. -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Elementary bound: on a vertical line, `Γ` is dominated in norm by its value at the real
part, via the triangle inequality applied to the Euler integral. -/
theorem norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) : ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral]
  have hbound :
    ‖∫ x in Set.Ioi (0 : ℝ), ((-x).exp : ℂ) * (x : ℂ) ^ (s - 1)‖ ≤
      ∫ x in Set.Ioi (0 : ℝ), ‖((-x).exp : ℂ) * (x : ℂ) ^ (s - 1)‖ :=
    MeasureTheory.norm_integral_le_integral_norm _
  refine hbound.trans_eq ?_
  rw [Real.Gamma_eq_integral hs]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  simp only [Set.mem_Ioi] at hx
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  congr 1

/-- If `Re w > 1`, then `w` avoids every pole of `Γ` and the point `1`, which is what
`riemannZeta_one_sub` needs as side conditions. -/
theorem side_conditions_of_one_lt_re {w : ℂ} (hw : 1 < w.re) : (∀ n : ℕ, w ≠ -n) ∧ w ≠ 1 := by
  refine ⟨fun n hn => ?_, fun h => ?_⟩
  · have hre := congrArg Complex.re hn
    rw [Complex.neg_re, Complex.natCast_re] at hre
    linarith only [hw, hre, Nat.cast_nonneg (α := ℝ) n]
  · rw [h] at hw
    simp only [Complex.one_re, lt_self_iff_false] at hw

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
