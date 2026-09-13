/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! Elementary norm estimates for the Riemann zeta function. -/

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

/-- Elementary bound: for `Re s > 1`, `ζ` is dominated in norm by the real Dirichlet series at
the real part, via the triangle inequality applied to `zeta_eq_tsum_one_div_nat_cpow`. -/
theorem norm_riemannZeta_le {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ ∑' n : ℕ, (n : ℝ) ^ (-s.re) := by
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  have hterm : ∀ n : ℕ, ‖(1 : ℂ) / (n : ℂ) ^ s‖ = (n : ℝ) ^ (-s.re) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn0
    · have hsne : s ≠ 0 := fun h => by
        rw [h] at hs
        simp only [Complex.zero_re] at hs
        linarith
      have hneg : -s.re ≠ 0 := by linarith
      simp only [CharP.cast_eq_zero, Complex.zero_cpow hsne, div_zero, norm_zero]
      rw [Real.zero_rpow hneg]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
      rw [norm_div, norm_one, show ((n : ℂ)) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm,
        Complex.norm_cpow_eq_rpow_re_of_pos hnpos, Real.rpow_neg hnpos.le]
      simp only [one_div]
  have hsummable : Summable (fun n : ℕ => ‖(1 : ℂ) / (n : ℂ) ^ s‖) := by
    simp_rw [hterm]
    exact Real.summable_nat_rpow.mpr (by linarith)
  calc
    ‖∑' n : ℕ, (1 : ℂ) / (n : ℂ) ^ s‖ ≤ ∑' n : ℕ, ‖(1 : ℂ) / (n : ℂ) ^ s‖ :=
      norm_tsum_le_tsum_norm hsummable
    _ = ∑' n : ℕ, (n : ℝ) ^ (-s.re) := tsum_congr hterm

/-- Elementary crude bound `‖cos z‖ ≤ 2 cosh(Im z)`, from the real/imaginary decomposition
`cos z = cos(Re z) cosh(Im z) - sin(Re z) sinh(Im z) I` and `|cos|, |sin| ≤ 1`,
`|sinh x| ≤ cosh x`. -/
theorem norm_cos_le_two_mul_cosh_im (z : ℂ) : ‖Complex.cos z‖ ≤ 2 * Real.cosh z.im := by
  have hsinh_le : |Real.sinh z.im| ≤ Real.cosh z.im := by
    have hpos : (0 : ℝ) < Real.cosh z.im := Real.cosh_pos _
    nlinarith only [Real.cosh_sq_sub_sinh_sq z.im, sq_abs (Real.sinh z.im),
      abs_nonneg (Real.sinh z.im), hpos]
  rw [Complex.cos_eq, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin, ←
    Complex.ofReal_sinh]
  calc
    ‖(Real.cos z.re : ℂ) * (Real.cosh z.im : ℂ) -
            (Real.sin z.re : ℂ) * (Real.sinh z.im : ℂ) * Complex.I‖ ≤
        ‖(Real.cos z.re : ℂ) * (Real.cosh z.im : ℂ)‖ +
          ‖(Real.sin z.re : ℂ) * (Real.sinh z.im : ℂ) * Complex.I‖ :=
      norm_sub_le _ _
    _ = |Real.cos z.re| * Real.cosh z.im + |Real.sin z.re| * |Real.sinh z.im| := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
        Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]
    _ ≤ 1 * Real.cosh z.im + 1 * Real.cosh z.im := by
      gcongr
      · exact Real.abs_cos_le_one _
      · exact Real.abs_sin_le_one _
    _ = 2 * Real.cosh z.im := by ring

/-- If `Re w > 1`, then `w` avoids every pole of `Γ` and the point `1`, which is what
`riemannZeta_one_sub` needs as side conditions. -/
theorem side_conditions_of_one_lt_re {w : ℂ} (hw : 1 < w.re) : (∀ n : ℕ, w ≠ -n) ∧ w ≠ 1 := by
  refine ⟨fun n hn => ?_, fun h => ?_⟩
  · have hre := congrArg Complex.re hn
    rw [Complex.neg_re, Complex.natCast_re] at hre
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  · rw [h] at hw
    simp only [Complex.one_re, lt_self_iff_false] at hw

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
