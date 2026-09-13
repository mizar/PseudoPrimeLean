import PseudoPrime.AnalyticNumberTheory.RiemannZeta.Growth
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.GrowthBounds

/-! Kernel-independent estimates extracted from the contour applications. -/

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- On `Re s = -(2m+1)`, a single constant gives a bound for `‖ζ'/ζ‖`
valid for every real `t`, with affine growth in `m` and `|t|`.
This line contains no trivial zeros; the bound is not independent of `t`. -/
theorem exists_norm_logDeriv_riemannZeta_neg_odd_add_mul_I_le_uniform :
    ∃ C : ℝ,
      ∀ (m : ℕ) (t : ℝ),
        ‖logDeriv riemannZeta (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C + 4 * Real.pi * |t| + (2 * (m : ℝ) + 1) := by
  obtain ⟨C₀, hC₀⟩ := exists_neg_log_norm_Gamma_one_add_mul_I_le_uniform
  refine
    ⟨Real.log (2 * Real.pi) + 8 * Real.log (Real.sqrt Real.pi) + 8 * C₀ + Real.pi / 2 +
        ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (2 : ℝ),
      fun m t => ?_⟩
  have hbase := norm_logDeriv_riemannZeta_neg_odd_add_mul_I_le m t
  have hGammaB := hC₀ (-t)
  have heq : (1 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I = (1 : ℂ) - (t : ℂ) * Complex.I := by
    push_cast
    ring
  rw [heq, abs_neg] at hGammaB
  have h2m2 : (2 : ℝ) ≤ 2 * (m : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hsum_le :=
    tsum_vonMangoldt_div_rpow_antitone (x := 2) (y := 2 * (m : ℝ) + 2) (by norm_num only) h2m2
  have hcast : ((2 * m + 2 : ℕ) : ℝ) = 2 * (m : ℝ) + 2 := by
    push_cast
    ring
  linarith [hbase, hGammaB, hsum_le]

/-- A concrete witness constant, following the `.choose`/`.choose_spec` idiom. -/
noncomputable def qMinusOneLeftVerticalConst : ℝ :=
  exists_norm_logDeriv_riemannZeta_neg_odd_add_mul_I_le_uniform.choose

/-- The explicit `m`- and `t`-dependent bound on `‖ζ'/ζ‖` along the left-vertical line. -/
noncomputable def leftVerticalZetaLogDerivBound (m : ℕ) (t : ℝ) : ℝ :=
  qMinusOneLeftVerticalConst + 4 * Real.pi * |t| + (2 * (m : ℝ) + 1)

theorem norm_logDeriv_riemannZeta_neg_odd_add_mul_I_le_uniform (m : ℕ) (t : ℝ) :
    ‖logDeriv riemannZeta (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      leftVerticalZetaLogDerivBound m t :=
  exists_norm_logDeriv_riemannZeta_neg_odd_add_mul_I_le_uniform.choose_spec m t

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
