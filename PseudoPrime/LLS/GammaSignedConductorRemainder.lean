/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaRefinedVariableScaleBounds
public import PseudoPrime.LLS.GammaSignedLeftIntegral
public import PseudoPrime.LLS.GammaArchimedeanSign

/-! # Variable-scale Gamma remainder with signed conductor integral

The completed explicit formula keeps the exact nonpositive left conductor component.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For primitive nonprincipal data under GRH and scale at least two, the actual
summand-plus-zero remainder has upper real bound given by the pole cost, exact signed
left conductor contribution and conductor-free cost 43 x^(-9/16).
Use the completed residue identity and the proved signed left integral bound. -/
theorem re_gamma_primitive_remainder_le_signed_conductor {q m : ℕ} [NeZero m]
    {χ : DirichletCharacter ℂ m} (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x : ℝ} (hx : 2 ≤ x) :
    ((∑' n : ℕ, gammaMellinKernel.summand χ x n) +
          (∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ)).re ≤
      ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        PseudoPrime.Analysis.gammaNegativeConductorTerm (Real.log m) x +
        43 * x ^ (-9 / 16 : ℝ) := by
  let S := ∑' n : ℕ, gammaMellinKernel.summand χ x n
  let Z := ∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ
  let P :=
    MellinKernel.weightedResidue gammaMellinKernel (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x
      (-1 / 2)
  let J :=
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
          (gammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))
  have hx1 : 1 ≤ x := le_trans (by norm_num only : (1 : ℝ) ≤ 2) hx
  have hr : (S - (P - Z + J)).re ≤ 0 := by
    have h :=
      MellinKernel.tsum_summand_eq_completed_residue_formula gammaMellinKernel
        (by linarith only [hm] : 2 ≤ m) hGRH hp hne hinv (a := -9 / 16) (b := 9 / 16)
        (by norm_num only)
        (by
          change (-1 / 2 - 1 / 8 : ℝ) < -9 / 16; norm_num only)
        (by
          change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
        (by norm_num only) (by norm_num only) hx1 (by norm_num only) (by norm_num only)
    dsimp only at h
    dsimp only [S, P, Z, J]
    rw [h, add_sub_cancel_left]
    exact
      gamma_right_integral_re_nonpos χ (by norm_num only)
        (by
          change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
        (by norm_num only) hx
  have hP0 := gamma_poleResidue_le_ambient hq hm hmq hp hne hGRH (zero_lt_one.trans_le hx1)
  have hP : ‖P‖ ≤ ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x := hP0
  have hJ :
    J.re ≤
      PseudoPrime.Analysis.gammaNegativeConductorTerm (Real.log m) x + 43 * x ^ (-9 / 16 : ℝ) := by
    have h := re_gammaSignedLeftIntegral_le_conductor_add hp hne hinv (zero_lt_one.trans_le hx1)
    rw [gammaSignedLeftIntegral_eq_original] at h
    exact h
  have he : S + Z = (S - (P - Z + J)) + P + J := by ring
  change (S + Z).re ≤ _
  rw [he]
  simp only [Complex.add_re]
  linarith only [hr, hP, hJ, Complex.re_le_norm P]

/-- The actual Gamma summand-plus-zero remainder has conductor-free left allowance
43 x^(-9/16), in addition to the existing ambient pole cost. Discard the exact conductor
term only after proving that it is nonpositive. -/
theorem re_gamma_primitive_remainder_le_conductor_free {q m : ℕ} [NeZero m]
    {χ : DirichletCharacter ℂ m} (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x : ℝ} (hx : 2 ≤ x) :
    ((∑' n : ℕ, gammaMellinKernel.summand χ x n) +
          (∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ)).re ≤
      ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x + 43 * x ^ (-9 / 16 : ℝ) := by
  have h := re_gamma_primitive_remainder_le_signed_conductor hq hm hmq hp hne hinv hGRH hx
  have hc :=
    PseudoPrime.Analysis.gammaNegativeConductorTerm_nonpos (Real.log_natCast_nonneg m)
      (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx)
  linarith only [h, hc]

end PseudoPrime.LLS.PaperStatements
