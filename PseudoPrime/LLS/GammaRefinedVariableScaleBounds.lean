/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaVariableScaleBounds
public import PseudoPrime.LLS.GammaRefinedLeftMomentBounds

/-! # Variable-scale remainder with the refined reflected Euler allowance

Preserve the existing pole and archimedean terms while reducing the left-line constant.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Input: primitive nonprincipal conductor data, GRH, and scale at least one.
Claim: the completed Gamma remainder keeps its pole and archimedean terms,
with the left allowance using twenty-eight in place of two hundred eighty-three.
Proof: insert the refined left-integral bound into the completed explicit formula.
Role: quantitative remainder for subsequent signed prefix witness comparisons. -/
theorem norm_gamma_primitive_remainder_le_variable_scale_refined {q m : ℕ} [NeZero m]
    {χ : DirichletCharacter ℂ m} (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x : ℝ} (hx : 1 ≤ x) :
    ‖(∑' n : ℕ, gammaMellinKernel.summand χ x n) +
          (∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ)‖ ≤
      64 / 9 + ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log m + 28) + 5 / 3) := by
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
  have hx1 : 1 ≤ x := hx
  have hr : ‖S - (P - Z + J)‖ ≤ 64 / 9 :=
    norm_gamma_completed_remainder_le_sixty_four_ninths (by linarith only [hm]) hGRH hp hne hinv
      (a := -9 / 16) (b := 9 / 16) (by norm_num only)
      (by
        change (-1 / 2 - 1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) (by norm_num only) hx1 (by norm_num only) (by norm_num only)
  have hP0 := gamma_poleResidue_le_ambient hq hm hmq hp hne hGRH (zero_lt_one.trans_le hx1)
  have hP : ‖P‖ ≤ ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x := hP0
  have hJ : ‖J‖ ≤ x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log m + 28) + 5 / 3) :=
    norm_gamma_left_integral_le_moments_refined hp hne hinv (zero_lt_one.trans_le hx)
  have he : S + Z = (S - (P - Z + J)) + P + J := by ring
  change ‖S + Z‖ ≤ _
  rw [he]
  have hn1 := norm_add_le (S - (P - Z + J)) P
  have hn2 := norm_add_le ((S - (P - Z + J)) + P) J
  linarith only [hr, hP, hJ, hn1, hn2]

end PseudoPrime.LLS.PaperStatements
