/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RationalPolePrincipalCutoff
public import PseudoPrime.LLS.MellinKernelPrimitiveSupport
public import PseudoPrime.LLS.MellinKernelTruncatedComparison
/-! # Explicit lower bound for the full fourth-pole principal series -/

public section

namespace PseudoPrime.LLS.PaperStatements
/-- A positive-index principal summand equals the scaled real Mangoldt weight. -/
theorem fourPole_principal_summand_eq {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    ((MellinKernel.summand rationalPoleFourKernel) (1 : DirichletCharacter ℂ
      1) x n).re =
      ArithmeticFunction.vonMangoldt n * fourScaledWeight x n := by
  simp only [MellinKernel.summand, ite_eq_right hn,
    MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), mul_one,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  dsimp only [fourScaledWeight, fourPoleKernelWeight]
  rw [Real.sqrt_div (Nat.cast_nonneg n)]
  have hs := (Real.sqrt_pos.mpr hx).ne'
  rw [div_div, div_mul_cancel₀ _ hs]
  ring

/-- Under RH and for scales at least two, the full level-one principal series is
bounded below by the unit-cutoff main term minus its explicit error.
Nonnegative summands transfer the proved finite lower bound to the full series. -/
theorem fourPole_principal_sum_lower (hRH : RiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    Real.sqrt x * ((484820459 / 528581976 : ℝ) * Real.exp (-(14 / 13))) -
      (26 * x ^ (1 / 4 : ℝ) + 40 / Real.sqrt x) ≤
      (∑' n : ℕ,
        (MellinKernel.summand rationalPoleFourKernel) (1 : DirichletCharacter
        ℂ 1) x n).re := by
  have hx0 : 0 < x := (by norm_num only : (0 : ℝ) < 2).trans_le hx
  have he := fourPole_cutoff_principal_error hRH hx
  have hfinite : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
      ArithmeticFunction.vonMangoldt n * fourScaledWeight x n) =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ((MellinKernel.summand rationalPoleFourKernel) (1 :
          DirichletCharacter ℂ 1) x n).re := by
    apply Finset.sum_congr rfl
    intro n hn
    exact (fourPole_principal_summand_eq hx0 (Nat.ne_of_gt (Finset.mem_Ioc.mp hn).1)).symm
  rw [hfinite] at he
  have hs := MellinKernel.summable_summand rationalPoleFourKernel
    (1 : DirichletCharacter ℂ 1) hx0
  have hsum := Summable.sum_le_tsum (Finset.Ioc 0 ⌊x⌋₊)
    (fun n _ ↦ MellinKernel.principal_summand_re_nonneg rationalPoleFourKernel hx0 n)
    (Complex.reCLM.summable hs)
  have hmap := Complex.reCLM.map_tsum hs
  change (∑' n : ℕ,
    (MellinKernel.summand rationalPoleFourKernel) (1 : DirichletCharacter ℂ
      1) x n).re =
    ∑' n : ℕ,
      ((MellinKernel.summand rationalPoleFourKernel) (1 : DirichletCharacter
      ℂ 1) x n).re at hmap
  rw [← hmap] at hsum
  have hlow := (abs_le.mp he).1
  linarith only [hlow, hsum]

/-- The same explicit lower bound holds for the primitive source of every principal
character. Its summands equal the level-one principal summands term by term. -/
theorem fourPole_primitive_principal_lower (hRH : RiemannHypothesis) {q : ℕ} [NeZero q]
    {x : ℝ} (hx : 2 ≤ x) :
    Real.sqrt x * ((484820459 / 528581976 : ℝ) * Real.exp (-(14 / 13))) -
      (26 * x ^ (1 / 4 : ℝ) + 40 / Real.sqrt x) ≤
      (∑' n : ℕ, (MellinKernel.summand rationalPoleFourKernel)
        (1 : DirichletCharacter ℂ q).primitiveCharacter x n).re := by
  rw [tsum_congr (MellinKernel.principal_primitive_summand_eq_level_one
    rationalPoleFourKernel (q := q) x)]
  exact fourPole_principal_sum_lower hRH hx

end PseudoPrime.LLS.PaperStatements
