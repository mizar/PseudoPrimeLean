/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RationalPoleWideKernel
public import PseudoPrime.LLS.RationalPoleLeftBounds
public import PseudoPrime.LLS.MellinKernelExplicitFormula
public import PseudoPrime.LLS.RationalPoleZeroMass

/-! Explicit finite remainder for the fourth-order kernel. -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The possible kernel-pole residue of the widened fourth-order kernel is zero
for every complex function and real scale. The regularization vanishes at -1/2.
This removes the endpoint residue from the completed explicit formula exactly. -/
theorem fourWide_pole_residue_zero (F : ℂ → ℂ) (x : ℝ) :
    MellinKernel.weightedResidue fourWideKernel F x (-1 / 2) = 0 := by
  simp only [MellinKernel.weightedResidue]
  change
    -logDeriv F (-1 / 2) *
        (((-1 / 2 : ℂ) + 1 / 2) * rationalPoleFourKernel.function (-1 / 2) * (x : ℂ) ^ (-1 / 2)) =
      0
  rw [neg_div, neg_add_cancel, zero_mul, zero_mul, mul_zero]

/-- Under GRH, primitive nonprincipal data of modulus at least two and scale x>=1
satisfy an explicit fourth-order smoothed-sum formula with error norm at most
3+(24 log q+793)x^(-3/4). Use left line -3/4 and right line 5/8 in the exact contour
identity, remove the zero kernel-pole residue, and shift gamma to the central line.
The proved gamma and left-integral bounds control the remaining two terms. -/
theorem fourWide_summand_error {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    ‖(∑' n : ℕ, (MellinKernel.summand fourWideKernel) χ x n) +
          (∑' ρ : ℂ, (MellinKernel.oscillatingZeroTerm fourWideKernel) χ x ρ)‖ ≤
      3 + (24 * Real.log q + 793) * x ^ (-3 / 4 : ℝ) := by
  have he :=
    MellinKernel.tsum_summand_eq_completed_residue_formula fourWideKernel hq hGRH hp hne hinv (a :=
      (-3 / 4 : ℝ)) (b := (5 / 8 : ℝ)) (by norm_num only)
      (by
        change (-1 / 2 - 27 / 100 : ℝ) < -3 / 4; norm_num only)
      (by
        change (5 / 8 : ℝ) ≤ 1 / 2 + 27 / 100; norm_num only)
      (by norm_num only) (by norm_num only) hx (by norm_num only) (by norm_num only)
  dsimp only at he
  rw [fourWide_pole_residue_zero] at he
  have hg :=
    MellinKernel.gammaIntegral_eq_central fourWideKernel χ (b := (5 / 8 : ℝ)) (by norm_num only)
      (by
        change (5 / 8 : ℝ) ≤ 1 / 2 + 27 / 100; norm_num only)
      (by norm_num only) hx
  rw [hg] at he
  have hleft := fourContour_left_signed_bound hp hne hinv (zero_lt_one.trans_le hx)
  have hgamma := fourContour_gammaIntegral_lt_three χ (zero_lt_one.trans_le hx)
  let L :=
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        -logDeriv χ.completedLFunction (((-3 / 4 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
          (fourWideKernel.function (((-3 / 4 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-3 / 4 : ℝ) : ℂ) + Complex.I * t)))
  let G :=
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
          (fourWideKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)))
  have hs :
    (∑' n : ℕ, (MellinKernel.summand fourWideKernel) χ x n) +
        (∑' ρ : ℂ, (MellinKernel.oscillatingZeroTerm fourWideKernel) χ x ρ) =
      L + G := by
    dsimp only [L, G]
    rw [he]
    ring
  rw [hs]
  change ‖L‖ ≤ (24 * Real.log q + 793) * x ^ (-3 / 4 : ℝ) at hleft
  change ‖G‖ < 3 at hgamma
  exact (norm_add_le L G).trans (by linarith only [hleft, hgamma])

/-- The original fourth-order kernel obeys the same explicit smoothed-sum error bound.
The wider kernel has the identical function and transform, hence identical summands
and oscillating zero terms. This connects the contour construction to the existing
Poisson-majorant and prime-bound APIs without changing their kernel. -/
theorem rationalPole_four_explicit_error {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    ‖(∑' n : ℕ, (MellinKernel.summand rationalPoleFourKernel) χ x n) +
          (∑' ρ : ℂ, (MellinKernel.oscillatingZeroTerm rationalPoleFourKernel) χ x ρ)‖ ≤
      3 + (24 * Real.log q + 793) * x ^ (-3 / 4 : ℝ) := by
  exact fourWide_summand_error hq hGRH hp hne hinv hx

/-- Under primitive nonprincipal GRH data, scale at least one and arbitrary finite Euler
prefixes, the absolute real smoothed sum is bounded by the retained two-node Euler budget
plus 3+(24 log q+793)x^(-3/4). Identify each oscillatory zero norm with its nonnegative
divisor-weighted kernel norm, apply the Poisson majorant, then the explicit remainder.
This is the finite nonprincipal arithmetic interface; principal and local costs stay separate. -/
theorem rationalPole_four_smoothed_le {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) (A B : Finset ℕ) :
    |(∑' n : ℕ, (MellinKernel.summand rationalPoleFourKernel) χ x n).re| ≤
      rationalPoleFourEulerBudget χ A B + 3 + (24 * Real.log q + 793) * x ^ (-3 / 4 : ℝ) := by
  have hx0 := zero_lt_one.trans_le hx
  have hz := rationalPole_four_zeroMass_le hq (hGRH q χ hp) hp hne hinv (14 / 25) A B
  have he (ρ : ℂ) :
    ‖(MellinKernel.oscillatingZeroTerm rationalPoleFourKernel) χ x ρ‖ =
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        ‖Analysis.rationalPoleFunction 2 (13 / 25) (14 / 25) (Complex.I * ρ.im)‖ := by
    have ha : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
      (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
    have hd : (0 : ℝ) ≤ MeromorphicOn.divisor χ.completedLFunction Set.univ ρ :=
      Int.cast_nonneg (MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ)
    rw [MellinKernel.norm_oscillatingZeroTerm _ χ hx0 ρ, MellinKernel.kernelZeroTerm, norm_mul,
      Complex.norm_intCast, abs_of_nonneg hd]
    rfl
  have hzero :
    ‖∑' ρ : ℂ, (MellinKernel.oscillatingZeroTerm rationalPoleFourKernel) χ x ρ‖ ≤
      rationalPoleFourEulerBudget χ A B := by
    calc
      _ ≤ ∑' ρ : ℂ, ‖(MellinKernel.oscillatingZeroTerm rationalPoleFourKernel) χ x ρ‖ :=
        norm_tsum_le_tsum_norm
          (MellinKernel.summable_oscillatingZeroTerm _ hq hGRH hp hne hinv hx0).norm
      _ = _ := tsum_congr he
      _ ≤ _ := hz.2
  have herr := rationalPole_four_explicit_error hq hGRH hp hne hinv hx
  have hs :=
    norm_sub_le
      ((∑' n : ℕ, (MellinKernel.summand rationalPoleFourKernel) χ x n) +
        (∑' ρ : ℂ, (MellinKernel.oscillatingZeroTerm rationalPoleFourKernel) χ x ρ))
      (∑' ρ : ℂ, (MellinKernel.oscillatingZeroTerm rationalPoleFourKernel) χ x ρ)
  rw [add_sub_cancel_right] at hs
  exact (Complex.abs_re_le_norm _).trans (hs.trans (by linarith only [herr, hzero]))

end PseudoPrime.LLS.PaperStatements
