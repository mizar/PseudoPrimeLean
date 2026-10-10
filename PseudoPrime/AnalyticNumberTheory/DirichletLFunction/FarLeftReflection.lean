/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.MulChar.Basic
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.Basic
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveFunctionalEquation
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorGrowth
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorLogDeriv
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LeftVerticalGammaBound
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.GrowthBounds

/-!
# Far-left reflection and bounds for the ordinary logarithmic derivative

The functional equation reflects a primitive nontrivial character to its inverse in the right
half-plane. For quadratic characters the inverse is the character itself. Absolute convergence
of the Mangoldt series and gamma-factor strip bounds give `O_A(|T| + 1)` on
`-A - 1/2 ≤ Re s ≤ -2`, for `|T| ≥ 1`. The all-height reflection identity on
`Re s = -A - 1/2` also handles height zero by avoiding gamma poles.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-! ### Far-left nonvanishing of the completed `L`-function -/

/-! ### A uniform bound on the ordinary `L'/L` on the right half-plane `Re ≥ 3` -/

/--
Input/assumptions: a character `χ` (any modulus), and `s : ℂ` with `3 ≤ s.re`.
Conclusion: `‖logDeriv (LFunction χ) s‖ ≤ M₃ := ∑' n, Λ(n) / n ^ 3`.
Content: `DirichletLFunction.norm_neg_deriv_div_dirichletLFunction_le_vonMangoldt_tsum` (existing,
`‖logDeriv L(s)‖ ≤
∑' n, Λ(n) / n ^ (s.re)`) combined with `RiemannZeta.tsum_vonMangoldt_div_rpow_antitone` (existing,
χ-free
monotonicity of the von Mangoldt Dirichlet series in the exponent) to replace `s.re ≥ 3` by the
fixed value `3`.
-/
theorem norm_logDeriv_dirichletLFunction_le_of_three_le_re {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 3 ≤ s.re) :
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 : ℝ) := by
  have h1 :=
    norm_neg_deriv_div_dirichletLFunction_le_vonMangoldt_tsum χ (τ := s.re)
      (lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 3) hs) s.im
  have hseq : (s.re : ℂ) + (s.im : ℂ) * Complex.I = s := by
    apply Complex.ext <;> simp only [Complex.re_add_im]
  rw [hseq] at h1
  have hlogDeriv_eq :
    ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ =
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ := by
    rw [neg_div, norm_neg, logDeriv_apply]
  rw [hlogDeriv_eq] at h1
  exact h1.trans (RiemannZeta.tsum_vonMangoldt_div_rpow_antitone (by norm_num only) hs)

/-! ### Far-left reflection for a character and its inverse -/

/--
For a primitive character with nontrivial inverse and `Re(1-s) ≥ 1`, the
completed L-function is nonzero at `s`. Reflect by the functional equation;
the level and root-number factors are nonzero, and the inverse-character
L-function is nonzero on the right. This supports far-left logarithmic derivatives.
-/
theorem completedLFunction_ne_zero_farLeft {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprimitive : χ.IsPrimitive) (_hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {s : ℂ} (hs : 1 ≤ (1 - s).re) :
    DirichletCharacter.completedLFunction χ s ≠ 0 := by
  intro hFs
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hrootne : DirichletCharacter.rootNumber χ ≠ 0 :=
    dirichletCharacter_rootNumber_ne_zero_of_isPrimitive hprimitive
  have hfeq := dirichletCompletedLFunction_one_sub_of_isPrimitive hprimitive (1 - s)
  rw [show (1 : ℂ) - (1 - s) = s from by ring, hFs] at hfeq
  have hfactne : (N : ℂ) ^ ((1 - s) - 1 / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hNne)
  have hgroupne : (N : ℂ) ^ ((1 - s) - 1 / 2) * DirichletCharacter.rootNumber χ ≠ 0 :=
    mul_ne_zero hfactne hrootne
  have hF1sne0 : DirichletCharacter.completedLFunction χ⁻¹ (1 - s) = 0 := by
    rcases mul_eq_zero.mp hfeq.symm with h | h
    · exact absurd h hgroupne
    · exact h
  exact completedLFunction_ne_zero_of_one_le_re hinv hs hF1sne0

/--
For a primitive nontrivial character with nontrivial inverse, `Re(1-s) ≥ 1`,
and `Im s ≠ 0`, express the ordinary L-function logarithmic derivative through
the reflected inverse-character derivative and the two gamma-factor derivatives.
Combine the completed functional equation with the completed-to-ordinary bridge;
this identity supplies far-left contour bounds.
-/
theorem logDeriv_dirichletLFunction_reflection {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {s : ℂ} (hs : 1 ≤ (1 - s).re)
    (hsim : s.im ≠ 0) :
    logDeriv (DirichletCharacter.LFunction χ) s =
      -Complex.log N - logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s) -
        logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s) -
        logDeriv (DirichletCharacter.gammaFactor χ) s := by
  have hFsne : DirichletCharacter.completedLFunction χ s ≠ 0 :=
    completedLFunction_ne_zero_farLeft hprimitive hne hinv hs
  have hF1sne : DirichletCharacter.completedLFunction χ⁻¹ (1 - s) ≠ 0 :=
    completedLFunction_ne_zero_of_one_le_re hinv hs
  have h1sim_ne : (1 - s).im ≠ 0 := by
    rw [Complex.sub_im, Complex.one_im, zero_sub]
    exact neg_ne_zero.mpr hsim
  have hFE := completedLFunction_logDeriv_functionalEquation_at hprimitive hne (s := 1 - s) hF1sne
  rw [show (1 : ℂ) - (1 - s) = s from by ring] at hFE
  have hbridge_s := logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor hne hFsne hsim
  have hbridge_1s := logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor hinv hF1sne h1sim_ne
  have hFeq :
    logDeriv (DirichletCharacter.completedLFunction χ) s =
      -Complex.log N - logDeriv (DirichletCharacter.completedLFunction χ⁻¹) (1 - s) := by
    linear_combination -hFE
  rw [hbridge_s, hFeq, hbridge_1s]
  ring

/-- For a primitive nontrivial character with nontrivial inverse, `A ≥ 2`, and any real
height `t`, reflect the ordinary logarithmic derivative at `s = -A-1/2 + it` to the
inverse character at `1-s`, with the conductor and both gamma logarithmic derivatives.
The functional equation and regular-point bridges apply because parity-specific gamma
arguments avoid all poles, including at `t = 0`. This supplies the all-height left-line bound. -/
theorem logDeriv_dirichletLFunction_reflection_leftVertical {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (A : ℕ)
    (hA : 2 ≤ A) (t : ℝ) :
    logDeriv (DirichletCharacter.LFunction χ) (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
      -Complex.log N -
        logDeriv (DirichletCharacter.LFunction χ⁻¹)
          (1 - (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) -
        logDeriv (DirichletCharacter.gammaFactor χ⁻¹)
          (1 - (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) -
        logDeriv (DirichletCharacter.gammaFactor χ)
          (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
  set s : ℂ := ((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I with hs_def
  have hA' : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hsre : s.re = -(A : ℝ) - 1 / 2 := by
    simp only [hs_def, one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
      Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.add_re, Complex.sub_re, Complex.neg_re,
      Complex.natCast_re, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat,
      div_self_mul_self', Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im, mul_zero, mul_one, sub_self, add_zero]
  have hs1re : (1 : ℝ) ≤ (1 - s).re := by
    have h1 : (1 - s).re = 1 - s.re := by simp only [Complex.sub_re, Complex.one_re]
    rw [h1, hsre]
    linarith only [hA']
  have hFsne := completedLFunction_ne_zero_farLeft hprimitive hne hinv hs1re
  have hF1sne := completedLFunction_ne_zero_of_one_le_re hinv hs1re
  have hFE := completedLFunction_logDeriv_functionalEquation_at hprimitive hne (s := 1 - s) hF1sne
  rw [show (1 : ℂ) - (1 - s) = s by ring] at hFE
  have hFeq :
    logDeriv (DirichletCharacter.completedLFunction χ) s =
      -Complex.log N - logDeriv (DirichletCharacter.completedLFunction χ⁻¹) (1 - s) := by
    linear_combination -hFE
  rcases χ.even_or_odd with heven | hodd
  · have hΓs :=
      gammaFactor_ne_zero_of_even_of_half_ne_neg_nat heven (leftVertical_even_half_ne_neg_nat A t)
    have hdΓs :=
      differentiableAt_gammaFactor_of_even_of_half_ne_neg_nat heven
        (leftVertical_even_half_ne_neg_nat A t)
    rcases χ⁻¹.even_or_odd with heven' | hodd'
    · have hΓ1s :=
        gammaFactor_ne_zero_of_even_of_half_ne_neg_nat heven'
          (reflectedLeftVertical_even_half_ne_neg_nat A hA t)
      have hdΓ1s :=
        differentiableAt_gammaFactor_of_even_of_half_ne_neg_nat heven'
          (reflectedLeftVertical_even_half_ne_neg_nat A hA t)
      have hbridge_s :=
        logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne hFsne hΓs hdΓs
      have hbridge_1s :=
        logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hinv hF1sne hΓ1s hdΓ1s
      rw [hbridge_s, hFeq, hbridge_1s]
      ring
    · have hΓ1s :=
        gammaFactor_ne_zero_of_odd_of_half_ne_neg_nat hodd'
          (reflectedLeftVertical_odd_half_ne_neg_nat A hA t)
      have hdΓ1s :=
        differentiableAt_gammaFactor_of_odd_of_half_ne_neg_nat hodd'
          (reflectedLeftVertical_odd_half_ne_neg_nat A hA t)
      have hbridge_s :=
        logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne hFsne hΓs hdΓs
      have hbridge_1s :=
        logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hinv hF1sne hΓ1s hdΓ1s
      rw [hbridge_s, hFeq, hbridge_1s]
      ring
  · have hΓs :=
      gammaFactor_ne_zero_of_odd_of_half_ne_neg_nat hodd (leftVertical_odd_half_ne_neg_nat A t)
    have hdΓs :=
      differentiableAt_gammaFactor_of_odd_of_half_ne_neg_nat hodd
        (leftVertical_odd_half_ne_neg_nat A t)
    rcases χ⁻¹.even_or_odd with heven' | hodd'
    · have hΓ1s :=
        gammaFactor_ne_zero_of_even_of_half_ne_neg_nat heven'
          (reflectedLeftVertical_even_half_ne_neg_nat A hA t)
      have hdΓ1s :=
        differentiableAt_gammaFactor_of_even_of_half_ne_neg_nat heven'
          (reflectedLeftVertical_even_half_ne_neg_nat A hA t)
      have hbridge_s :=
        logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne hFsne hΓs hdΓs
      have hbridge_1s :=
        logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hinv hF1sne hΓ1s hdΓ1s
      rw [hbridge_s, hFeq, hbridge_1s]
      ring
    · have hΓ1s :=
        gammaFactor_ne_zero_of_odd_of_half_ne_neg_nat hodd'
          (reflectedLeftVertical_odd_half_ne_neg_nat A hA t)
      have hdΓ1s :=
        differentiableAt_gammaFactor_of_odd_of_half_ne_neg_nat hodd'
          (reflectedLeftVertical_odd_half_ne_neg_nat A hA t)
      have hbridge_s :=
        logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne hFsne hΓs hdΓs
      have hbridge_1s :=
        logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hinv hF1sne hΓ1s hdΓ1s
      rw [hbridge_s, hFeq, hbridge_1s]
      ring

/--
For a primitive nontrivial character with nontrivial inverse and fixed `A`,
there is `D ≥ 0` bounding the ordinary logarithmic derivative by `D * (|T|+1)`
on `-A-1/2 ≤ σ ≤ -2`, `|T| ≥ 1`. Reflect to the inverse character in the
right half-plane and bound both gamma terms. This controls horizontal far-left edges.
-/
theorem exists_norm_logDeriv_dirichletLFunction_farLeft_le_general (A : ℕ) {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    ∃ D : ℝ,
      0 ≤ D ∧
        ∀ σ T : ℝ,
          -(A : ℝ) - 1 / 2 ≤ σ →
            σ ≤ -2 →
            1 ≤ |T| →
            ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤
              D * (|T| + 1) := by
  obtain ⟨CΓ, hCΓnonneg, hCΓ⟩ := exists_norm_logDeriv_gammaFactor_fixed_strip_le A
  set M3 : ℝ := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 : ℝ) with hM3_def
  have hM3nonneg : 0 ≤ M3 :=
    tsum_nonneg fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  set D : ℝ := ‖Complex.log (N : ℂ)‖ + M3 + 2 * CΓ with hD_def
  have hDnonneg : 0 ≤ D := by
    rw [hD_def]
    have := norm_nonneg (Complex.log (N : ℂ))
    linarith only [this, hM3nonneg, hCΓnonneg]
  refine ⟨D, hDnonneg, fun σ T hσ1 hσ2 hT => ?_⟩
  set s : ℂ := (σ : ℂ) + (T : ℂ) * Complex.I with hs_def
  have hsim : s.im = T := by
    simp only [hs_def, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  have hsim_ne : s.im ≠ 0 := by
    rw [hsim]
    intro h
    rw [h] at hT
    norm_num only at hT
  have hAnn : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
  have h1s_re_eq : (1 - s).re = 1 - σ := by
    simp only [hs_def, Complex.sub_re, Complex.one_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
      add_zero]
  have h1s_im_eq : (1 - s).im = -T := by
    simp only [hs_def, Complex.sub_im, Complex.one_im, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero,
      zero_add, zero_sub]
  have h1s_re1 : 1 ≤ (1 - s).re := by
    rw [h1s_re_eq]
    linarith only [hσ2]
  have hrefl := logDeriv_dirichletLFunction_reflection hprimitive hne hinv h1s_re1 hsim_ne
  have h1s_im_abs : |(1 - s).im| = |T| := by rw [h1s_im_eq, abs_neg]
  have h1s_re_le : (1 - s).re ≤ (A : ℝ) + 3 / 2 := by
    rw [h1s_re_eq]
    linarith only [hσ1]
  have h1s_re_ge : -(A : ℝ) - 1 / 2 ≤ (1 - s).re := by
    rw [h1s_re_eq]
    linarith only [hσ2, hAnn]
  have hgam1s : ‖logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s)‖ ≤ CΓ * (|T| + 1) := by
    have h :=
      hCΓ χ⁻¹ (1 - s).re (1 - s).im h1s_re_ge h1s_re_le
        (by
          rw [h1s_im_abs]
          exact hT)
    have hform : (((1 - s).re : ℂ) + ((1 - s).im : ℂ) * Complex.I) = 1 - s := by
      apply Complex.ext <;>
        simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_sub, Complex.ofReal_one,
          Complex.sub_im, Complex.one_im, zero_sub, Complex.ofReal_neg, neg_mul, Complex.add_re,
          Complex.ofReal_re, Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_self, neg_zero, add_zero, Complex.add_im,
          Complex.mul_im, zero_add]
    rw [hform, h1s_im_abs] at h
    exact h
  have hgams : ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ ≤ CΓ * (|T| + 1) := by
    have hσ2' : σ ≤ (A : ℝ) + 3 / 2 := by linarith only [h1s_re_eq, h1s_re_ge]
    have h := hCΓ χ σ T hσ1 hσ2' hT
    rwa [← hs_def] at h
  have hLone : ‖logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s)‖ ≤ M3 :=
    norm_logDeriv_dirichletLFunction_le_of_three_le_re χ⁻¹
      (by
        rw [h1s_re_eq]
        linarith only [hσ2])
  have htri :
    ‖(-Complex.log (N : ℂ) - logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s) -
          logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s) -
          logDeriv (DirichletCharacter.gammaFactor χ) s)‖ ≤
      ‖Complex.log (N : ℂ)‖ + ‖logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s)‖ +
        ‖logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s)‖ +
        ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ := by
    calc
      ‖(-Complex.log (N : ℂ) - logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s) -
              logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s) -
              logDeriv (DirichletCharacter.gammaFactor χ) s)‖ ≤
          ‖(-Complex.log (N : ℂ) - logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s) -
                logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s))‖ +
            ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ :=
        norm_sub_le _ _
      _ ≤
          (‖(-Complex.log (N : ℂ) - logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s))‖ +
              ‖logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s)‖) +
            ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ :=
        by
        gcongr
        exact norm_sub_le _ _
      _ ≤
          ((‖(-Complex.log (N : ℂ))‖ + ‖logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s)‖) +
              ‖logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s)‖) +
            ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ :=
        by
        gcongr
        exact norm_sub_le _ _
      _ =
          ‖Complex.log (N : ℂ)‖ + ‖logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s)‖ +
            ‖logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s)‖ +
            ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ :=
        by rw [norm_neg]
  rw [hrefl]
  have hTpos : (0 : ℝ) ≤ |T| := abs_nonneg T
  calc
    ‖(-Complex.log (N : ℂ) - logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s) -
            logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s) -
            logDeriv (DirichletCharacter.gammaFactor χ) s)‖ ≤
        ‖Complex.log (N : ℂ)‖ + ‖logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s)‖ +
          ‖logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s)‖ +
          ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ :=
      htri
    _ ≤ ‖Complex.log (N : ℂ)‖ + M3 + CΓ * (|T| + 1) + CΓ * (|T| + 1) := by gcongr
    _ ≤ D * (|T| + 1) := by
      rw [hD_def]
      nlinarith only [norm_nonneg (Complex.log (N : ℂ)), hM3nonneg, hCΓnonneg, hTpos]

/-! ### The ordinary `L'/L` far-left reflection identity -/

/-! ### The far-left ordinary `L'/L` bound, `O_A(|T| + 1)` -/

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
