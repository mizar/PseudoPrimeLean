/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LeftVerticalGammaBound
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.FarLeftReflection

/-!
# Left-vertical ordinary `L'/L` bound

Specializes the reflection identity to the left-vertical line `s_A(t) := -A - 1/2 + i t`
(`A ≥ 2`), valid for *every* `t` (including `t = 0`, unlike the generic `s.im ≠ 0` version), by
routing through the regular-point completed-to-ordinary bridge and the four `hhalf` pole-avoidance
facts. Combined with the gamma-factor pair bound and the existing right-half-plane `L'/L` bound,
this yields a single explicit-`A` bound on `‖logDeriv (LFunction χ) (s_A(t))‖`.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-! ### The all-`t` reflection identity at the left-vertical line -/

/--
Input/assumptions: `N ≥ 1` (via `[NeZero N]`), `χ` primitive nontrivial quadratic mod `N`,
`A : ℕ` with `2 ≤ A`, `t : ℝ` (any, including `0`).
Conclusion: `logDeriv (LFunction χ) (s_A(t)) = -log N - logDeriv (LFunction χ) (1 - s_A(t)) -
logDeriv (gammaFactor χ) (1 - s_A(t)) - logDeriv (gammaFactor χ) (s_A(t))`, where
`s_A(t) := -A - 1/2 + t i`.
Content: `(1 - s_A(t)).re = A + 3/2 ≥ 1` (from `A ≥ 2`) supplies
`completedLFunction_ne_zero_farLeft_of_isQuadratic`/`completedLFunction_ne_zero_of_one_le_re`
(nonvanishing at both points) and the functional-equation identity
(`DirichletLFunction.completedLFunction_logDeriv_functionalEquation_isQuadratic_at`);
parity dispatch on `χ` supplies
the gamma-factor regularity (`gammaFactor_ne_zero_of_even/odd_of_half_ne_neg_nat` +
`differentiableAt_gammaFactor_of_even/odd_of_half_ne_neg_nat`, fed by the four `leftVertical_*`/
`reflectedLeftVertical_*` pole-avoidance facts) needed by the *regular-point* completed-to-ordinary
bridge
`DirichletLFunction.logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular`
at both `s_A(t)` and
`1 - s_A(t)`; `linear_combination` then closes the algebra exactly as in the generic (`s.im ≠ 0`)
version.
Role: the backbone, valid at `t = 0` (unlike
`logDeriv_dirichletLFunction_reflection_isQuadratic`), turning the far-left `L'/L` bound
into a right-half-plane + gamma-pair bound uniformly over the whole left-vertical line.
-/
theorem logDeriv_dirichletLFunction_reflection_leftVertical_isQuadratic {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hquad : χ.IsQuadratic)
    (A : ℕ) (hA : 2 ≤ A) (t : ℝ) :
    logDeriv (DirichletCharacter.LFunction χ) (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
      -Complex.log N -
        logDeriv (DirichletCharacter.LFunction χ)
          (1 - (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) -
        logDeriv (DirichletCharacter.gammaFactor χ)
          (1 - (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) -
        logDeriv (DirichletCharacter.gammaFactor χ)
          (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
  set s : ℂ := ((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I with hs_def
  have hA' : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hsre : s.re = -(A : ℝ) - 1 / 2 := by
    simp only [hs_def, one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
      Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.add_re, Complex.sub_re, Complex.neg_re,
      Complex.natCast_re, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat,
      div_self_mul_self', Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hs1re : (1 : ℝ) ≤ (1 - s).re := by
    have h1 : (1 - s).re = 1 - s.re := by simp only [Complex.sub_re, Complex.one_re]
    rw [h1, hsre]; linarith
  have hFsne := completedLFunction_ne_zero_farLeft_of_isQuadratic hprimitive hne hquad hs1re
  have hF1sne := completedLFunction_ne_zero_of_one_le_re hne hs1re
  have hFE :=
    completedLFunction_logDeriv_functionalEquation_isQuadratic_at
      hprimitive hne hquad hFsne
  have hFeq :
    logDeriv (DirichletCharacter.completedLFunction χ) s =
      -Complex.log N - logDeriv (DirichletCharacter.completedLFunction χ) (1 - s) := by
    linear_combination -hFE
  rcases χ.even_or_odd with heven | hodd
  · have hΓs :=
      gammaFactor_ne_zero_of_even_of_half_ne_neg_nat
        heven (leftVertical_even_half_ne_neg_nat A t)
    have hdΓs :=
      differentiableAt_gammaFactor_of_even_of_half_ne_neg_nat
        heven (leftVertical_even_half_ne_neg_nat A t)
    have hΓ1s :=
      gammaFactor_ne_zero_of_even_of_half_ne_neg_nat
        heven (reflectedLeftVertical_even_half_ne_neg_nat A hA t)
    have hdΓ1s :=
      differentiableAt_gammaFactor_of_even_of_half_ne_neg_nat
        heven (reflectedLeftVertical_even_half_ne_neg_nat A hA t)
    have hbridge_s :=
      logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular
        hne hFsne hΓs hdΓs
    have hbridge_1s :=
      logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular
        hne hF1sne hΓ1s hdΓ1s
    rw [hbridge_s, hFeq, hbridge_1s]; ring
  · have hΓs :=
      gammaFactor_ne_zero_of_odd_of_half_ne_neg_nat
        hodd (leftVertical_odd_half_ne_neg_nat A t)
    have hdΓs :=
      differentiableAt_gammaFactor_of_odd_of_half_ne_neg_nat
        hodd (leftVertical_odd_half_ne_neg_nat A t)
    have hΓ1s :=
      gammaFactor_ne_zero_of_odd_of_half_ne_neg_nat
        hodd (reflectedLeftVertical_odd_half_ne_neg_nat A hA t)
    have hdΓ1s :=
      differentiableAt_gammaFactor_of_odd_of_half_ne_neg_nat
        hodd (reflectedLeftVertical_odd_half_ne_neg_nat A hA t)
    have hbridge_s :=
      logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular
        hne hFsne hΓs hdΓs
    have hbridge_1s :=
      logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular
        hne hF1sne hΓ1s hdΓ1s
    rw [hbridge_s, hFeq, hbridge_1s]; ring

/-! ### The left-vertical ordinary `L'/L` bound -/

/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial quadratic mod `N`.
Conclusion: there is `D ≥ 0` such that for every `A ≥ 2` and every `t : ℝ`,
`‖logDeriv (LFunction χ) (s_A(t))‖ ≤ D ((A + 5)² + 1 + log(|t| + 2))`, where
`s_A(t) := -A - 1/2 + t i`.
Content: `logDeriv_dirichletLFunction_reflection_leftVertical_isQuadratic` (all-`t`) expresses
`logDeriv (LFunction χ) (s_A(t))` as a sum of four terms: the constant `log N`; the right-half-plane
`logDeriv (LFunction χ) (1 - s_A(t))`, bounded by the `T`-independent constant `M₃` via
`norm_logDeriv_dirichletLFunction_le_of_three_le_re` (since `(1 - s_A(t)).re = A + 3/2 ≥ 3`); and
the gamma-factor pair, bounded by `exists_C_forall_norm_logDeriv_gammaFactor_leftVertical_pair_le`.
The triangle inequality combines all four; `D` absorbs the `A`,`t`-independent constants using
`(A + 5)² + 1 + log(|t| + 2) ≥ 1`.
Role: supplies the pointwise bound used by reciprocal-kernel envelopes and the
`A → ∞` limit of the left-vertical integral.
-/
theorem exists_C_norm_logDeriv_dirichletLFunction_leftVertical_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hquad : χ.IsQuadratic) :
    ∃ D : ℝ,
      0 ≤ D ∧
        ∀ A : ℕ,
          2 ≤ A →
            ∀ t : ℝ,
              ‖logDeriv (DirichletCharacter.LFunction χ)
                    (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
                D * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) := by
  obtain ⟨CΓ, hCΓnn, hCΓ⟩ := exists_C_forall_norm_logDeriv_gammaFactor_leftVertical_pair_le
  set M3 : ℝ := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 : ℝ) with hM3_def
  have hM3nn : 0 ≤ M3 :=
    tsum_nonneg fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  set D : ℝ := ‖Complex.log (N : ℂ)‖ + M3 + CΓ + 5 with hD_def
  have hDnn : 0 ≤ D := by
    have h1 := norm_nonneg (Complex.log (N : ℂ)); linarith
  refine ⟨D, hDnn, fun A hA t => ?_⟩
  have hA' : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  set s : ℂ := ((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I with hs_def
  have hrefl :=
    logDeriv_dirichletLFunction_reflection_leftVertical_isQuadratic hprimitive hne hquad A hA t
  rw [← hs_def] at hrefl
  have hsre : s.re = -(A : ℝ) - 1 / 2 := by
    simp only [hs_def, one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
      Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.add_re, Complex.sub_re, Complex.neg_re,
      Complex.natCast_re, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat,
      div_self_mul_self', Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hs1re3 : (3 : ℝ) ≤ (1 - s).re := by
    have h1 : (1 - s).re = 1 - s.re := by simp only [Complex.sub_re, Complex.one_re]
    rw [h1, hsre]; linarith
  have hLone := norm_logDeriv_dirichletLFunction_le_of_three_le_re χ hs1re3
  have hgam := hCΓ A hA χ t
  rw [← hs_def] at hgam
  have htnn : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hEA1 : (1 : ℝ) ≤ ((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2) := by
    calc
      (1 : ℝ) ≤ ((A : ℝ) + 5) ^ 2 + 1 := by linarith [sq_nonneg ((A : ℝ) + 5)]
      _ ≤ ((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2) := by linarith
  have htri :
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤
      ‖Complex.log (N : ℂ)‖ + ‖logDeriv (DirichletCharacter.LFunction χ) (1 - s)‖ +
        ‖logDeriv (DirichletCharacter.gammaFactor χ) (1 - s)‖ +
        ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ := by
    calc
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ =
          ‖(-Complex.log (N : ℂ) - logDeriv (DirichletCharacter.LFunction χ) (1 - s) -
              logDeriv (DirichletCharacter.gammaFactor χ) (1 - s) -
              logDeriv (DirichletCharacter.gammaFactor χ) s)‖ :=
        by rw [hrefl]
      _ ≤
          ‖(-Complex.log (N : ℂ) - logDeriv (DirichletCharacter.LFunction χ) (1 - s) -
                logDeriv (DirichletCharacter.gammaFactor χ) (1 - s))‖ +
            ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ :=
        by
        have h :=
          norm_sub_le
            (-Complex.log (N : ℂ) - logDeriv (DirichletCharacter.LFunction χ) (1 - s) -
              logDeriv (DirichletCharacter.gammaFactor χ) (1 - s))
            (logDeriv (DirichletCharacter.gammaFactor χ) s)
        simpa only using h
      _ ≤
          (‖(-Complex.log (N : ℂ) - logDeriv (DirichletCharacter.LFunction χ) (1 - s))‖ +
              ‖logDeriv (DirichletCharacter.gammaFactor χ) (1 - s)‖) +
            ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ :=
        by
        gcongr; exact norm_sub_le _ _
      _ ≤
          ((‖(-Complex.log (N : ℂ))‖ + ‖logDeriv (DirichletCharacter.LFunction χ) (1 - s)‖) +
              ‖logDeriv (DirichletCharacter.gammaFactor χ) (1 - s)‖) +
            ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ :=
        by
        gcongr; exact norm_sub_le _ _
      _ =
          ‖Complex.log (N : ℂ)‖ + ‖logDeriv (DirichletCharacter.LFunction χ) (1 - s)‖ +
            ‖logDeriv (DirichletCharacter.gammaFactor χ) (1 - s)‖ +
            ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ :=
        by rw [norm_neg]
  calc
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤
        ‖Complex.log (N : ℂ)‖ + ‖logDeriv (DirichletCharacter.LFunction χ) (1 - s)‖ +
          ‖logDeriv (DirichletCharacter.gammaFactor χ) (1 - s)‖ +
          ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ :=
      htri
    _ ≤ ‖Complex.log (N : ℂ)‖ + M3 + CΓ * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) := by
      have hgam' :
        ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ +
            ‖logDeriv (DirichletCharacter.gammaFactor χ) (1 - s)‖ ≤
          CΓ * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) :=
        hgam
      linarith [hLone, hgam']
    _ ≤ D * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) := by
      rw [hD_def]
      have hBnn : (0 : ℝ) ≤ ((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2) :=
        le_trans (by norm_num only) hEA1
      have hLMnn : (0 : ℝ) ≤ ‖Complex.log (N : ℂ)‖ + M3 := add_nonneg (norm_nonneg _) hM3nn
      have hLM :
        ‖Complex.log (N : ℂ)‖ + M3 ≤
          (‖Complex.log (N : ℂ)‖ + M3) * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) := by
        calc
          ‖Complex.log (N : ℂ)‖ + M3 = (‖Complex.log (N : ℂ)‖ + M3) * 1 := by ring
          _ ≤ (‖Complex.log (N : ℂ)‖ + M3) * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) :=
            mul_le_mul_of_nonneg_left hEA1 hLMnn
      calc
        ‖Complex.log (N : ℂ)‖ + M3 + CΓ * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) =
            CΓ * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) + (‖Complex.log (N : ℂ)‖ + M3) :=
          by ring
        _ ≤
            CΓ * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) +
              (‖Complex.log (N : ℂ)‖ + M3) * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) :=
          (by
            convert add_le_add_right hLM (CΓ * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2))) using
                1)
        _ = (‖Complex.log (N : ℂ)‖ + M3 + CΓ) * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) := by
          ring
        _ ≤ (‖Complex.log (N : ℂ)‖ + M3 + CΓ + 5) * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) :=
          by
          apply mul_le_mul_of_nonneg_right _ hBnn
          linarith

theorem exists_C_norm_logDeriv_dirichletLFunction_leftVertical_le_general {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    ∃ D : ℝ,
      0 ≤ D ∧
        ∀ A : ℕ,
          2 ≤ A →
            ∀ t : ℝ,
              ‖logDeriv (DirichletCharacter.LFunction χ)
                    (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
                D * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) := by
  obtain ⟨CΓ, hCΓnn, hCΓ⟩ := exists_C_forall_norm_logDeriv_gammaFactor_leftVertical_pair_le
  set M3 : ℝ := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 : ℝ)
  have hM3nn : 0 ≤ M3 :=
    tsum_nonneg fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  set D : ℝ := ‖Complex.log (N : ℂ)‖ + M3 + CΓ + 5
  have hDnn : 0 ≤ D := by
    have h1 := norm_nonneg (Complex.log (N : ℂ)); linarith
  refine ⟨D, hDnn, fun A hA t => ?_⟩
  have hA' : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  set s : ℂ := ((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  have hrefl0 := logDeriv_dirichletLFunction_reflection_leftVertical hprimitive hne hinv A hA t
  have hrefl := by
    simpa only [one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
      Complex.ofReal_inv, Complex.ofReal_ofNat] using hrefl0
  have hsre : s.re = -(A : ℝ) - 1 / 2 := by
    simp only [one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
      Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.add_re, Complex.sub_re, Complex.neg_re,
      Complex.natCast_re, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat,
      div_self_mul_self', Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, s]
  have h1sre : (3 : ℝ) ≤ (1 - s).re := by
    have h1 : (1 - s).re = 1 - s.re := by simp only [Complex.sub_re, Complex.one_re]
    rw [h1, hsre]
    linarith
  have hLone := norm_logDeriv_dirichletLFunction_le_of_three_le_re χ⁻¹ h1sre
  have hgam := hCΓ A hA χ t
  have htnn : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hEA1 : (1 : ℝ) ≤ ((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2) := by
    calc
      (1 : ℝ) ≤ ((A : ℝ) + 5) ^ 2 + 1 := by linarith [sq_nonneg ((A : ℝ) + 5)]
      _ ≤ ((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2) := by linarith
  have htri :
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤
      ‖Complex.log (N : ℂ)‖ + ‖logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s)‖ +
        ‖logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s)‖ +
        ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ := by
    have hrewrite :
      logDeriv (DirichletCharacter.LFunction χ) s =
        -Complex.log N - logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s) -
          logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s) -
          logDeriv (DirichletCharacter.gammaFactor χ) s := by
      simpa only [s, one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
        Complex.ofReal_inv, Complex.ofReal_ofNat] using hrefl
    rw [hrewrite]
    have hABC :=
      norm_sub_le
        (-Complex.log (N : ℂ) - logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s) -
          logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s))
        (logDeriv (DirichletCharacter.gammaFactor χ) s)
    have hAB :=
      norm_sub_le (-Complex.log (N : ℂ) - logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s))
        (logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s))
    have hA :=
      norm_sub_le (-Complex.log (N : ℂ)) (logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s))
    calc
      _ ≤
          ‖-Complex.log (N : ℂ) - logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s) -
                logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s)‖ +
            ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ :=
        hABC
      _ ≤
          (‖-Complex.log (N : ℂ) - logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s)‖ +
              ‖logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s)‖) +
            ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ :=
        by nlinarith [hAB]
      _ ≤
          ((‖-Complex.log (N : ℂ)‖ + ‖logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s)‖) +
              ‖logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s)‖) +
            ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ :=
        by nlinarith [hA]
      _ = _ := by rw [norm_neg]
  calc
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ ≤
        ‖Complex.log (N : ℂ)‖ + ‖logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s)‖ +
          ‖logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s)‖ +
          ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ :=
      htri
    _ ≤ ‖Complex.log (N : ℂ)‖ + M3 + CΓ * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) := by
      have hgam' := hgam
      have hgam'' :
        ‖logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s)‖ +
            ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ ≤
          CΓ * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) := by
        have heq :=
          DirichletCharacter.gammaFactor_inv_eq
            χ
        have hgf : DirichletCharacter.gammaFactor χ⁻¹ = DirichletCharacter.gammaFactor χ := by
          funext z
          exact heq z
        have hld :
          logDeriv (DirichletCharacter.gammaFactor χ⁻¹) =
            logDeriv (DirichletCharacter.gammaFactor χ) := by
          rw [hgf]
        rw [hld]
        simpa only [add_comm, add_assoc, s] using hgam'
      linarith [hLone, hgam'']
    _ ≤ D * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) := by
      dsimp only [D]
      have hBnn : (0 : ℝ) ≤ ((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2) :=
        le_trans (by norm_num only) hEA1
      have hLMnn : (0 : ℝ) ≤ ‖Complex.log (N : ℂ)‖ + M3 := add_nonneg (norm_nonneg _) hM3nn
      have hLM :
        ‖Complex.log (N : ℂ)‖ + M3 ≤
          (‖Complex.log (N : ℂ)‖ + M3) * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) := by
        calc
          ‖Complex.log (N : ℂ)‖ + M3 = (‖Complex.log (N : ℂ)‖ + M3) * 1 := by ring
          _ ≤ (‖Complex.log (N : ℂ)‖ + M3) * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) :=
            mul_le_mul_of_nonneg_left hEA1 hLMnn
      calc
        ‖Complex.log (N : ℂ)‖ + M3 + CΓ * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) =
            CΓ * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) + (‖Complex.log (N : ℂ)‖ + M3) :=
          by ring
        _ ≤
            CΓ * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) +
              (‖Complex.log (N : ℂ)‖ + M3) * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) :=
          (by
            convert add_le_add_right hLM (CΓ * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2))) using
                1)
        _ = (‖Complex.log (N : ℂ)‖ + M3 + CΓ) * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) := by
          ring
        _ ≤ (‖Complex.log (N : ℂ)‖ + M3 + CΓ + 5) * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) :=
          by
          apply mul_le_mul_of_nonneg_right _ hBnn
          linarith

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
