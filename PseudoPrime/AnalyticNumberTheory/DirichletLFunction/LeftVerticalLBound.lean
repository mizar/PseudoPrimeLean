/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LeftVerticalGammaBound
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.FarLeftReflection

/-!
# Left-vertical ordinary `L'/L` bound

Specializes the reflection identity to the left-vertical line `s_A(t) := -A - 1/2 + i t`
(`A ≥ 2`), valid for *every* `t` (including `t = 0`, unlike the generic `s.im ≠ 0` version), by
routing through the regular-point completed-to-ordinary bridge and the four `hhalf` pole-avoidance
facts. Combined with the gamma-factor pair bound and the existing right-half-plane `L'/L` bound,
this yields a single explicit-`A` bound on `‖logDeriv (LFunction χ) (s_A(t))‖`.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-! ### The all-`t` reflection identity at the left-vertical line -/

/-! ### The left-vertical ordinary `L'/L` bound -/

/-- For a primitive nontrivial character with nontrivial inverse, choose `D ≥ 0` independently
of `A` and `t` so that, for `A ≥ 2`, the ordinary logarithmic derivative on
`-A-1/2+it` is bounded by `D * ((A+5)² + 1 + log(|t|+2))`.
Reflect to the inverse character in the Euler half-plane, apply the von Mangoldt series bound,
and combine the two gamma-factor bounds using parity invariance under inversion.
This supplies whole-line contour envelopes for general primitive characters without GRH. -/
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
    have h1 := norm_nonneg (Complex.log (N : ℂ))
    linarith only [h1, hM3nn, hCΓnn]
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
    linarith only [hA']
  have hLone := norm_logDeriv_dirichletLFunction_le_of_three_le_re χ⁻¹ h1sre
  have hgam := hCΓ A hA χ t
  have htnn : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith only [abs_nonneg t])
  have hEA1 : (1 : ℝ) ≤ ((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2) := by
    calc
      (1 : ℝ) ≤ ((A : ℝ) + 5) ^ 2 + 1 := by linarith only [sq_nonneg ((A : ℝ) + 5)]
      _ ≤ ((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2) := by linarith only [htnn]
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
        by nlinarith only [hAB]
      _ ≤
          ((‖-Complex.log (N : ℂ)‖ + ‖logDeriv (DirichletCharacter.LFunction χ⁻¹) (1 - s)‖) +
              ‖logDeriv (DirichletCharacter.gammaFactor χ⁻¹) (1 - s)‖) +
            ‖logDeriv (DirichletCharacter.gammaFactor χ) s‖ :=
        by nlinarith only [hA]
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
        have heq := DirichletCharacter.gammaFactor_inv_eq χ
        have hgf : DirichletCharacter.gammaFactor χ⁻¹ = DirichletCharacter.gammaFactor χ := by
          funext z
          exact heq z
        have hld :
          logDeriv (DirichletCharacter.gammaFactor χ⁻¹) =
            logDeriv (DirichletCharacter.gammaFactor χ) := by
          rw [hgf]
        rw [hld]
        simpa only [add_comm, add_assoc, s] using hgam'
      linarith only [hLone, hgam'']
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
          linarith only [hDnn]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
