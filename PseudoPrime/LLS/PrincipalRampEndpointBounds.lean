/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaQuadraticArithmetic
public import PseudoPrime.LLS.MellinKernelBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ScaledMangoldtMonotonicity

/-! # Endpoint bounds for the actual principal-ramp difference -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The unnormalized full exponential Mangoldt mass at a real scale.
At positive scale the series converges and equals the actual principal Gamma series
multiplied by the square root. It is used for endpoint comparisons without normalization loss. -/
noncomputable def principalExponentialMass (x : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n

/-- At positive scale, each principal Gamma term times sqrt(x) is its
exponential Mangoldt atom. Use the quadratic principal-character identity and cancel sqrt(x). -/
theorem gamma_principal_scaled_term {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re * Real.sqrt x =
      Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n := by
  have h1 : (1 : DirichletCharacter ℂ 1).IsQuadratic := fun z ↦
    Or.inr (Or.inl (MulChar.one_apply (isUnit_of_subsingleton z)))
  rw [PaperStatements.gamma_quadratic_summand_re_eq_exponential_all _ h1 hx]
  simp only [MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), Complex.one_re, one_mul,
    div_mul_cancel₀ _ (Real.sqrt_pos.mpr hx).ne']

/-- At positive scale the exponential Mangoldt atoms are summable.
Transport existing Gamma summability through real projection and multiplication by sqrt(x). -/
theorem summable_principalExponentialMass {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ ↦ Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n) := by
  have hs :=
    (Complex.reCLM.summable
          (PaperStatements.MellinKernel.summable_summand PaperStatements.gammaMellinKernel
            (1 : DirichletCharacter ℂ 1) hx)).mul_right
      (Real.sqrt x)
  exact hs.congr (gamma_principal_scaled_term hx)

/-- At positive scale the full exponential mass equals the real principal
Gamma series times sqrt(x). Commute the continuous real projection and scalar multiplication
with the convergent series. This connects arithmetic endpoint bounds to the actual kernel. -/
theorem principalExponentialMass_eq_scaled_gamma {x : ℝ} (hx : 0 < x) :
    principalExponentialMass x =
      (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re *
        Real.sqrt x := by
  have hs :=
    PaperStatements.MellinKernel.summable_summand PaperStatements.gammaMellinKernel
      (1 : DirichletCharacter ℂ 1) hx
  dsimp only [principalExponentialMass]
  rw [← tsum_congr (gamma_principal_scaled_term hx), tsum_mul_right]
  exact congrArg (fun z : ℝ ↦ z * Real.sqrt x) (Complex.reCLM.map_tsum hs).symm

/-- For positive ordered scales the unnormalized principal exponential mass
increases. Compare every nonnegative exponential Mangoldt atom and use summability. -/
theorem principalExponentialMass_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    principalExponentialMass a ≤ principalExponentialMass b := by
  apply
    Summable.tsum_le_tsum _ (summable_principalExponentialMass ha)
      (summable_principalExponentialMass (ha.trans_le hab))
  intro n
  exact
    mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr
        (by
          simpa only [neg_div] using
            neg_le_neg (div_le_div_of_nonneg_left (Nat.cast_nonneg n) ha hab)))
      (ArithmeticFunction.vonMangoldt_nonneg (n := n))

/-- The actual twice-normalized ramp sum minus the real principal Gamma series.
Its strict excess over the character budget extracts witnesses. Endpoint bounds below
apply to this expression itself, with no separate approximate main terms. -/
noncomputable def principalRampDifference (x : ℝ) : ℝ :=
  2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
    (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re

/-- At positive scale the principal-ramp difference is a single numerator
2*ramp-principalMass divided by sqrt(x). Substitute the exact principal identity. -/
theorem principalRampDifference_eq_mass {x : ℝ} (hx : 0 < x) :
    principalRampDifference x =
      (2 * AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x -
          principalExponentialMass x) /
        Real.sqrt x := by
  rw [principalExponentialMass_eq_scaled_gamma hx, sub_div,
    mul_div_cancel_right₀ _ (Real.sqrt_pos.mpr hx).ne', mul_div_assoc]
  rfl

/-- On a positive real scale interval, a nonnegative lower bound C for twice
the ramp at the left endpoint minus principal mass at the right endpoint gives C/R below
the actual difference when sqrt(right)<=R. Preserve the combined numerator before division. -/
theorem principalRampDifference_lower_of_endpoints {a b x C R : ℝ} (ha : 0 < a) (hax : a ≤ x)
    (hxb : x ≤ b)
    (hC :
      C ≤
        2 * AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum a -
          principalExponentialMass b)
    (hC0 : 0 ≤ C) (hR : Real.sqrt b ≤ R) : C / R ≤ principalRampDifference x := by
  have hx := ha.trans_le hax
  have hS := AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum_mono ha hax
  have hP := principalExponentialMass_mono hx hxb
  have hnum :
    C ≤
      2 * AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x -
        principalExponentialMass x := by
    linarith only [hC, hS, hP]
  have hr := (Real.sqrt_le_sqrt hxb).trans hR
  rw [principalRampDifference_eq_mass hx]
  exact
    (div_le_div_of_nonneg_left hC0 (Real.sqrt_pos.mpr hx) hr).trans
      (div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg x))

end PseudoPrime.LLS
