/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.FamilyHalfScaleBudget

/-! # Positivity and modulus monotonicity of explicit half-scale budgets -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Collect the two fixed completed-genus mass constants and the numerical part
of the correction budget. The modulus dependence remains a separate `log q` term.
This fixed positive constant is used in scalar tail and remainder estimates. -/
noncomputable def genusCorrectionBudgetConstant : ℝ :=
  12 +
    (LogFreeDensity.completedGenusMassShiftConstant +
        LogFreeDensity.completedGenusMassCenterConstant) *
      (Real.log 4 + 1)

/-- The fixed genus-correction budget constant is positive. Use positivity of
the two existing mass constants and `log 4`. This certifies nonnegativity of the
explicit correction uniformly in all positive moduli. -/
theorem genusCorrectionBudgetConstant_pos : 0 < genusCorrectionBudgetConstant := by
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num only)
  exact
    add_pos_of_pos_of_nonneg (by norm_num only)
      (mul_nonneg
        (add_nonneg LogFreeDensity.completedGenusMassShiftConstant_pos.le
          LogFreeDensity.completedGenusMassCenterConstant_pos.le)
        (by linarith only [hlog]))

/-- Rewrite the high-zero budget as its two original tail terms plus the fixed
genus constant and `log q`. Expand the two definitions and rearrange. This exposes
all modulus dependence for monotonicity and asymptotic absorption. -/
theorem regularizedHighZeroTailMajorant_eq (q : ℕ) (x : ℝ) (H : ℕ) (K : ℝ) :
    regularizedHighZeroTailMajorant q x H K =
      24 * x * K * Real.log q / ((H - 1 : ℕ) : ℝ) +
        192 * x * K * (Real.log ((H + 3 : ℕ) : ℝ) + 2) / (H + 3) +
        (32 * Real.log 2) * (genusCorrectionBudgetConstant + Real.log q) := by
  dsimp only [regularizedHighZeroTailMajorant, genusCorrectionBudgetConstant]
  ring

/-- For positive natural modulus, nonnegative scale, and nonnegative local-count
constant, the high-zero budget is nonnegative at every natural cutoff. Check its
three terms separately. This allows replacing a family size by an upper bound. -/
theorem regularizedHighZeroTailMajorant_nonneg {q H : ℕ} {x K : ℝ} (hq : 1 ≤ q) (hx : 0 ≤ x)
    (hK : 0 ≤ K) : 0 ≤ regularizedHighZeroTailMajorant q x H K := by
  have hqlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hhlog : 0 ≤ Real.log ((H + 3 : ℕ) : ℝ) :=
    Real.log_nonneg
      (by
        norm_num only [Nat.cast_add, Nat.cast_ofNat]
        linarith only [(Nat.cast_nonneg H : (0 : ℝ) ≤ H)])
  rw [regularizedHighZeroTailMajorant_eq]
  exact
    add_nonneg
      (add_nonneg
        (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num only) hx) hK) hqlog)
          (Nat.cast_nonneg (H - 1)))
        (div_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num only) hx) hK) (by linarith only [hhlog]))
          (by linarith only [(Nat.cast_nonneg H : (0 : ℝ) ≤ H)])))
      (mul_nonneg (mul_nonneg (by norm_num only) (Real.log_nonneg (by norm_num only)))
        (add_nonneg genusCorrectionBudgetConstant_pos.le hqlog))

/-- At fixed cutoff and nonnegative scale and tail constant, the high-zero budget
is monotone in positive modulus. Only `log q` varies; its coefficients are
nonnegative. This supplies one tail majorant for all primitive conductors. -/
theorem regularizedHighZeroTailMajorant_mono_modulus {q r H : ℕ} {x K : ℝ} (hq : 0 < q)
    (hqr : q ≤ r) (hx : 0 ≤ x) (hK : 0 ≤ K) :
    regularizedHighZeroTailMajorant q x H K ≤ regularizedHighZeroTailMajorant r x H K := by
  have hl := Real.log_le_log (Nat.cast_pos.mpr hq) (Nat.cast_le.mpr hqr)
  rw [regularizedHighZeroTailMajorant_eq, regularizedHighZeroTailMajorant_eq]
  have hp : 0 ≤ 24 * x * K := mul_nonneg (mul_nonneg (by norm_num only) hx) hK
  have ht := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl hp) (Nat.cast_nonneg (H - 1))
  have hgc : 0 ≤ 32 * Real.log 2 :=
    mul_nonneg (by norm_num only) (Real.log_nonneg (by norm_num only))
  have hg :=
    mul_le_mul_of_nonneg_left
      (show genusCorrectionBudgetConstant + Real.log q ≤ genusCorrectionBudgetConstant + Real.log r
        from add_le_add le_rfl hl)
      hgc
  exact add_le_add (add_le_add ht le_rfl) hg

/-- At positive modulus and scale at least two, nonnegative budget constants make
the full primitive remainder nonnegative. Combine the low-height and high-tail
positivity bounds. This permits cardinality majorization of finite remainder sums. -/
theorem primitiveHalfScaleRemainderBudget_nonneg {q H : ℕ} {x σ C K T : ℝ} (hq : 1 ≤ q) (hx : 2 ≤ x)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hT : 0 ≤ T) :
    0 ≤ primitiveHalfScaleRemainderBudget q x σ H C K T := by
  have hqlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hxlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith only [hx])
  have hhlog : 0 ≤ Real.log (4 + ((H + 1 : ℕ) : ℝ)) :=
    Real.log_nonneg (by linarith only [(Nat.cast_nonneg (H + 1) : (0 : ℝ) ≤ (H + 1 : ℕ))])
  have hcount :
    0 ≤ (2 * ((H + 1 : ℕ) : ℝ) + 1) * K * (Real.log q + Real.log (4 + ((H + 1 : ℕ) : ℝ)) + 1) :=
    mul_nonneg
      (mul_nonneg (by linarith only [(Nat.cast_nonneg (H + 1) : (0 : ℝ) ≤ (H + 1 : ℕ))]) hK)
      (by linarith only [hqlog, hhlog])
  exact
    add_nonneg
      (add_nonneg (mul_nonneg hcount (regularizedLowHeightMajorant_nonneg hx))
        (regularizedHighZeroTailMajorant_nonneg hq (by linarith only [hx]) hT))
      (mul_nonneg hC (by linarith only [hxlog]))

/-- At scale at least two with nonnegative local and tail constants, the primitive
remainder is monotone in positive modulus. Compare logarithms, multiply by the
nonnegative low-height majorant, and use high-tail monotonicity. The arithmetic
remainder constant is unchanged. This reduces conductor-dependent sums to one level. -/
theorem primitiveHalfScaleRemainderBudget_mono_modulus {q r H : ℕ} {x σ C K T : ℝ} (hq : 0 < q)
    (hqr : q ≤ r) (hx : 2 ≤ x) (hK : 0 ≤ K) (hT : 0 ≤ T) :
    primitiveHalfScaleRemainderBudget q x σ H C K T ≤
      primitiveHalfScaleRemainderBudget r x σ H C K T := by
  have hl := Real.log_le_log (Nat.cast_pos.mpr hq) (Nat.cast_le.mpr hqr)
  have hc : 0 ≤ (2 * ((H + 1 : ℕ) : ℝ) + 1) * K :=
    mul_nonneg (by linarith only [(Nat.cast_nonneg (H + 1) : (0 : ℝ) ≤ (H + 1 : ℕ))]) hK
  have hadd :
    Real.log q + Real.log (4 + ((H + 1 : ℕ) : ℝ)) + 1 ≤
      Real.log r + Real.log (4 + ((H + 1 : ℕ) : ℝ)) + 1 := by
    linarith only [hl]
  have hm :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hadd hc)
      (regularizedLowHeightMajorant_nonneg (σ := σ) hx)
  have ht :=
    regularizedHighZeroTailMajorant_mono_modulus (H := H) hq hqr (by linarith only [hx] : 0 ≤ x) hT
  exact add_le_add (add_le_add hm ht) le_rfl

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
