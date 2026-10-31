/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.SignedHalfZeroRemainderBounds
public import PseudoPrime.LLS.DirectHadamardConductorBounds
public import PseudoPrime.LLS.SignedHalfPowerWitnessBounds

/-! # Selected real half-scale remainder budget -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under primitive GRH, N≥3 and x≥4, the real half-scale remainder is at
most (4/5)log(N)+5. Combine the direct Hadamard mass bound with both trivial corrections. -/
theorem logarithmicHalfRemainder_re_le {N : ℕ} [NeZero N] (hN : 3 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 4 ≤ x) :
    (AnalyticNumberTheory.DirichletLFunction.logarithmicHalfRemainder hne x).re ≤
      (4 / 5 : ℝ) * Real.log N + 5 := by
  have hO :=
    AnalyticNumberTheory.DirichletLFunction.log_origin_half_re_le (le_trans (by decide : 2 ≤ 3) hN)
      hGRH hp hne hinv (show 1 ≤ x by linarith only [hx])
  have ht :=
    Complex.re_le_norm
      (AnalyticNumberTheory.DirichletLFunction.logarithmicTrivialCorrection χ x -
        AnalyticNumberTheory.DirichletLFunction.logarithmicTrivialCorrection χ (x / 2))
  have htn :=
    norm_sub_le (AnalyticNumberTheory.DirichletLFunction.logarithmicTrivialCorrection χ x)
      (AnalyticNumberTheory.DirichletLFunction.logarithmicTrivialCorrection χ (x / 2))
  have h1 :=
    AnalyticNumberTheory.DirichletLFunction.norm_logarithmicTrivialCorrection_le_one χ
      (show 2 ≤ x by linarith only [hx])
  have h2 :=
    AnalyticNumberTheory.DirichletLFunction.norm_logarithmicTrivialCorrection_le_one χ
      (show 2 ≤ x / 2 by linarith only [hx])
  have hb := PaperStatements.abs_primitiveBRe_le_direct_reciprocal hN hp hGRH
  have hl := Real.log_natCast_nonneg N
  have h20 := Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 2)
  have h21 : Real.log (2 : ℝ) ≤ 7 / 10 := by linarith only [Real.log_two_lt_d9]
  have hm :=
    mul_le_mul_of_nonneg_left h21
      (show 0 ≤ |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| + Real.log N / 2 by
        linarith only [abs_nonneg (AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ), hl])
  have hsq := pow_le_pow_left₀ h20 h21 2
  dsimp only [AnalyticNumberTheory.DirichletLFunction.logarithmicHalfRemainder]
  simp only [Complex.sub_re, Complex.add_re] at hO ht ⊢
  nlinarith only [hO, ht, htn, h1, h2, hb, hm, hsq, hl]

end PseudoPrime.LLS
