/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.Arithmetic.TwoAdicCorrections
import PseudoPrime.NumberTheory.JacobiCharacterCutoff
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimePowerCutoff
import PseudoPrime.LLS.Lemma23
import PseudoPrime.NumberTheory.JacobiCharacterArithmetic

/-!
2-adic weighted corrections for the Q_ne1 arithmetic bridge.
-/

namespace PseudoPrime.LLS.Extensions

/-!
The exact reciprocal decomposition is combined with the LLS Riemann lower bound.
In the `χ̃(2)=0` branch the only additional loss is the `log 2` correction.
-/

/-- The `χ̃(2)=0` branch gives the reciprocal lower bound after the 2-adic correction. -/
theorem characterReciprocalWeightedSum_re_ge_log_sub_eight_fifths_sub_log_two_of_eq_zero {q : ℕ}
    (x : ℝ) (χ : DirichletCharacter ℂ q) (hriemann : LLSRiemannReciprocalLowerBound) (hx : 2 ≤ x)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ → p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 0) :
    Real.log x - 8 / 5 - Real.log 2 ≤
      (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x
          χ.primitiveCharacter).re := by
  have hζ := hriemann x hx
  have hexact :=
    AnalyticNumberTheory.Arithmetic.reciprocalWeightedSum_sub_re_eq_twoAdicCorrection_of_eq_one
      x χ hx hodd
  have hcorr :=
    AnalyticNumberTheory.Arithmetic.twoAdicReciprocalCorrection_le_log_two_of_apply_two_eq_zero
      x χ (lt_of_lt_of_le (by norm_num only) hx) h2
  linarith

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
/-- The `χ̃(2)=0` branch gives the logarithmic lower bound after its correction loss. -/
theorem characterLogWeightedSum_re_ge_riemann_lower_sub_half_log_sq_of_eq_zero {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hriemann : LLSRiemannWeightedLowerBound) (hx : 2 ≤ x)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ → p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 0) :
    x - Real.log (2 * Real.pi) * Real.log x - 1 -
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (Real.sqrt x + 1) -
        (Real.log x) ^ 2 / 2 ≤
      (characterLogWeightedSum x
          χ.primitiveCharacter).re := by
  have hζ := hriemann x (by linarith : 1 < x)
  have hexact :=
    logWeightedMangoldtSum_sub_characterLogWeightedSum_re_eq_twoAdicCorrection_of_eq_one
      x χ (by linarith) hodd
  have hcorr :=
    twoAdicLogCorrection_le_half_log_sq_of_apply_two_eq_zero
      x χ (ne_of_gt (lt_of_lt_of_le (by norm_num only) hx)) h2
  linarith

/-! In the `χ̃(2)=1` branch the reciprocal correction is zero, giving `log x - 8/5`. -/

theorem characterReciprocalWeightedSum_re_ge_log_sub_eight_fifths_of_eq_one {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hquad : χ.primitiveCharacter.IsQuadratic)
    (hriemann : LLSRiemannReciprocalLowerBound) (hx : 2 ≤ x)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ → p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 1) :
    Real.log x - 8 / 5 ≤
      (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x
          χ.primitiveCharacter).re := by
  have hζ := hriemann x hx
  have hexact :=
    AnalyticNumberTheory.Arithmetic.reciprocalWeightedSum_sub_re_eq_twoAdicCorrection_of_eq_one
      x χ hx hodd
  have hcorr :=
    AnalyticNumberTheory.Arithmetic.twoAdicReciprocalCorrection_eq_zero_of_apply_two_eq_one
      x χ hquad h2
  rw [hcorr] at hexact
  linarith

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
/-- For `χ̃(2)=1` the correction vanishes. This theorem deliberately retains the weaker
`(log x)^2 / 2` loss so that the logarithmic branches share an envelope. -/
theorem characterLogWeightedSum_re_ge_riemann_lower_sub_half_log_sq_of_eq_one {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hquad : χ.primitiveCharacter.IsQuadratic)
    (hriemann : LLSRiemannWeightedLowerBound) (hx : 2 ≤ x)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ → p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 1) :
    x - Real.log (2 * Real.pi) * Real.log x - 1 -
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (Real.sqrt x + 1) -
        (Real.log x) ^ 2 / 2 ≤
      (characterLogWeightedSum x
          χ.primitiveCharacter).re := by
  have hζ := hriemann x (by linarith : 1 < x)
  have hexact :=
    logWeightedMangoldtSum_sub_characterLogWeightedSum_re_eq_twoAdicCorrection_of_eq_one
      x χ hx hodd
  have hcorr :=
    twoAdicLogCorrection_eq_zero_of_apply_two_eq_one x χ
      hquad (ne_of_gt (lt_of_lt_of_le (by norm_num only) hx)) h2
  have hcorrbound :=
    twoAdicLogCorrection_le_half_log_sq_of_apply_two_eq_one
      x χ hquad (ne_of_gt (lt_of_lt_of_le (by norm_num only) hx)) h2
  rw [hcorr] at hexact
  linarith [hcorrbound]

/-! The c=-1 branch pays the full odd-tail square-log correction. -/

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
theorem characterLogWeightedSum_re_ge_riemann_lower_sub_three_half_log_sq_of_eq_neg_one {q : ℕ}
    (x : ℝ) (χ : DirichletCharacter ℂ q) (hquad : χ.primitiveCharacter.IsQuadratic)
    (hriemann : LLSRiemannWeightedLowerBound) (hx : 2 ≤ x)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ → p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = -1) :
    x - Real.log (2 * Real.pi) * Real.log x - 1 -
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (Real.sqrt x + 1) -
        (3 / 2) * (Real.log x) ^ 2 ≤
      (characterLogWeightedSum x
          χ.primitiveCharacter).re := by
  have hζ := hriemann x (by linarith : 1 < x)
  have hexact :=
    logWeightedMangoldtSum_sub_characterLogWeightedSum_re_eq_twoAdicCorrection_of_eq_one
      x χ hx hodd
  have hcorr :=
    twoAdicLogCorrection_le_log_sq_of_apply_two_eq_neg_one
      x χ hquad hx h2
  have hlognonneg : 0 ≤ (Real.log x) ^ 2 := sq_nonneg _
  linarith

/-!
The sharpened c=-1 logarithmic lower bound keeps the c=0 half-square envelope and pays only the
additional loss `δ = log 2 * (log x - log 2)`. It supplies the corrected lower bound used in
`primitiveQuadraticLogWeightedLower_of_qneOne_neg_one_branch_corrected`.
-/

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
theorem characterLogWeightedSum_re_ge_riemann_lower_half_log_sq_sub_delta_of_eq_neg_one {q : ℕ}
    (x : ℝ) (χ : DirichletCharacter ℂ q) (hquad : χ.primitiveCharacter.IsQuadratic)
    (hriemann : LLSRiemannWeightedLowerBound) (hx : 4 ≤ x)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ → p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = -1) :
    x - Real.log (2 * Real.pi) * Real.log x - 1 -
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (Real.sqrt x + 1) -
        (Real.log x) ^ 2 / 2 -
        Real.log 2 * (Real.log x - Real.log 2) ≤
      (characterLogWeightedSum x
          χ.primitiveCharacter).re := by
  have hζ := hriemann x (by linarith : 1 < x)
  have hexact :=
    logWeightedMangoldtSum_sub_characterLogWeightedSum_re_eq_twoAdicCorrection_of_eq_one
      x χ (by linarith) hodd
  have hcorr :=
    twoAdicLogCorrection_le_half_log_sq_add_log_two_mul_log_half_of_apply_two_eq_neg_one
      x χ hquad hx h2
  linarith

/-! The c=-1 reciprocal lower bound exposes the explicit odd-tail loss. -/

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
theorem characterReciprocalWeightedSum_re_ge_log_sub_cneg_one {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hquad : χ.primitiveCharacter.IsQuadratic)
    (hriemann : LLSRiemannReciprocalLowerBound) (hx : 2 ≤ x)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ → p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = -1) :
    Real.log x - 8 / 5 - (4 / 3) * Real.log 2 ≤
      (characterReciprocalWeightedSum x
          χ.primitiveCharacter).re := by
  have hζ := hriemann x hx
  have hexact :=
    reciprocalWeightedSum_sub_re_eq_twoAdicCorrection_of_eq_one
      x χ hx hodd
  have hcorr :=
    twoAdicReciprocalCorrection_le_four_thirds_log_two_of_apply_two_eq_neg_one
      x χ hquad hx h2
  linarith

end PseudoPrime.LLS.Extensions
