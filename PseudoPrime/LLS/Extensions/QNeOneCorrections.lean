/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TwoAdicCorrections
public import PseudoPrime.NumberTheory.JacobiCharacterArithmetic
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimePowerCutoff
public import PseudoPrime.LLS.Lemma23

/-!
2-adic weighted corrections for the Q_ne1 arithmetic bridge.
-/

@[expose] public section

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
    AnalyticNumberTheory.Arithmetic.reciprocalWeightedSum_sub_re_eq_twoAdicCorrection_of_eq_one x χ
      hx hodd
  have hcorr :=
    AnalyticNumberTheory.Arithmetic.twoAdicReciprocalCorrection_le_log_two_of_apply_two_eq_zero x χ
      (lt_of_lt_of_le (by norm_num only) hx) h2
  linarith only [hζ, hexact, hcorr]

/-! In the `χ̃(2)=1` branch the reciprocal correction is zero, giving `log x - 8/5`. -/

/-- For `x ≥ 2`, a primitive inducing character that is one at two and at the
specified odd primes inherits the Riemann reciprocal lower bound `log x - 8/5`.
The exact two-adic decomposition has zero correction in this branch, supplying its sharp
reciprocal input to the three-branch comparison. -/
theorem characterReciprocalWeightedSum_re_ge_log_sub_eight_fifths_of_eq_one {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hriemann : LLSRiemannReciprocalLowerBound) (hx : 2 ≤ x)
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
    AnalyticNumberTheory.Arithmetic.reciprocalWeightedSum_sub_re_eq_twoAdicCorrection_of_eq_one x χ
      hx hodd
  have hcorr :=
    AnalyticNumberTheory.Arithmetic.twoAdicReciprocalCorrection_eq_zero_of_apply_two_eq_one x χ h2
  rw [hcorr] at hexact
  linarith only [hζ, hexact]

/-! The c=-1 branch pays the full odd-tail square-log correction. -/

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
/-- With the Riemann logarithmic lower bound, `x ≥ 2`, and odd-prime triviality, the
branch with primitive-character value `-1` at two admits the displayed `3(log x)²/2` loss.
The exact defect identity and a two-adic correction bounded by `(log x)²` imply this
coarser envelope by nonnegativity of the additional half-square. -/
theorem characterLogWeightedSum_re_ge_riemann_lower_sub_three_half_log_sq_of_eq_neg_one {q : ℕ}
    (x : ℝ) (χ : DirichletCharacter ℂ q) (hriemann : LLSRiemannWeightedLowerBound) (hx : 2 ≤ x)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ → p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = -1) :
    x - Real.log (2 * Real.pi) * Real.log x - 1 -
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (Real.sqrt x + 1) -
        (3 / 2) * (Real.log x) ^ 2 ≤
      (characterLogWeightedSum x χ.primitiveCharacter).re := by
  have hζ := hriemann x (by exact lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 2) hx)
  have hexact :=
    logWeightedMangoldtSum_sub_characterLogWeightedSum_re_eq_twoAdicCorrection_of_eq_one x χ hx hodd
  have hcorr := twoAdicLogCorrection_le_log_sq_of_apply_two_eq_neg_one x χ hx h2
  have hlognonneg : 0 ≤ (Real.log x) ^ 2 := sq_nonneg _
  linarith only [hζ, hexact, hcorr, hlognonneg]

/-! The c=-1 reciprocal lower bound exposes the explicit odd-tail loss. -/

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
/-- For `x ≥ 2`, the branch with value `-1` at two and the stated odd-prime
triviality loses at most `(4/3) log 2` from the Riemann reciprocal bound.
Combine the exact two-adic decomposition with its odd-tail estimate; this supplies the
reciprocal lower input to the corrected negative-one branch. -/
theorem characterReciprocalWeightedSum_re_ge_log_sub_cneg_one {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hriemann : LLSRiemannReciprocalLowerBound) (hx : 2 ≤ x)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ → p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = -1) :
    Real.log x - 8 / 5 - (4 / 3) * Real.log 2 ≤
      (characterReciprocalWeightedSum x χ.primitiveCharacter).re := by
  have hζ := hriemann x hx
  have hexact := reciprocalWeightedSum_sub_re_eq_twoAdicCorrection_of_eq_one x χ hx hodd
  have hcorr := twoAdicReciprocalCorrection_le_four_thirds_log_two_of_apply_two_eq_neg_one x χ hx h2
  linarith only [hζ, hexact, hcorr]

end PseudoPrime.LLS.Extensions
