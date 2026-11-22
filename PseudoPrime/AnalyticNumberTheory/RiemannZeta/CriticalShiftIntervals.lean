/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.CriticalTermWitness

/-! # Shared phase rotations for shifted critical-line terms -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Shifting a critical-line height by `h` multiplies a positive-base power term by the
unit phase `exp(-h * log n * I)`. The amplitude is unchanged. This identity allows a small
rotation to be shared among endpoint pairs with the same height displacement. -/
theorem dyadicPowerTerm_shift (n : ℕ) (t h : ℝ) (hn : 0 < n) :
    dyadicPowerTerm ((((1 / 2 : ℝ) : ℂ) + ((t + h : ℝ) : ℂ) * Complex.I)) n =
      dyadicPowerTerm ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) n *
        Complex.exp (((-h * Real.log n : ℝ) : ℂ) * Complex.I) := by
  have hreal : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  simp only [dyadicPowerTerm, ite_eq_right (Nat.ne_of_gt hn), ← Complex.ofReal_natCast,
    critical_power_sqrt_phase _ _ hreal]
  have hx :
    (((-(t + h) * Real.log n : ℝ) : ℂ) * Complex.I) =
      (((-t * Real.log n : ℝ) : ℂ) * Complex.I) + (((-h * Real.log n : ℝ) : ℂ) * Complex.I) := by
    simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_add]
    ring
  rw [hx, Complex.exp_add, mul_assoc]

/-- Compute the unit-phase rectangle encoded by a critical-term witness. Unlike the full term
rectangle, this output has no amplitude factor and can be reused at every common height shift. -/
def CriticalTermWitness.phaseResult (w : CriticalTermWitness) (G e : ℤ) :
    Analysis.IntegerInterval × Analysis.IntegerInterval :=
  Analysis.quarterComputedResult (Analysis.roundedConstant G w.center (4 * G)) G e w.radius
    w.residue

/-- A checked phase witness and a shared certified logarithm enclose the unit phase at height
`t`. Its integer center provides the rational Taylor center, and the quarter-turn checker
handles the exact rotation. No square-root or reciprocal amplitude certificate is required. -/
theorem CriticalTermWitness.phase_contains (w : CriticalTermWitness) (G e : ℤ)
    (T P : Analysis.IntegerInterval) (t : ℝ) (hG : 0 < G) (ht : T.Contains G t)
    (hpi : P.Contains G Real.pi) (he : (1 / 2 ^ 120 : ℝ) ≤ (e : ℝ) / G)
    (hlog : (w.log.lower : ℝ) ≤ Real.log w.log.base ∧ Real.log w.log.base ≤ (w.log.upper : ℝ))
    (hw : w.check G T P = true) :
    Analysis.complexIntervalContains (w.phaseResult G e).1 (w.phaseResult G e).2 G
      (Complex.exp (((-t * Real.log w.log.base : ℝ) : ℂ) * Complex.I)) := by
  have ⟨_hn, hc1, hc2, hll, hlu, hj, hlo, hup⟩ := of_decide_eq_true hw
  have hl := w.log.interval_contains G w.logBox hG hlog hll hlu
  have hx := criticalPhaseArgument_contains hG ht hl
  let q : ℚ := w.center / (4 * G)
  have hg : (0 : ℝ) < G := Int.cast_pos.mpr hG
  have h4 : (0 : ℝ) < 4 * G := mul_pos (by norm_num only) hg
  have h4z : (0 : ℤ) < 4 * G := mul_pos (by decide) hG
  have hlo' : -(G : ℝ) ≤ w.center := by exact_mod_cast hc1
  have hhi' : (w.center : ℝ) ≤ G := by exact_mod_cast hc2
  have hqr : (q : ℝ) = (w.center : ℝ) / (4 * G) := by
    norm_num only [q, Rat.cast_div, Rat.cast_intCast, Rat.cast_mul, Rat.cast_ofNat]
  have hq : (Analysis.roundedConstant G w.center (4 * G)).Contains G (q : ℝ) := by
    have h := Analysis.roundedConstant_contains (G := G) (p := w.center) (d := 4 * G) hG h4z
    rw [hqr]
    norm_num only [Int.cast_mul, Int.cast_ofNat] at h
    exact h
  have hsmall : |(q : ℝ)| ≤ 1 / 4 := by
    rw [hqr, abs_le]
    constructor
    · apply (le_div_iff₀ h4).2
      linarith only [hlo']
    · apply (div_le_iff₀ h4).2
      linarith only [hhi']
  have hcenter : 4 * (q : ℝ) = (w.center : ℝ) / G := by
    rw [hqr, ← mul_div_assoc, mul_div_mul_left _ _ (by norm_num only : (4 : ℝ) ≠ 0)]
  exact
    Analysis.quarter_computed_checked _ _ P G e w.radius w.center q _ w.turn w.residue hG hq hsmall
      he hj hx hpi hcenter hlo hup

/-- A certified left-endpoint term and a certified unit shift phase yield a rectangle for the
same base at the shifted endpoint. The shift identity and outward-rounded multiplication prove
the result; the unit phase depends on the displacement rather than the left endpoint. -/
theorem CriticalTermWitness.shift_contains (w : CriticalTermWitness) (G e : ℤ)
    (L : Analysis.IntegerInterval × Analysis.IntegerInterval) (T P : Analysis.IntegerInterval)
    (t h : ℝ) (hG : 0 < G) (hh : T.Contains G h) (hpi : P.Contains G Real.pi)
    (he : (1 / 2 ^ 120 : ℝ) ≤ (e : ℝ) / G)
    (hlog : (w.log.lower : ℝ) ≤ Real.log w.log.base ∧ Real.log w.log.base ≤ (w.log.upper : ℝ))
    (hw : w.check G T P = true)
    (hleft :
      Analysis.complexIntervalContains L.1 L.2 G
        (dyadicPowerTerm ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) w.log.base)) :
    Analysis.complexIntervalContains (Analysis.roundedComplexProduct G L (w.phaseResult G e)).1
      (Analysis.roundedComplexProduct G L (w.phaseResult G e)).2 G
      (dyadicPowerTerm ((((1 / 2 : ℝ) : ℂ) + ((t + h : ℝ) : ℂ) * Complex.I)) w.log.base) := by
  have hn := (of_decide_eq_true hw).1
  rw [dyadicPowerTerm_shift _ _ _ hn]
  exact
    Analysis.roundedComplexProduct_contains hG hleft
      (w.phase_contains G e T P h hG hh hpi he hlog hw)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
