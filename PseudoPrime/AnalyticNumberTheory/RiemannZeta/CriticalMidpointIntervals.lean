/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.CriticalShiftIntervals
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.CompactPhaseWitness

/-! # Shared midpoint and phase enclosures for both endpoints -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Reconstruct phase-only witnesses by traversing shared logarithms and compact phase data.
The amplitude fields are zero placeholders and are not used by the phase checker or its
soundness theorem. This avoids storing or checking amplitudes for the common endpoint shift. -/
def compactPhaseFamily (G : ℤ) (logs : List Analysis.NaturalLogWitness)
    (phases : List CompactPhaseWitness) : List CriticalTermWitness :=
  (logs.zip phases).map fun p ↦ compactTermWitness G p.1 ⟨⟨0, 0⟩, ⟨0, 0⟩⟩ p.2

/-- A midpoint term and one unit-phase enclosure give enclosures for the two endpoints at
`c - h` and `c + h`. Conjugating the phase reverses the displacement, so both endpoints use
the same certified midpoint and the same phase rectangle. This theorem is independent of the
choice of base, midpoint, displacement, or certificate table. -/
theorem midpoint_shift_contains (G : ℤ) (A R : Analysis.IntegerInterval × Analysis.IntegerInterval)
    (n : ℕ) (c h : ℝ) (hG : 0 < G) (hn : 0 < n)
    (hA :
      Analysis.complexIntervalContains A.1 A.2 G
        (dyadicPowerTerm ((((1 / 2 : ℝ) : ℂ) + (c : ℂ) * Complex.I)) n))
    (hR :
      Analysis.complexIntervalContains R.1 R.2 G
        (Complex.exp (((-h * Real.log n : ℝ) : ℂ) * Complex.I))) :
    Analysis.complexIntervalContains (Analysis.roundedComplexProduct G A (R.1, R.2.neg)).1
        (Analysis.roundedComplexProduct G A (R.1, R.2.neg)).2 G
        (dyadicPowerTerm ((((1 / 2 : ℝ) : ℂ) + ((c - h : ℝ) : ℂ) * Complex.I)) n) ∧
      Analysis.complexIntervalContains (Analysis.roundedComplexProduct G A R).1
        (Analysis.roundedComplexProduct G A R).2 G
        (dyadicPowerTerm ((((1 / 2 : ℝ) : ℂ) + ((c + h : ℝ) : ℂ) * Complex.I)) n) := by
  have hneg :
    Analysis.complexIntervalContains R.1 R.2.neg G
      (Complex.exp (((-(-h) * Real.log n : ℝ) : ℂ) * Complex.I)) := by
    have hc :
      Analysis.complexIntervalContains R.1 R.2.neg G
        (starRingEnd ℂ (Complex.exp (((-h * Real.log n : ℝ) : ℂ) * Complex.I))) := by
      exact
        ⟨by simpa only [Complex.conj_re] using hR.1, by
          simpa only [Complex.conj_im] using Analysis.IntegerInterval.neg_contains hR.2⟩
    have hid :
      starRingEnd ℂ (Complex.exp (((-h * Real.log n : ℝ) : ℂ) * Complex.I)) =
        Complex.exp (((-(-h) * Real.log n : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_conj]
      simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg, neg_mul,
        mul_neg, neg_neg]
    rw [hid] at hc
    exact hc
  constructor
  · rw [show c - h = c + -h by ring, dyadicPowerTerm_shift n c (-h) hn]
    exact Analysis.roundedComplexProduct_contains hG hA hneg
  · rw [dyadicPowerTerm_shift n c h hn]
    exact Analysis.roundedComplexProduct_contains hG hA hR

/-- A checked phase witness and a midpoint enclosure certify both endpoint terms at once.
The phase witness is checked once for the displacement and can be reused across every
midpoint with the same displacement. -/
theorem CriticalTermWitness.midpoint_contains (w : CriticalTermWitness) (G e : ℤ)
    (A : Analysis.IntegerInterval × Analysis.IntegerInterval) (T P : Analysis.IntegerInterval)
    (c h : ℝ) (hG : 0 < G) (hh : T.Contains G h) (hpi : P.Contains G Real.pi)
    (he : (1 / 2 ^ 120 : ℝ) ≤ (e : ℝ) / G)
    (hlog : (w.log.lower : ℝ) ≤ Real.log w.log.base ∧ Real.log w.log.base ≤ (w.log.upper : ℝ))
    (hw : w.check G T P = true)
    (hmid :
      Analysis.complexIntervalContains A.1 A.2 G
        (dyadicPowerTerm ((((1 / 2 : ℝ) : ℂ) + (c : ℂ) * Complex.I)) w.log.base)) :
    let R := w.phaseResult G e
    Analysis.complexIntervalContains (Analysis.roundedComplexProduct G A (R.1, R.2.neg)).1
        (Analysis.roundedComplexProduct G A (R.1, R.2.neg)).2 G
        (dyadicPowerTerm ((((1 / 2 : ℝ) : ℂ) + ((c - h : ℝ) : ℂ) * Complex.I)) w.log.base) ∧
      Analysis.complexIntervalContains (Analysis.roundedComplexProduct G A R).1
        (Analysis.roundedComplexProduct G A R).2 G
        (dyadicPowerTerm ((((1 / 2 : ℝ) : ℂ) + ((c + h : ℝ) : ℂ) * Complex.I)) w.log.base) := by
  exact
    midpoint_shift_contains G A (w.phaseResult G e) w.log.base c h hG (of_decide_eq_true hw).1 hmid
      (w.phase_contains G e T P h hG hh hpi he hlog hw)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
