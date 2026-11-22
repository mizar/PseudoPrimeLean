/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.QuarterPhaseHorner
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.DyadicEM8Intervals

/-! # Compact critical-power terms from phase and amplitude certificates -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Compute an outward-rounded interval for the negative product of a height and a logarithm.
The input intervals share the positive integer scale `G`. This interval supplies the phase
argument for a compact critical-line power certificate. -/
def criticalPhaseArgument (G : ℤ) (T L : Analysis.IntegerInterval) : Analysis.IntegerInterval :=
  Analysis.roundedProduct G T.neg L

/-- Certified height and logarithm intervals contain the phase argument after computed negation
and multiplication. The result provides the exact `-t * log n` input to quarter-turn reduction. -/
theorem criticalPhaseArgument_contains {G : ℤ} {T L : Analysis.IntegerInterval} {t : ℝ} {n : ℕ}
    (hG : 0 < G) (ht : T.Contains G t) (hl : L.Contains G (Real.log n)) :
    (criticalPhaseArgument G T L).Contains G (-t * Real.log n) := by
  exact Analysis.roundedProduct_contains hG (Analysis.IntegerInterval.neg_contains ht) hl

/-- A certified logarithm, height, π interval, rational Taylor center, quarter-turn residue,
and shared amplitude witness enclose a positive-integer critical-line power term. Integer
endpoint comparisons certify the reduced-phase error, and the computed phase and amplitude
rectangles are multiplied with outward rounding. This is the table-free soundness theorem used by
the compact odd-term evaluator. -/
theorem criticalTerm_compact (G e d c k : ℤ) (n : ℕ) (t : ℝ) (j : Fin 4) (q : ℚ)
    (T L P X : Analysis.IntegerInterval) (w : Analysis.AmplitudeWitness) (hG : 0 < G) (hn : 0 < n)
    (ht : T.Contains G t) (hl : L.Contains G (Real.log n)) (hpi : P.Contains G Real.pi)
    (hq : X.Contains G (q : ℝ)) (hd : |(q : ℝ)| ≤ 1 / 4) (he : (1 / 2 ^ 120 : ℝ) ≤ (e : ℝ) / G)
    (hj : k % 4 = j.val) (hcenter : 4 * (q : ℝ) = (c : ℝ) / G)
    (hlo : c - d ≤ (Analysis.quarterRemainder G k (criticalPhaseArgument G T L) P).lower)
    (hup : (Analysis.quarterRemainder G k (criticalPhaseArgument G T L) P).upper ≤ c + d)
    (hw : w.check G n = true) :
    Analysis.complexIntervalContains
      (criticalTermBox G w.inverse (Analysis.quarterComputedResult X G e d j)).1
      (criticalTermBox G w.inverse (Analysis.quarterComputedResult X G e d j)).2 G
      (dyadicPowerTerm ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) n) := by
  have hx := criticalPhaseArgument_contains hG ht hl
  have hp :=
    Analysis.quarter_computed_checked X (criticalPhaseArgument G T L) P G e d c q _ k j hG hq hd he
      hj hx hpi hcenter hlo hup
  exact criticalTermBox_witness G w (Analysis.quarterComputedResult X G e d j) n t hG hn hw hp

/-- A critical-line term is enclosed using an integer phase center `c` at scale `G`.
The computed rational Taylor center is `c / (4 * G)`; integer bounds on `c` establish its
Taylor domain automatically. This interface removes separate rational-center proofs from each
entry of an endpoint certificate while retaining checked phase, logarithm, and amplitude inputs. -/
theorem criticalTerm_centered (G e d c k : ℤ) (n : ℕ) (t : ℝ) (j : Fin 4)
    (T L P : Analysis.IntegerInterval) (w : Analysis.AmplitudeWitness) (hG : 0 < G) (hn : 0 < n)
    (ht : T.Contains G t) (hl : L.Contains G (Real.log n)) (hpi : P.Contains G Real.pi)
    (hc1 : -G ≤ c) (hc2 : c ≤ G) (he : (1 / 2 ^ 120 : ℝ) ≤ (e : ℝ) / G) (hj : k % 4 = j.val)
    (hlo : c - d ≤ (Analysis.quarterRemainder G k (criticalPhaseArgument G T L) P).lower)
    (hup : (Analysis.quarterRemainder G k (criticalPhaseArgument G T L) P).upper ≤ c + d)
    (hw : w.check G n = true) :
    let X := Analysis.roundedConstant G c (4 * G)
    Analysis.complexIntervalContains
      (criticalTermBox G w.inverse (Analysis.quarterComputedResult X G e d j)).1
      (criticalTermBox G w.inverse (Analysis.quarterComputedResult X G e d j)).2 G
      (dyadicPowerTerm ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) n) := by
  let q : ℚ := c / (4 * G)
  have hg : (0 : ℝ) < G := Int.cast_pos.mpr hG
  have h4 : (0 : ℝ) < 4 * G := mul_pos (by norm_num only) hg
  have h4z : (0 : ℤ) < 4 * G := mul_pos (by decide) hG
  have hlo' : -(G : ℝ) ≤ c := by exact_mod_cast hc1
  have hhi' : (c : ℝ) ≤ G := by exact_mod_cast hc2
  have hqr : (q : ℝ) = (c : ℝ) / (4 * G) := by
    norm_num only [q, Rat.cast_div, Rat.cast_intCast, Rat.cast_mul, Rat.cast_ofNat]
  have hq : (Analysis.roundedConstant G c (4 * G)).Contains G (q : ℝ) := by
    have h := Analysis.roundedConstant_contains (G := G) (p := c) (d := 4 * G) hG h4z
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
  have hcenter : 4 * (q : ℝ) = (c : ℝ) / G := by
    rw [hqr, ← mul_div_assoc, mul_div_mul_left _ _ (by norm_num only : (4 : ℝ) ≠ 0)]
  exact
    criticalTerm_compact G e d c k n t j q T L P (Analysis.roundedConstant G c (4 * G)) w hG hn ht
      hl hpi hq hsmall he hj hcenter hlo hup hw

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
