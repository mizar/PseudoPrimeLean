/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.QuarterPhaseIntervals
public import PseudoPrime.Analysis.IntegerIntervalHorner
public import PseudoPrime.Analysis.ComputedPhaseRotation

/-! # Quarter-turn phase certificates from computed Horner intervals -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Compute a quarter-turn phase rectangle using a Taylor enclosure and two outward-rounded
complex squares. The two errors `e` and `d` widen the Taylor result and reduced-phase result,
respectively. The final rotation is selected by the supplied residue modulo four. -/
def quarterComputedResult (X : IntegerInterval) (G e d : ℤ) (j : Fin 4) :
    IntegerInterval × IntegerInterval :=
  let H := intervalPhaseHorner G X 24 0
  let A := roundedPhaseDouble G (H.1.widen e) (H.2.widen e)
  let B := roundedPhaseDouble G A.1 A.2
  quarterRotate (B.1.widen d) (B.2.widen d) j

/-- A computed Horner interval and two computed complex squares enclose a rational small-angle
center. A certified distance from the true reduced phase and the checked quarter-turn residue
then give containment for the original phase. Both squaring steps use outward rounding and need
no intermediate product witnesses. -/
theorem quarter_computed_contains (X : IntegerInterval) (G e d : ℤ) (q : ℚ) (x : ℝ) (k : ℤ)
    (j : Fin 4) (hG : 0 < G) (hq : X.Contains G (q : ℝ)) (hd : |(q : ℝ)| ≤ 1 / 4)
    (he : (1 / 2 ^ 120 : ℝ) ≤ (e : ℝ) / G) (hj : k % 4 = j.val)
    (hdelta : |x - k * (Real.pi / 2) - 4 * (q : ℝ)| ≤ (d : ℝ) / G) :
    complexIntervalContains (quarterComputedResult X G e d j).1 (quarterComputedResult X G e d j).2
      G (Complex.exp ((x : ℂ) * Complex.I)) := by
  have ht := intervalHorner25_phase q hG hq hd he
  have h1 := rounded_phase_double_contains hG ht
  have h2 := rounded_phase_double_contains hG h1
  have hc : (q : ℝ) + q + (q + q) = 4 * q := by ring
  rw [hc] at h2
  have hr := phase_perturb_contains h2 hdelta
  have hz := quarterRotate_contains _ _ G _ k j hj hr
  have hx : x = (x - k * (Real.pi / 2)) + k * (Real.pi / 2) := by rw [sub_add_cancel]
  rw [hx, exp_quarter_turn]
  exact hz

/-- Certified intervals for the phase and π, integer bounds on their computed remainder, and a
small rational center certify the fully computed quarter-turn phase rectangle. The endpoint
comparisons establish the perturbation bound; no intermediate squaring witnesses or external
phase table are needed. This is the soundness interface for compact endpoint certificates. -/
theorem quarter_computed_checked (X A P : IntegerInterval) (G e d c : ℤ) (q : ℚ) (x : ℝ) (k : ℤ)
    (j : Fin 4) (hG : 0 < G) (hq : X.Contains G (q : ℝ)) (hd : |(q : ℝ)| ≤ 1 / 4)
    (he : (1 / 2 ^ 120 : ℝ) ≤ (e : ℝ) / G) (hj : k % 4 = j.val) (hx : A.Contains G x)
    (hpi : P.Contains G Real.pi) (hcenter : 4 * (q : ℝ) = (c : ℝ) / G)
    (hl : c - d ≤ (quarterRemainder G k A P).lower)
    (hu : (quarterRemainder G k A P).upper ≤ c + d) :
    complexIntervalContains (quarterComputedResult X G e d j).1 (quarterComputedResult X G e d j).2
      G (Complex.exp ((x : ℂ) * Complex.I)) := by
  have hr := quarterRemainder_contains (k := k) hG hx hpi
  have hdist := interval_center_distance hG hr hl hu
  rw [← hcenter] at hdist
  exact quarter_computed_contains X G e d q x k j hG hq hd he hj hdist

/-- Compute the final complex interval for a quarter-turn Horner certificate. The Taylor
enclosure is widened by `e`, the checked squaring chain is evaluated, and its output is widened
by `d` before the selected exact rotation. This keeps the checker result independent of the
input phase and of the mathematical proof of its containment. -/
def quarterHornerResult (chain : List PhaseSquareWitness) (X : IntegerInterval) (G e d : ℤ)
    (j : Fin 4) : IntegerInterval × IntegerInterval :=
  let S :=
    phaseSquareResult ((intervalPhaseHorner G X 24 0).1.widen e)
      ((intervalPhaseHorner G X 24 0).2.widen e) chain
  quarterRotate (S.1.widen d) (S.2.widen d) j

/-- A rational small-angle center, computed Horner bounds, two checked squarings, and a bound on
the distance from the exact quarter-turn remainder enclose the original phase. The perturbation
bound includes every error in the true remainder, including uncertainty in `π`. The four-way
rotation uses a checked residue and does not access certificate lists by index. -/
theorem quarter_horner_contains (chain : List PhaseSquareWitness) (X : IntegerInterval) (G e d : ℤ)
    (q : ℚ) (x : ℝ) (k : ℤ) (j : Fin 4) (hG : 0 < G) (hq : X.Contains G (q : ℝ))
    (hd : |(q : ℝ)| ≤ 1 / 4) (he : (1 / 2 ^ 120 : ℝ) ≤ (e : ℝ) / G) (hlen : chain.length = 2)
    (hc :
      phaseSquareCheck G ((intervalPhaseHorner G X 24 0).1.widen e)
          ((intervalPhaseHorner G X 24 0).2.widen e) chain =
        true)
    (hj : k % 4 = j.val) (hdelta : |x - k * (Real.pi / 2) - 4 * (q : ℝ)| ≤ (d : ℝ) / G) :
    complexIntervalContains
      (quarterRotate
          ((phaseSquareResult ((intervalPhaseHorner G X 24 0).1.widen e)
                ((intervalPhaseHorner G X 24 0).2.widen e) chain).1.widen
            d)
          ((phaseSquareResult ((intervalPhaseHorner G X 24 0).1.widen e)
                ((intervalPhaseHorner G X 24 0).2.widen e) chain).2.widen
            d)
          j).1
      (quarterRotate
          ((phaseSquareResult ((intervalPhaseHorner G X 24 0).1.widen e)
                ((intervalPhaseHorner G X 24 0).2.widen e) chain).1.widen
            d)
          ((phaseSquareResult ((intervalPhaseHorner G X 24 0).1.widen e)
                ((intervalPhaseHorner G X 24 0).2.widen e) chain).2.widen
            d)
          j).2
      G (Complex.exp ((x : ℂ) * Complex.I)) := by
  have ht := intervalHorner25_phase q hG hq hd he
  have hs := phaseSquareCheck_sound chain G _ _ (q : ℝ) hc ht
  rw [hlen, show (2 : ℝ) ^ 2 = 4 by norm_num only] at hs
  have hr := phase_perturb_contains hs hdelta
  have hz := quarterRotate_contains _ _ G _ k j hj hr
  have hx : x = (x - k * (Real.pi / 2)) + k * (Real.pi / 2) := by rw [sub_add_cancel]
  rw [hx, exp_quarter_turn]
  exact hz

/-- A certified input phase and π interval, integer bounds around the proposed center, a small
rational Taylor argument, and two checked squarings certify the computed quarter-turn result.
The integer comparisons bound the true phase remainder, including the π interval error, and
therefore discharge the perturbation hypothesis of `quarter_horner_contains`. -/
theorem quarter_horner_checked (chain : List PhaseSquareWitness) (X A P : IntegerInterval)
    (G e d c : ℤ) (q : ℚ) (x : ℝ) (k : ℤ) (j : Fin 4) (hG : 0 < G) (hq : X.Contains G (q : ℝ))
    (hd : |(q : ℝ)| ≤ 1 / 4) (he : (1 / 2 ^ 120 : ℝ) ≤ (e : ℝ) / G) (hlen : chain.length = 2)
    (hc :
      phaseSquareCheck G ((intervalPhaseHorner G X 24 0).1.widen e)
          ((intervalPhaseHorner G X 24 0).2.widen e) chain =
        true)
    (hj : k % 4 = j.val) (hx : A.Contains G x) (hpi : P.Contains G Real.pi)
    (hcenter : 4 * (q : ℝ) = (c : ℝ) / G) (hl : c - d ≤ (quarterRemainder G k A P).lower)
    (hu : (quarterRemainder G k A P).upper ≤ c + d) :
    complexIntervalContains (quarterHornerResult chain X G e d j).1
      (quarterHornerResult chain X G e d j).2 G (Complex.exp ((x : ℂ) * Complex.I)) := by
  have hr := quarterRemainder_contains (k := k) hG hx hpi
  have hdist := interval_center_distance hG hr hl hu
  rw [← hcenter] at hdist
  exact quarter_horner_contains chain X G e d q x k j hG hq hd he hlen hc hj hdist

end PseudoPrime.Analysis
