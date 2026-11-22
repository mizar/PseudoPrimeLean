/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.NaturalLogWitness
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.CriticalPhaseIntervals

/-! # Checked witnesses for critical-line power terms -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

deriving instance DecidableEq for Analysis.IntegerInterval

deriving instance DecidableEq for Analysis.NaturalLogWitness

deriving instance DecidableEq for Analysis.AmplitudeWitness

/-- Data for one critical-line power term. The logarithm and amplitude witnesses describe the
positive natural base; `logBox` converts the logarithm to the common fixed-point scale. The
integer center, error radius, quarter turn, and residue describe the reduced phase. The fields
are candidates until `check` succeeds and the shared logarithm and amplitude have been certified. -/
structure CriticalTermWitness where
  log : Analysis.NaturalLogWitness
  logBox : Analysis.IntegerInterval
  amp : Analysis.AmplitudeWitness
  center : ℤ
  radius : ℤ
  turn : ℤ
  residue : Fin 4

/-- Check integer and rational phase conditions for one term at the common scale and height
interval. The independent amplitude and logarithm checks are shared separately among endpoints.
No list lookup or unverified transcendental evaluation is used. -/
def CriticalTermWitness.check (w : CriticalTermWitness) (G : ℤ) (T P : Analysis.IntegerInterval) :
    Bool :=
  decide
    (0 < w.log.base ∧
      -G ≤ w.center ∧
      w.center ≤ G ∧
      (w.logBox.lower : ℚ) ≤ w.log.lower * G ∧
      w.log.upper * G ≤ (w.logBox.upper : ℚ) ∧
      w.turn % 4 = w.residue.val ∧
      w.center - w.radius ≤
        (Analysis.quarterRemainder G w.turn (criticalPhaseArgument G T w.logBox) P).lower ∧
      (Analysis.quarterRemainder G w.turn (criticalPhaseArgument G T w.logBox) P).upper ≤
        w.center + w.radius)

/-- Compute the fixed-point rectangle for a term witness using its amplitude and quarter-turn
phase data. This is the proposed output consumed by finite-sum certificates after the witness
and shared logarithm have been verified. -/
def CriticalTermWitness.result (w : CriticalTermWitness) (G e : ℤ) :
    Analysis.IntegerInterval × Analysis.IntegerInterval :=
  criticalTermBox G w.amp.inverse
    (Analysis.quarterComputedResult (Analysis.roundedConstant G w.center (4 * G)) G e w.radius
      w.residue)

/-- A checked witness and independently certified logarithm and amplitude enclose the actual
critical-line power term. The common height and pi intervals and the Taylor error parameter
are supplied once by the endpoint. The phase side conditions come from the finite checker. -/
theorem CriticalTermWitness.sound (w : CriticalTermWitness) (G e : ℤ)
    (T P : Analysis.IntegerInterval) (t : ℝ) (hG : 0 < G) (ht : T.Contains G t)
    (hpi : P.Contains G Real.pi) (he : (1 / 2 ^ 120 : ℝ) ≤ (e : ℝ) / G)
    (hlog : (w.log.lower : ℝ) ≤ Real.log w.log.base ∧ Real.log w.log.base ≤ (w.log.upper : ℝ))
    (ha : w.amp.check G w.log.base = true) (hw : w.check G T P = true) :
    Analysis.complexIntervalContains (w.result G e).1 (w.result G e).2 G
      (dyadicPowerTerm ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) w.log.base) := by
  have ⟨hn, hc1, hc2, hll, hlu, hj, hlo, hup⟩ := of_decide_eq_true hw
  have hl := w.log.interval_contains G w.logBox hG hlog hll hlu
  exact
    criticalTerm_centered G e w.radius w.center w.turn w.log.base t w.residue T w.logBox P w.amp hG
      hn ht hl hpi hc1 hc2 he hj hlo hup ha

/-- Check a finite block of term witnesses by traversing its list once. Each entry carries its own
base, and the result does not use indexed access to list values. -/
def criticalTermFamilyCheck (data : List CriticalTermWitness) (G : ℤ)
    (T P : Analysis.IntegerInterval) : Bool :=
  data.all (fun w ↦ w.check G T P)

/-- Each member of a successfully checked block encloses its critical-line term when its shared
logarithm and amplitude are certified. Membership extracts the local Boolean check; the
individual soundness theorem supplies the corresponding mathematical enclosure. -/
theorem criticalTermFamilyCheck_sound (data : List CriticalTermWitness) (G e : ℤ)
    (T P : Analysis.IntegerInterval) (t : ℝ) (hG : 0 < G) (ht : T.Contains G t)
    (hpi : P.Contains G Real.pi) (he : (1 / 2 ^ 120 : ℝ) ≤ (e : ℝ) / G)
    (hdata : criticalTermFamilyCheck data G T P = true) {w : CriticalTermWitness} (hw : w ∈ data)
    (hlog : (w.log.lower : ℝ) ≤ Real.log w.log.base ∧ Real.log w.log.base ≤ (w.log.upper : ℝ))
    (ha : w.amp.check G w.log.base = true) :
    Analysis.complexIntervalContains (w.result G e).1 (w.result G e).2 G
      (dyadicPowerTerm ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) w.log.base) := by
  exact w.sound G e T P t hG ht hpi he hlog ha ((List.all_eq_true.mp hdata) w hw)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
