/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.CriticalTermWitness

/-! # Compact reconstruction of critical-line term witnesses -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Endpoint-specific phase data for one base. The center and radius are integer ticks, while
the quarter turn and its residue select the exact rotation. Logarithm and amplitude witnesses
are supplied separately so that they can be shared by many endpoint certificates. -/
structure CompactPhaseWitness where
  center : ℤ
  radius : ℤ
  turn : ℤ
  residue : Fin 4

/-- Compute a fixed-point rectangle from the rational endpoints of a logarithm witness.
Rational floor and ceiling round outward at scale `G`. The usual witness checker verifies the
resulting endpoint inequalities before the interval is used in a phase certificate. -/
def compactLogBox (G : ℤ) (w : Analysis.NaturalLogWitness) : Analysis.IntegerInterval :=
  ⟨Rat.floor (w.lower * G), Rat.ceil (w.upper * G)⟩

/-- Reconstruct a complete term witness from a shared logarithm and amplitude witness and
endpoint-specific compact phase data. The logarithm rectangle is computed from the shared
rational bounds, so it does not need to be stored separately for every endpoint. -/
def compactTermWitness (G : ℤ) (log : Analysis.NaturalLogWitness) (amp : Analysis.AmplitudeWitness)
    (phase : CompactPhaseWitness) : CriticalTermWitness :=
  ⟨log, compactLogBox G log, amp, phase.center, phase.radius, phase.turn, phase.residue⟩

/-- Traverse logarithm, amplitude, and phase lists together to reconstruct a block of term
witnesses. The amplitude list carries its natural base alongside its witness; consistency and
full coverage are checked separately by the consumer. No list element is selected by index. -/
def compactTermFamily (G : ℤ) (logs : List Analysis.NaturalLogWitness)
    (amps : List (ℕ × Analysis.AmplitudeWitness)) (phases : List CompactPhaseWitness) :
    List CriticalTermWitness :=
  ((logs.zip amps).zip phases).map fun p ↦ compactTermWitness G p.1.1 p.1.2.2 p.2

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
