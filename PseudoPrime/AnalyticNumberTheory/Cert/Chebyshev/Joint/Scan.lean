/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.PowerLookup
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.Segment
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.SegmentSieve

/-! # Integer replay for joint prime and prime-power batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- The fixed-point scale used for every logarithm tick in a joint batch. -/
def scale : Nat :=
  10 ^ 12

/-- Enclose a prime logarithm using its binary exponent, a width-32 table and
the first two polynomial bounds for the residual logarithm. Returns integer ticks. -/
def primeTicks (table : Nat → Nat × Nat) (ln2 : Nat × Nat) (p : Nat) : Nat × Nat :=
  let k := p.log2
  let pow := 2 ^ k
  let j := (32 * p) / pow
  let r := (32 * p) % pow
  let d := j * pow
  let t := table (j - 32)
  (t.1 + k * ln2.1 + scale * r * (2 * d - r) / (2 * d * d),
    t.2 + k * ln2.2 + (scale * r + d - 1) / d)

/-- Test a one-sided square-root estimate after clearing the positive
denominator. Natural subtraction at the caller supplies the positive part. -/
def within (error x u v : Nat) : Bool :=
  decide ((v * error) ^ 2 ≤ x * (scale * u) ^ 2)

/-- Check the two psi inequalities on a cell and, from 2657, one of the
two theta lower inequalities. Inputs are the ticks at its two interior ends. -/
def cellCheck (a b u v pl tl ph dh : Nat) : Bool :=
  let (tu, tv) := if a < 3100 then (9, 5) else if a < 3500 then (19, 10) else (97, 50)
  within (ph - scale * a) a u v && within (scale * b - pl) b u v &&
    (a < 2657 || within dh a (5 * tu - 4 * tv) (5 * tv) || within (scale * b - tl) b tu tv)

/-- Consume the integer at the edge. A zero marker leaves all ticks unchanged;
a nonzero prime base adds its ticks to psi and, at a higher power, to the defect. -/
def advance (ticks : Nat → Nat × Nat) (s : Edge) (p : Nat) : Edge :=
  if p = 0 then { s with n := s.n + 1 }
  else
    let t := ticks p
    if p = s.n then ⟨s.n + 1, s.psiLo + t.1, s.psiHi + t.2, s.powerLo, s.powerHi⟩
    else ⟨s.n + 1, s.psiLo + t.1, s.psiHi + t.2, s.powerLo + t.1, s.powerHi + t.2⟩

/-- One pass updates the four tick sums, checks cell widths and guards, and
compares the exact outgoing state. The warm-up segment ends at eleven. -/
def batchCheck (bases : Array Nat) (ticks : Nat → Nat × Nat) (coef : Nat → Nat × Nat) (s t : Edge)
    (widths : Array Nat) : Bool :=
  Id.run do
    let flags := sieve s.n t.n bases
    let powers := lookupPower (powerEntries bases) s.n t.n
    let mut state := s
    let mut cell := s.n
    let mut i := 0
    let mut lower := 0
    let mut theta := 0
    for n in [s.n:t.n] do
      let p := if (flags[n - s.n]?).getD false then n else powers n
      state := advance ticks state p
      if n < 11 then
        continue
      if n == 2657 || n == 3100 || n == 3500 then
        let (u, v) := if n ≤ 3100 then (9, 5) else (19, 10)
        if !within (scale * n - (state.psiLo - state.powerLo)) n u v then
          return false
      if n == cell then
        lower := state.psiLo
        theta := state.psiLo - state.powerLo
      let some w := widths[i]? | return false
      if w == 0 then
        return false
      if n + 1 == cell + w then
        let c := coef cell
        if
            c.1 == 0 || c.2 == 0 ||
              !cellCheck cell (n + 1) c.1 c.2 lower theta state.psiHi state.powerHi then
          return false
        i := i + 1
        cell := n + 1
    return s.n < t.n && (t.n ≤ 11 || cell == t.n) && i == widths.size && state.n == t.n &&
        state.psiLo == t.psiLo &&
        state.psiHi == t.psiHi &&
        state.powerLo == t.powerLo &&
        state.powerHi == t.powerHi

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
