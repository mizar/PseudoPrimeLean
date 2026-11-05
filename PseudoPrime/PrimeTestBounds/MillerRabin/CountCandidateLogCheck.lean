/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.HighPrecisionLogBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeCandidateEnvelope

/-! # Repeated-product candidate logarithm certificates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A repeated-product candidate and the binary scales used to certify its logarithms.
The scales normalize the prime cutoff and the multichoose count for the Taylor checker.
The candidate itself stores the prime supply, degree and desired rational endpoints. -/
structure CandidateLogData where
  /-- The candidate with its rational product-size and multichoose endpoints. -/
  candidate : SemiprimeCandidate
  /-- Binary scale for the prime cutoff. -/
  boundScale : ℕ
  /-- Binary scale for the multichoose count. -/
  countScale : ℕ

/-- Check both logarithm endpoints of a candidate, using 64 Taylor terms and a positive
`10⁻¹⁸` margin at the multichoose lower endpoint. The positive degree and both Taylor
interval certificates are checked by rational computation. -/
def CandidateLogData.check (d : CandidateLogData) : Bool :=
  decide
    (0 < d.candidate.degree ∧
      Analysis.fineLogCheck d.candidate.bound d.boundScale 64 0
          (d.candidate.upper / d.candidate.degree) =
        true ∧
      Analysis.fineLogCheck (Nat.choose (d.candidate.count + d.candidate.degree) d.candidate.degree)
          d.countScale 64 (d.candidate.lower + 1 / 1000000000000000000) (d.candidate.lower + 1) =
        true)

/-- A successful check proves the product-size upper bound and a strict multichoose
lower bound. Transfer the two Taylor intervals to the reals and multiply by the positive
degree. These are the logarithmic hypotheses for both square and semiprime counting. -/
theorem CandidateLogData.sound (d : CandidateLogData) (h : d.check = true) :
    (d.candidate.degree : ℝ) * Real.log d.candidate.bound ≤ d.candidate.upper ∧
      (d.candidate.lower : ℝ) <
        Real.log (Nat.choose (d.candidate.count + d.candidate.degree) d.candidate.degree : ℝ) := by
  have hc :
    0 < d.candidate.degree ∧
      Analysis.fineLogCheck d.candidate.bound d.boundScale 64 0
          (d.candidate.upper / d.candidate.degree) =
        true ∧
      Analysis.fineLogCheck (Nat.choose (d.candidate.count + d.candidate.degree) d.candidate.degree)
          d.countScale 64 (d.candidate.lower + 1 / 1000000000000000000) (d.candidate.lower + 1) =
        true :=
    of_decide_eq_true h
  have hb := (Analysis.fineLogCheck_sound hc.2.1).2
  have hl := (Analysis.fineLogCheck_sound hc.2.2).1
  simp only [Rat.cast_natCast, Rat.cast_div] at hb
  simp only [Rat.cast_natCast, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at hl
  have hd : (0 : ℝ) < d.candidate.degree := Nat.cast_pos.mpr hc.1
  constructor
  · have hmul := (le_div_iff₀ hd).mp hb
    simpa only [mul_comm] using hmul
  · linarith only [hl]

end PseudoPrime.PrimeTestBounds.MillerRabin
