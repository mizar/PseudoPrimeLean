/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaMixedEulerBounds

public import PseudoPrime.LLS.GammaEnvelopePrimeRows

/-! # Compact computed mixed-Euler row certificates for quadratic profile cells -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: a rational q. Definition: ceil(10^6 q)/10^6. Output: an outer grid rounding.
Role: keep rational row allowances on common denominators for cheap finite sums. -/
def gammaCellGridCeil (q : ℚ) : ℚ :=
  (⌈q * 1000000⌉ : ℤ) / 1000000

/-- Input: logarithmic endpoints a,b. Definition: scales (2/5)a^2,(2/5)b^2 and
rational root enclosures (79/125)a,(633/1000)b, with theta=5/4.
Output: common cell data; validity is checked before use. Role: profile interval certificates. -/
def gammaProfileEnvelopeCell (a b : ℚ) : GammaLocalCellData :=
  { lo := (2 / 5) * a ^ 2, hi := (2 / 5) * b ^ 2, rootLo := (79 / 125) * a,
    rootHi := (633 / 1000) * b, theta := 5 / 4 }

/-- Input: a common cell and prime p. Definition: natural power cutoff, twenty-term
exponential/logarithm enclosures and outward-rounded cost and excess endpoints.
Output: finite row data. Role: compute compact certificates without long row payloads. -/
def gammaProfileEnvelopeRow (c : GammaLocalCellData) (p : ℕ) : GammaLocalPrimeRow :=
  let N := Nat.log p ⌈(99 / 40 : ℚ) * c.hi⌉₊
  let R := gammaCellGridCeil (gammaSignedRampPrefixUpper p N c.lo c.hi 20)
  let C := gammaCellGridCeil (Analysis.gammaMixedEulerUpper p + max R 0 / c.rootLo)
  { prime := p, logScale := Nat.log2 p + 1, logTerms := 20, logLower := 0,
    logUpper := gammaCellGridCeil (Analysis.rationalLogUpper p (Nat.log2 p + 1) 20),
    ratios := Analysis.gammaMixedEulerRatios p, powers := N, expTerms := 20,
    eulerUpper := Analysis.gammaMixedEulerUpper p, rampUpper := R, costUpper := C,
    excessUpper := gammaCellGridCeil (max (C - c.theta / c.rootHi) 0) }

/-- Claim: the profile cell [300,310] satisfies all sign and root conditions.
Proof: kernel rational arithmetic. Role: validate its common numerical invariants. -/
theorem gamma_profile_cell_300_310_check : (gammaProfileEnvelopeCell 300 310).check = true := by
  decide +kernel

/-- Claim: every prime row from 3 through 559 passes the analytic-envelope row check.
Proof: kernel logarithm, tail and Taylor arithmetic. Role: certify the entire scale cell. -/
theorem gamma_profile_rows_300_310_check :
    ∀ p ∈ (Finset.Icc 3 559).filter Nat.Prime,
      (gammaProfileEnvelopeRow (gammaProfileEnvelopeCell 300 310) p).envelopeCheck
          (gammaProfileEnvelopeCell 300 310) =
        true := by
  decide +kernel

/-- Claim: all row allowances in the support cell sum to at most 47/10.
Proof: exact rational kernel arithmetic. Role: provide the finite dual-excess cap. -/
theorem gamma_profile_sum_300_310_check :
    (∑ p ∈ (Finset.Icc 3 559).filter Nat.Prime,
        (gammaProfileEnvelopeRow (gammaProfileEnvelopeCell 300 310) p).allowance) ≤
      (47 / 10 : ℚ) := by
  decide +kernel

end PseudoPrime.LLS
