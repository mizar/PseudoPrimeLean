/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaSignedPrincipalEntranceCertificates
public import PseudoPrime.LLS.GammaQuadraticPolynomialSeparation
public import PseudoPrime.LLS.GammaLowerWindowBounds
public import PseudoPrime.Analysis.GammaWindowRationalCaps

/-! # Reusing the log-260 rows below their old left endpoint -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Definition: the already certified local cell for log levels 260 to 261.
Role: reuse every local logarithm and Euler/ramp certificate unchanged. -/
def gammaTransportedOldCell : Analysis.GammaLocalCellData :=
  (gammaSignedPrincipalEntranceCertificate 0).cell

/-- Definition: the new left scale (101/250)(2591/10)^2. Role: extend the old cell downward. -/
def gammaTransportedNewLo : ℚ :=
  (101 / 250) * (2591 / 10) ^ 2

/-- Definition: a rational lower root at the new scale. Role: check signed allowances. -/
def gammaTransportedNewRootLo : ℚ :=
  (1589 / 2500) * (2591 / 10)

/-- Definition: the base-sensitive analytic left-endpoint correction.
Role: reuse old signed ramp caps. -/
def gammaTransportedDelta (p : ℕ) : ℚ :=
  (((p : ℚ) + 1) / (p - 1)) * (gammaTransportedOldCell.lo - gammaTransportedNewLo) /
    gammaTransportedNewLo

/-- Input: a prime candidate. Definition: the unchanged old adaptive row.
Role: avoid storing any new prime-specific numerical data. -/
def gammaTransportedRow (p : ℕ) : Analysis.GammaLocalPrimeRow :=
  Analysis.gammaAdaptiveProfileRow gammaTransportedOldCell p

/-- Input: a prime candidate. Definition: its rational weighted window allowance.
Role: sum only the old row data with its base-sensitive analytic correction. -/
def gammaTransportedAllowance (p : ℕ) : ℚ :=
  let r := gammaTransportedRow p
  let N := r.rampUpper - 5 / 4 + gammaTransportedDelta p
  r.logUpper *
    max (r.eulerUpper + max (N / gammaTransportedNewRootLo) (N / gammaTransportedOldCell.rootHi)) 0

/-- Definition: sum over odd primes through 350. Role: one compact aggregate
check; no new per-prime certificates or input-integer search are involved. -/
def gammaTransportedAllowanceSum : ℚ :=
  ∑ p ∈ (Finset.Icc 3 350).filter Nat.Prime, gammaTransportedAllowance p

/-- Claim: the transported aggregate is at most 377/100.
Use kernel rational arithmetic on the unchanged row factories.
Role: provide the numerical excess cap for the lower entrance. -/
theorem gamma_transported_allowance_sum_le : gammaTransportedAllowanceSum ≤ 377 / 100 := by
  decide +kernel

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Input: logarithmic level L. Definition: prefix 28493/5000 minus half
of the transported local-cost cap. Role: supply the common polynomial criterion. -/
noncomputable def gammaTransportedCredit (L : ℝ) : ℝ :=
  28493 / 5000 -
    (3 / 4 + ((5 / (4 * ((1589 / 2500 : ℝ) * (2591 / 10)))) * L + 377 / 100) + 7 / 60) / 2

/-- Input: L >= 2591/10. Claim: the shared polynomial condition holds at the
scale (101/250)L^2 with the transported credit. Use a short log certificate,
the tangent inequality and a rational quadratic. Role: close the continuous
separation without adding scale-specific local rows. -/
theorem gamma_transported_polynomial_condition {L : ℝ} (hL : 2591 / 10 ≤ L) :
    GammaPairedPolynomialCondition (L + 7 / 5) ((101 / 250 : ℝ) * L ^ 2)
      (gammaTransportedCredit L) := by
  have hL0 : 0 < L := by linarith only [hL]
  have hr : Real.sqrt ((101 / 250 : ℝ) * L ^ 2) ≤ (63561 / 100000 : ℝ) * L := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by linarith only [hL], by nlinarith only [sq_nonneg L]⟩
  have hc : Analysis.rationalLogIntervalCheck 260 9 16 5 (55607 / 10000) = true := by decide +kernel
  have hl := (Analysis.rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
  have ht := Analysis.log_le_log_add_sub_div (by norm_num only : (0 : ℝ) < 260) hL0
  have hlL : Real.log L ≤ (L - 260) / 260 + 55607 / 10000 := by linarith only [hl, ht]
  have hlog : Real.log ((101 / 40 : ℝ) * ((101 / 250 : ℝ) * L ^ 2)) ≤ L / 130 + 18283 / 2000 := by
    rw [show (101 / 40 : ℝ) * ((101 / 250 : ℝ) * L ^ 2) = (10201 / 10000 : ℝ) * L ^ 2 by ring,
      Real.log_mul (by norm_num only) (sq_pos_of_pos hL0).ne', Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    have he := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 10201 / 10000)
    linarith only [hlL, he]
  refine ⟨(63561 / 100000 : ℝ) * L, L / 130 + 18283 / 2000, hr, hlog, ?_, ?_⟩
  · dsimp only [gammaTransportedCredit]
    linarith only [hL]
  · dsimp only [gammaTransportedCredit]
    nlinarith only [hL, sq_nonneg (L - 2591 / 10)]

end PseudoPrime.LLS
