/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaNearUnitCertificateData
public import PseudoPrime.LLS.GammaPrefixCellCertificate

/-! # Compact nearly-unit certificates covering logarithmic scales 264 to 265 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: endpoints and rational cell allowances.
Definition: reuse the nearly-unit scale with left-error cap 17/125.
Output: prefix-aware certificate data. Role: cover the interval from 264 to 265. -/
def gammaLog264Cell (a b C D R P ellX ellE : ℚ) : GammaScaledCellCertificate :=
  { gammaNearUnitCertificateData a b C D R P ellX ellE 480 15 with leftError := 17 / 125 }

/-- Input: one of three indices. Definition: adjacent cells covering [264,265].
Output: compact rational data. Role: avoid enumerating the arithmetic input n. -/
def gammaLog264Certificate (i : Fin 3) : GammaScaledCellCertificate :=
  match i.val with
  | 0 =>
    gammaLog264Cell 264 (1057 / 4) (3767 / 1000) (5734 / 1000) (2890 / 1000) (396 / 1000)
      (10248 / 1000) (11174 / 1000)
  | 1 =>
    gammaLog264Cell (1057 / 4) (529 / 2) (3767 / 1000) (5734 / 1000) (2890 / 1000) (396 / 1000)
      (10250 / 1000) (11176 / 1000)
  | _ =>
    gammaLog264Cell (529 / 2) 265 (3771 / 1000) (5738 / 1000) (2891 / 1000) (396 / 1000)
      (10254 / 1000) (11180 / 1000)

/-- Claim: cell 0 passes the scalar, supported-row and allowance-sum checks.
Proof: exact kernel computation.
Role: keep each finite certificate within default resource limits. -/
private theorem gamma_log264_check_0 :
    (gammaLog264Certificate 0).prefixScalarCheck (28493 / 5000) = true ∧
      (∀ p ∈ (Finset.Icc 3 (gammaLog264Certificate 0).support).filter Nat.Prime,
        (Analysis.gammaAdaptiveProfileRow (gammaLog264Certificate 0).cell p).envelopeCheck
            (gammaLog264Certificate 0).cell =
          true) ∧
      (∑ p ∈ (Finset.Icc 3 (gammaLog264Certificate 0).support).filter Nat.Prime,
          (Analysis.gammaAdaptiveProfileRow (gammaLog264Certificate 0).cell p).allowance) ≤
        (gammaLog264Certificate 0).excess := by
  decide +kernel

/-- Claim: cell 1 passes the scalar, supported-row and allowance-sum checks.
Proof: exact kernel computation.
Role: keep each finite certificate within default resource limits. -/
private theorem gamma_log264_check_1 :
    (gammaLog264Certificate 1).prefixScalarCheck (28493 / 5000) = true ∧
      (∀ p ∈ (Finset.Icc 3 (gammaLog264Certificate 1).support).filter Nat.Prime,
        (Analysis.gammaAdaptiveProfileRow (gammaLog264Certificate 1).cell p).envelopeCheck
            (gammaLog264Certificate 1).cell =
          true) ∧
      (∑ p ∈ (Finset.Icc 3 (gammaLog264Certificate 1).support).filter Nat.Prime,
          (Analysis.gammaAdaptiveProfileRow (gammaLog264Certificate 1).cell p).allowance) ≤
        (gammaLog264Certificate 1).excess := by
  decide +kernel

/-- Claim: cell 2 passes the scalar, supported-row and allowance-sum checks.
Proof: exact kernel computation.
Role: keep each finite certificate within default resource limits. -/
private theorem gamma_log264_check_2 :
    (gammaLog264Certificate 2).prefixScalarCheck (28493 / 5000) = true ∧
      (∀ p ∈ (Finset.Icc 3 (gammaLog264Certificate 2).support).filter Nat.Prime,
        (Analysis.gammaAdaptiveProfileRow (gammaLog264Certificate 2).cell p).envelopeCheck
            (gammaLog264Certificate 2).cell =
          true) ∧
      (∑ p ∈ (Finset.Icc 3 (gammaLog264Certificate 2).support).filter Nat.Prime,
          (Analysis.gammaAdaptiveProfileRow (gammaLog264Certificate 2).cell p).allowance) ≤
        (gammaLog264Certificate 2).excess := by
  decide +kernel

/-- Input: a cell index. Claim: all three certificate obligations hold.
Proof: combine the three separately checked cells.
Role: supply numerical data to the prefix-parametric analytic transfer. -/
theorem gamma_log264_certificates_check (i : Fin 3) :
    (gammaLog264Certificate i).prefixScalarCheck (28493 / 5000) = true ∧
      (∀ p ∈ (Finset.Icc 3 (gammaLog264Certificate i).support).filter Nat.Prime,
        (Analysis.gammaAdaptiveProfileRow (gammaLog264Certificate i).cell p).envelopeCheck
            (gammaLog264Certificate i).cell =
          true) ∧
      (∑ p ∈ (Finset.Icc 3 (gammaLog264Certificate i).support).filter Nat.Prime,
          (Analysis.gammaAdaptiveProfileRow (gammaLog264Certificate i).cell p).allowance) ≤
        (gammaLog264Certificate i).excess := by
  fin_cases i
  · exact gamma_log264_check_0
  · exact gamma_log264_check_1
  · exact gamma_log264_check_2

end PseudoPrime.LLS
