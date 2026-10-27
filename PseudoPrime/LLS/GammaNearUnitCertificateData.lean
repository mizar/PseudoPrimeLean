/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaScaledCellCertificate

/-! # Compact rational cells for the coefficient 9999/10000 bridge -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: logarithmic endpoints, excess/dual/error/log caps and support data.
Definition: a scale-101/250 certificate with fixed rational root and pole/left bounds.
Output: generic cell data, requiring separate scalar and row checks.
Role: keep the shared constants outside the five small cell records. -/
def gammaNearUnitCertificateData (a b C D R P ellX ellE : ℚ) (K jX : ℕ) :
    GammaScaledCellCertificate :=
  { scale := 101 / 250, rootLoRatio := 1589 / 2500, rootHiRatio := 63561 / 100000, left := a,
    right := b, excess := C, dual := D, ramp := R, principal := P, pole := 187 / 100,
    leftError := 27 / 200, logX := ellX, logE := ellE, support := K, logIndexX := jX,
    logIndexE := 16 }

/-- Input: one of five cell indices. Definition: consecutive cells covering [265,290].
Output: rational certificate data; validity is proved separately.
Role: provide a compact bridge without enumerating candidate input integers. -/
def gammaNearUnitCertificate (i : Fin 5) : GammaScaledCellCertificate :=
  match i.val with
  | 0 =>
    gammaNearUnitCertificateData 265 266 (3775 / 1000) (2871 / 500) (2892 / 1000) (79 / 200)
      (10261 / 1000) (11187 / 1000) 482 15
  | 1 =>
    gammaNearUnitCertificateData 266 268 (379 / 100) (5757 / 1000) (2895 / 1000) (79 / 200)
      (2569 / 250) (5601 / 500) 485 15
  | 2 =>
    gammaNearUnitCertificateData 268 270 (3795 / 1000) (5762 / 1000) (2893 / 1000) (197 / 500)
      (10291 / 1000) (11217 / 1000) 489 15
  | 3 =>
    gammaNearUnitCertificateData 270 280 (393 / 100) (59 / 10) (2921 / 1000) (397 / 1000)
      (2591 / 250) (1129 / 100) 507 15
  | _ =>
    gammaNearUnitCertificateData 280 290 (79 / 20) (148 / 25) (2912 / 1000) (389 / 1000)
      (5217 / 500) (284 / 25) 525 15

end PseudoPrime.LLS
