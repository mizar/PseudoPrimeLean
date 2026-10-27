/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.Phase64EndpointCertificates.Data

/-! # Principal endpoint kernel blocks 0 through 7 -/

@[expose] public section

namespace PseudoPrime.Analysis.Phase64EndpointCertificates

/-- Kernel verification of principal block 0: logarithm gates and the
outward upper natural sum. No floating-point values or external computation are trusted. -/
theorem principal_block00 : PrincipalBlockValid 0 := by
  unfold PrincipalBlockValid
  decide +kernel

/-- Kernel verification of principal block 1: logarithm gates and the
outward upper natural sum. No floating-point values or external computation are trusted. -/
theorem principal_block01 : PrincipalBlockValid 1 := by
  unfold PrincipalBlockValid
  decide +kernel

/-- Kernel verification of principal block 2: logarithm gates and the
outward upper natural sum. No floating-point values or external computation are trusted. -/
theorem principal_block02 : PrincipalBlockValid 2 := by
  unfold PrincipalBlockValid
  decide +kernel

/-- Kernel verification of principal block 3: logarithm gates and the
outward upper natural sum. No floating-point values or external computation are trusted. -/
theorem principal_block03 : PrincipalBlockValid 3 := by
  unfold PrincipalBlockValid
  decide +kernel

/-- Kernel verification of principal block 4: logarithm gates and the
outward upper natural sum. No floating-point values or external computation are trusted. -/
theorem principal_block04 : PrincipalBlockValid 4 := by
  unfold PrincipalBlockValid
  decide +kernel

/-- Kernel verification of principal block 5: logarithm gates and the
outward upper natural sum. No floating-point values or external computation are trusted. -/
theorem principal_block05 : PrincipalBlockValid 5 := by
  unfold PrincipalBlockValid
  decide +kernel

/-- Kernel verification of principal block 6: logarithm gates and the
outward upper natural sum. No floating-point values or external computation are trusted. -/
theorem principal_block06 : PrincipalBlockValid 6 := by
  unfold PrincipalBlockValid
  decide +kernel

/-- Kernel verification of principal block 7: logarithm gates and the
outward upper natural sum. No floating-point values or external computation are trusted. -/
theorem principal_block07 : PrincipalBlockValid 7 := by
  unfold PrincipalBlockValid
  decide +kernel

end PseudoPrime.Analysis.Phase64EndpointCertificates
