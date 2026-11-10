/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 243, block 3 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows243Block3 : List QuarterFineWeightRow :=
  [⟨243, 67, 2, 12882, 12885, 42266, 81854, 14601952, 20043⟩,
    ⟨243, 71, 2, 12302, 12305, 41640, 84262, 15545252, 19237⟩,
    ⟨243, 73, 2, 12025, 12028, 41341, 85441, 16017074, 18855⟩,
    ⟨243, 79, 2, 11235, 11238, 40488, 88882, 17443294, 17784⟩,
    ⟨243, 81, 2, 10985, 10988, 40218, 90000, 17920678, 17450⟩,
    ⟨243, 83, 2, 10741, 10744, 39954, 91105, 18400084, 17127⟩,
    ⟨243, 89, 1, 10043, 10046, 39200, 94340, 19841094, 16215⟩,
    ⟨243, 97, 1, 9182, 9185, 38270, 98489, 21774842, 15117⟩,
    ⟨243, 101, 1, 8778, 8781, 37834, 100499, 22745226, 14613⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows243_block3_check :
    quarterFineRows243Block3.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
