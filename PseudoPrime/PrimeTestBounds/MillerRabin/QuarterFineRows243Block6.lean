/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 243, block 6 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows243Block6 : List QuarterFineWeightRow :=
  [⟨243, 179, 0, 3055, 3058, 31653, 133791, 42201479, 8347⟩,
    ⟨243, 181, 0, 2944, 2947, 31533, 134537, 42710947, 8243⟩,
    ⟨243, 191, 0, 2406, 2409, 30952, 138203, 45265958, 7749⟩,
    ⟨243, 193, 0, 2302, 2305, 30840, 138925, 45775786, 7655⟩,
    ⟨243, 197, 0, 2097, 2100, 30618, 140357, 46803373, 7473⟩,
    ⟨243, 199, 0, 1996, 1999, 30509, 141068, 47316320, 7384⟩,
    ⟨243, 211, 0, 1411, 1414, 29878, 145259, 50398190, 6879⟩,
    ⟨243, 223, 0, 857, 860, 29279, 149332, 53509289, 6421⟩,
    ⟨243, 227, 0, 680, 683, 29088, 150666, 54541139, 6278⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows243_block6_check :
    quarterFineRows243Block6.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
