/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Principal upper rows at cutoff 56, block 6 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper-weight certificates for a block of prime powers. -/
def quarterUpperRows56Block6 : List QuarterUpperWeightRow :=
  [⟨56, 211, 2, 1325, 1328, 1400, 1404, 14525, 4055199960, 772⟩,
    ⟨56, 223, 2, 1380, 1383, 1341, 1345, 14933, 3822864451, 643⟩,
    ⟨56, 227, 2, 1398, 1401, 1321, 1326, 15066, 3747166664, 606⟩,
    ⟨56, 229, 2, 1407, 1410, 1312, 1316, 15132, 3713593469, 586⟩,
    ⟨56, 233, 2, 1424, 1427, 1293, 1298, 15264, 3643701274, 553⟩,
    ⟨56, 239, 2, 1450, 1453, 1265, 1269, 15459, 3543092730, 501⟩,
    ⟨56, 241, 2, 1458, 1461, 1257, 1261, 15524, 3514861064, 487⟩,
    ⟨56, 243, 2, 1466, 1469, 1248, 1252, 15588, 3483369240, 473⟩,
    ⟨56, 251, 2, 1499, 1502, 1212, 1217, 15842, 3360198328, 418⟩,
    ⟨56, 256, 2, 1518, 1521, 1192, 1196, 16000, 3293661942, 387⟩]

/-- Each listed row satisfies the rational upper-weight checks. -/
theorem quarter_upper_rows56_block6_check :
    quarterUpperRows56Block6.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
