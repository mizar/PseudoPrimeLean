/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Principal upper rows at cutoff 56, block 7 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper-weight certificates for a block of prime powers. -/
def quarterUpperRows56Block7 : List QuarterUpperWeightRow :=
  [⟨56, 257, 2, 1522, 1525, 1188, 1192, 16031, 3280513610, 382⟩,
    ⟨56, 263, 2, 1545, 1548, 1163, 1167, 16217, 3199517438, 348⟩,
    ⟨56, 269, 2, 1568, 1571, 1138, 1142, 16401, 3120521069, 317⟩,
    ⟨56, 271, 2, 1575, 1578, 1130, 1134, 16462, 3095656495, 307⟩,
    ⟨56, 277, 2, 1597, 1600, 1107, 1111, 16643, 3025268956, 281⟩,
    ⟨56, 281, 2, 1612, 1615, 1090, 1095, 16763, 2974274067, 264⟩,
    ⟨56, 283, 2, 1619, 1622, 1083, 1087, 16822, 2953526849, 255⟩,
    ⟨56, 289, 2, 1640, 1643, 1060, 1064, 17000, 2886370983, 232⟩,
    ⟨56, 293, 2, 1653, 1656, 1046, 1050, 17117, 2846243338, 219⟩,
    ⟨56, 307, 2, 1700, 1703, 995, 999, 17521, 2704724335, 175⟩]

/-- Each listed row satisfies the rational upper-weight checks. -/
theorem quarter_upper_rows56_block7_check :
    quarterUpperRows56Block7.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
