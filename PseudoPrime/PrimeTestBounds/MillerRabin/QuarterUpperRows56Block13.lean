/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Principal upper rows at cutoff 56, block 13 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper-weight certificates for a block of prime powers. -/
def quarterUpperRows56Block13 : List QuarterUpperWeightRow :=
  [⟨56, 601, 3, 2372, 2375, 270, 274, 24515, 1309964448, 1⟩,
    ⟨56, 607, 3, 2382, 2385, 259, 263, 24637, 1295633803, 1⟩,
    ⟨56, 613, 3, 2392, 2395, 248, 252, 24758, 1281459930, 1⟩,
    ⟨56, 617, 3, 2398, 2401, 241, 246, 24839, 1272521033, 1⟩,
    ⟨56, 619, 3, 2401, 2404, 238, 242, 24879, 1268709190, 1⟩,
    ⟨56, 625, 3, 2411, 2414, 227, 232, 25000, 1254829864, 1⟩,
    ⟨56, 631, 3, 2420, 2423, 218, 222, 25119, 1243587065, 1⟩,
    ⟨56, 641, 4, 2436, 2439, 200, 205, 25317, 1221402755, 1⟩,
    ⟨56, 643, 4, 2439, 2442, 197, 201, 25357, 1217744038, 1⟩,
    ⟨56, 647, 4, 2445, 2448, 191, 195, 25436, 1210459449, 1⟩]

/-- Each listed row satisfies the rational upper-weight checks. -/
theorem quarter_upper_rows56_block13_check :
    quarterUpperRows56Block13.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
