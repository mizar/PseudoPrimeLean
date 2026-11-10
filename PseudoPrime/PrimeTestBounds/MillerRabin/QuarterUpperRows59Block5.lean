/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Upper principal rows at cutoff 59, block 5 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterUpperRows59Block5 : List QuarterUpperWeightRow :=
  [⟨59, 571, 3, 2268, 2271, 382, 386, 23895, 1465212082, 3⟩,
    ⟨59, 577, 3, 2279, 2282, 370, 374, 24020, 1447734611, 2⟩,
    ⟨59, 587, 3, 2296, 2299, 352, 356, 24228, 1421908519, 2⟩,
    ⟨59, 593, 3, 2306, 2309, 341, 345, 24351, 1406353237, 2⟩,
    ⟨59, 599, 3, 2316, 2319, 330, 334, 24474, 1390968125, 2⟩,
    ⟨59, 601, 3, 2320, 2323, 326, 330, 24515, 1385415366, 1⟩,
    ⟨59, 607, 3, 2329, 2332, 316, 320, 24637, 1371630252, 1⟩,
    ⟨59, 613, 3, 2339, 2342, 305, 309, 24758, 1356624999, 1⟩,
    ⟨59, 617, 3, 2346, 2349, 298, 302, 24839, 1347161784, 1⟩,
    ⟨59, 619, 3, 2349, 2352, 294, 299, 24879, 1341783901, 1⟩,
    ⟨59, 625, 3, 2359, 2362, 284, 288, 25000, 1328432928, 1⟩,
    ⟨59, 631, 3, 2368, 2371, 274, 278, 25119, 1315214798, 1⟩,
    ⟨59, 641, 3, 2384, 2387, 257, 261, 25317, 1293045123, 1⟩,
    ⟨59, 643, 3, 2387, 2390, 253, 258, 25357, 1287883275, 1⟩,
    ⟨59, 647, 3, 2393, 2396, 247, 251, 25436, 1280179111, 1⟩,
    ⟨59, 653, 3, 2403, 2406, 236, 240, 25553, 1266174307, 1⟩,
    ⟨59, 659, 3, 2412, 2415, 226, 231, 25670, 1253575663, 1⟩,
    ⟨59, 661, 3, 2415, 2418, 223, 227, 25709, 1249820571, 1⟩,
    ⟨59, 673, 4, 2433, 2436, 204, 208, 25942, 1226298152, 1⟩,
    ⟨59, 677, 4, 2439, 2442, 197, 201, 26019, 1217744038, 1⟩,
    ⟨59, 683, 4, 2447, 2450, 189, 193, 26134, 1208040950, 1⟩,
    ⟨59, 691, 4, 2459, 2462, 176, 180, 26286, 1192438057, 1⟩,
    ⟨59, 701, 4, 2473, 2476, 160, 165, 26476, 1173510868, 1⟩,
    ⟨59, 709, 4, 2485, 2488, 147, 152, 26627, 1158353962, 1⟩,
    ⟨59, 719, 4, 2499, 2502, 132, 137, 26814, 1141108317, 1⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_upper_rows59_block5_check :
    quarterUpperRows59Block5.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
