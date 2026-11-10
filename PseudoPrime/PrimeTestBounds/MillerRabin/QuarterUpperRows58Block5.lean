/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Upper principal rows at cutoff 58, block 5 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterUpperRows58Block5 : List QuarterUpperWeightRow :=
  [⟨58, 571, 3, 2285, 2288, 363, 368, 23895, 1437635856, 2⟩,
    ⟨58, 577, 3, 2296, 2299, 352, 356, 24020, 1421908519, 2⟩,
    ⟨58, 587, 3, 2313, 2316, 333, 337, 24228, 1395147295, 2⟩,
    ⟨58, 593, 3, 2323, 2326, 322, 327, 24351, 1379884773, 1⟩,
    ⟨58, 599, 3, 2333, 2336, 312, 316, 24474, 1366154692, 1⟩,
    ⟨58, 601, 3, 2337, 2340, 307, 312, 24515, 1359340964, 1⟩,
    ⟨58, 607, 3, 2347, 2350, 297, 301, 24637, 1345815297, 1⟩,
    ⟨58, 613, 3, 2356, 2359, 287, 291, 24758, 1332424210, 1⟩,
    ⟨58, 617, 3, 2363, 2366, 279, 283, 24839, 1321807341, 1⟩,
    ⟨58, 619, 3, 2366, 2369, 276, 280, 24879, 1317847861, 1⟩,
    ⟨58, 625, 3, 2376, 2379, 265, 269, 25000, 1303430973, 1⟩,
    ⟨58, 631, 3, 2385, 2388, 255, 260, 25119, 1290461618, 1⟩,
    ⟨58, 641, 3, 2401, 2404, 238, 242, 25317, 1268709190, 1⟩,
    ⟨58, 643, 3, 2404, 2407, 235, 239, 25357, 1264908766, 1⟩,
    ⟨58, 647, 3, 2410, 2413, 228, 233, 25436, 1256085324, 1⟩,
    ⟨58, 653, 3, 2420, 2423, 218, 222, 25553, 1243587065, 1⟩,
    ⟨58, 659, 4, 2429, 2432, 208, 212, 25670, 1231213167, 1⟩,
    ⟨58, 661, 4, 2432, 2435, 205, 209, 25709, 1227525064, 1⟩,
    ⟨58, 673, 4, 2450, 2453, 185, 189, 25942, 1203218437, 1⟩,
    ⟨58, 677, 4, 2456, 2459, 179, 183, 26019, 1196020742, 1⟩,
    ⟨58, 683, 4, 2465, 2468, 169, 173, 26134, 1184120136, 1⟩,
    ⟨58, 691, 4, 2476, 2479, 157, 161, 26286, 1169995611, 1⟩,
    ⟨58, 701, 4, 2491, 2494, 141, 145, 26476, 1151424645, 1⟩,
    ⟨58, 709, 4, 2502, 2505, 129, 133, 26627, 1137690122, 1⟩,
    ⟨58, 719, 4, 2516, 2519, 114, 118, 26814, 1120752124, 1⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_upper_rows58_block5_check :
    quarterUpperRows58Block5.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
