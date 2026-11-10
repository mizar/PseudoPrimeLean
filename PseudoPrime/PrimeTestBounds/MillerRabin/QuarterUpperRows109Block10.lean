/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Upper principal rows at cutoff 109, block 10 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterUpperRows109Block10 : List QuarterUpperWeightRow :=
  [⟨109, 1409, 4, 2558, 2561, 69, 73, 37536, 1071436208, 1⟩,
    ⟨109, 1423, 4, 2568, 2571, 58, 62, 37722, 1059714994, 1⟩,
    ⟨109, 1427, 4, 2570, 2573, 56, 60, 37775, 1057597682, 1⟩,
    ⟨109, 1429, 4, 2572, 2575, 54, 58, 37802, 1055484601, 1⟩,
    ⟨109, 1433, 4, 2575, 2578, 50, 54, 37854, 1051271095, 1⟩,
    ⟨109, 1439, 4, 2579, 2582, 46, 50, 37934, 1047074409, 1⟩,
    ⟨109, 1447, 4, 2584, 2587, 41, 45, 38039, 1041852103, 1⟩,
    ⟨109, 1451, 4, 2587, 2590, 37, 42, 38091, 1037693020, 1⟩,
    ⟨109, 1453, 4, 2589, 2592, 35, 39, 38118, 1035619707, 1⟩,
    ⟨109, 1459, 4, 2593, 2596, 31, 35, 38196, 1031485503, 1⟩,
    ⟨109, 1471, 4, 2601, 2604, 22, 26, 38353, 1022243783, 1⟩,
    ⟨109, 1481, 4, 2608, 2611, 15, 19, 38483, 1015113064, 1⟩,
    ⟨109, 1483, 4, 2609, 2612, 14, 18, 38509, 1014098458, 1⟩,
    ⟨109, 1487, 4, 2612, 2615, 10, 15, 38561, 1010050166, 1⟩,
    ⟨109, 1489, 4, 2613, 2616, 9, 13, 38587, 1009040621, 1⟩,
    ⟨109, 1493, 4, 2616, 2619, 6, 10, 38639, 1006018036, 1⟩,
    ⟨109, 1499, 4, 2620, 2623, 2, 6, 38716, 1002002001, 1⟩,
    ⟨109, 1511, 4, 2628, 2631, (-7), 0, 38871, 993024412, 0⟩,
    ⟨109, 1523, 4, 2636, 2639, (-16), 0, 39025, 984127291, 0⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_upper_rows109_block10_check :
    quarterUpperRows109Block10.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
