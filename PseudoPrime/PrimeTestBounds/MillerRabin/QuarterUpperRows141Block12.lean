/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Upper principal rows at cutoff 141, block 12 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterUpperRows141Block12 : List QuarterUpperWeightRow :=
  [⟨141, 1747, 4, 2515, 2518, 115, 119, 41797, 1121873436, 1⟩,
    ⟨141, 1753, 4, 2519, 2522, 111, 115, 41868, 1117394905, 1⟩,
    ⟨141, 1759, 4, 2522, 2525, 108, 112, 41940, 1114047744, 1⟩,
    ⟨141, 1777, 4, 2532, 2535, 97, 101, 42154, 1101860372, 1⟩,
    ⟨141, 1783, 4, 2536, 2539, 92, 97, 42225, 1096364819, 1⟩,
    ⟨141, 1787, 4, 2538, 2541, 90, 94, 42272, 1094174282, 1⟩,
    ⟨141, 1789, 4, 2539, 2542, 89, 93, 42296, 1093080654, 1⟩,
    ⟨141, 1801, 4, 2546, 2549, 82, 86, 42438, 1085455807, 1⟩,
    ⟨141, 1811, 4, 2551, 2554, 76, 80, 42555, 1078962573, 1⟩,
    ⟨141, 1823, 4, 2558, 2561, 69, 73, 42696, 1071436208, 1⟩,
    ⟨141, 1831, 4, 2562, 2565, 64, 69, 42790, 1066092397, 1⟩,
    ⟨141, 1847, 4, 2571, 2574, 55, 59, 42976, 1056540614, 1⟩,
    ⟨141, 1849, 4, 2572, 2575, 54, 58, 43000, 1055484601, 1⟩,
    ⟨141, 1861, 4, 2579, 2582, 46, 50, 43139, 1047074409, 1⟩,
    ⟨141, 1867, 4, 2582, 2585, 43, 47, 43208, 1043937894, 1⟩,
    ⟨141, 1871, 4, 2584, 2587, 41, 45, 43255, 1041852103, 1⟩,
    ⟨141, 1873, 4, 2585, 2588, 39, 44, 43278, 1039770482, 1⟩,
    ⟨141, 1877, 4, 2587, 2590, 37, 42, 43324, 1037693020, 1⟩,
    ⟨141, 1879, 4, 2588, 2591, 36, 40, 43347, 1036655845, 1⟩,
    ⟨141, 1889, 4, 2594, 2597, 30, 34, 43462, 1030454533, 1⟩,
    ⟨141, 1901, 4, 2600, 2603, 23, 27, 43600, 1023266538, 1⟩,
    ⟨141, 1907, 4, 2603, 2606, 20, 24, 43669, 1020201339, 1⟩,
    ⟨141, 1913, 4, 2606, 2609, 17, 21, 43737, 1017145321, 1⟩,
    ⟨141, 1931, 4, 2616, 2619, 6, 10, 43943, 1006018036, 1⟩,
    ⟨141, 1933, 4, 2617, 2620, 5, 9, 43965, 1005012520, 1⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_upper_rows141_block12_check :
    quarterUpperRows141Block12.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
